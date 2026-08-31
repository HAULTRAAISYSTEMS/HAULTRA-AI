"""Cancel / un-cancel regression suite.

Covers the real scenario this feature was built for: the boss texts the driver
"cancel it" mid-shift, the driver clears the route from the cab, and neither
side loses the record that the work was ever dispatched.
"""
import os, sys, tempfile, importlib, json

TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "cancel.db")
os.environ["SECRET_KEY"] = "cancel"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")


def ok(c, m):
    print(("PASS" if c else "FAIL") + " - " + m)
    if not c:
        raise SystemExit("FAILED: " + m)


app.init_db()
conn = app.get_db(); cur = conn.cursor(); ts = app.now_ts(); today = app.today_str()

cur.execute("INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,created_at)"
            " VALUES (?,?,?,?,?,?)", ("CX", "cxco", "pro", "active", 10, ts)); co = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,company_id,created_at)"
            " VALUES (?,?,?,?,?)", ("c_boss", "x", "boss", co, ts)); boss = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at)"
            " VALUES (?,?,?,?,?,?)", ("c_drv", "x", "driver", "Dave", co, ts)); drv = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at)"
            " VALUES (?,?,?,?,?,?)", ("c_drv2", "x", "driver", "Other", co, ts)); drv2 = cur.lastrowid


def make_route(name, n_stops, assigned):
    cur.execute("INSERT INTO routes (company_id,route_date,route_name,created_by,assigned_to,status,started_at,created_at)"
                " VALUES (?,?,?,?,?,'in_progress',?,?)", (co, today, name, boss, assigned, ts, ts))
    rid = cur.lastrowid
    ids = []
    for i in range(1, n_stops + 1):
        cur.execute("""INSERT INTO stops (route_id,stop_order,customer_name,address,city,state,action,
                       container_size,status,driver_status,created_at)
                       VALUES (?,?,?,?,?,?,?,?,'open','pending',?)""",
                    (rid, i, "Cust%d" % i, "%d Main" % i, "Norfolk", "VA", "Pull", "30yd", ts))
        ids.append(cur.lastrowid)
    return rid, ids


rid, sids = make_route("R-cancel", 5, drv)
rid2, sids2 = make_route("R-other", 3, drv2)
conn.commit(); conn.close()

app.app.config["TESTING"] = True
cl = app.app.test_client()


def as_boss():
    with cl.session_transaction() as s:
        s.update(user_id=boss, company_id=co, role="boss",
                 roles=["owner", "dispatcher"], username="c_boss", _csrf_token="tok")


def as_driver(uid=None):
    with cl.session_transaction() as s:
        s.update(user_id=uid or drv, company_id=co, role="driver",
                 roles=["driver"], username="c_drv", _csrf_token="tok")


def stop_row(sid):
    c = app.get_db()
    r = c.execute("SELECT * FROM stops WHERE id=?", (sid,)).fetchone()
    c.close()
    return r


def route_row(r_id):
    c = app.get_db()
    r = c.execute("SELECT * FROM routes WHERE id=?", (r_id,)).fetchone()
    c.close()
    return r


# ── schema ────────────────────────────────────────────────────────────────
c = app.get_db()
cols = {r[1] for r in c.execute("PRAGMA table_info(stops)").fetchall()}
ok({"cancelled_at", "cancelled_by", "cancel_reason", "cancel_source",
    "cancel_client_uuid"} <= cols, "stops has cancel columns")
rcols = {r[1] for r in c.execute("PRAGMA table_info(routes)").fetchall()}
ok({"cancelled_at", "cancel_reason", "cancel_source"} <= rcols, "routes has cancel columns")
c.close()

# ── boss cancels a single stop ────────────────────────────────────────────
as_boss()
r = cl.post("/stop/%d/cancel" % sids[2],
            data={"_csrf_token": "tok", "reason": "CUSTOMER_CANCELLED", "client_uuid": "u1"})
ok(r.status_code in (200, 302), "boss cancel stop returns ok/redirect")
row = stop_row(sids[2])
ok(row["cancelled_at"] is not None, "stop 3 is cancelled")
ok(row["cancel_reason"] == "CUSTOMER_CANCELLED", "reason stored")
ok(row["cancel_source"] == "boss", "source recorded as boss")
ok(row["cancelled_by"] == boss, "cancelled_by recorded")
ok(row["status"] == "open", "cancel does not fake-complete the stop")

# ── cancelled stop drops out of progress + never becomes current ──────────
as_driver()
j = json.loads(cl.get("/driver/route/%d/status" % rid).data)
ok(j["total"] == 4, "denominator excludes cancelled stop (got %s)" % j["total"])
ok(j["cancelled"] == 1, "cancelled count surfaced")
c = app.get_db()
snap = app._route_realtime_snapshot(c, rid, drv)
c.close()
ok(snap["cancelled_ids"] == [sids[2]], "snapshot carries cancelled ids")
ok(snap["current_stop_id"] == sids[0], "current stop is still stop 1")

# complete stops 1 and 2, current must SKIP the cancelled 3 and land on 4
c = app.get_db()
c.execute("UPDATE stops SET status='completed', completed_at=? WHERE id IN (?,?)",
          (ts, sids[0], sids[1]))
c.commit()
snap = app._route_realtime_snapshot(c, rid, drv)
c.close()
ok(snap["current_stop_id"] == sids[3], "current stop skips the cancelled one")
ok(snap["completed"] == 2 and snap["total"] == 4, "progress reads 2/4 not 2/5")

# ── idempotent replay ─────────────────────────────────────────────────────
as_boss()
r = cl.post("/stop/%d/cancel" % sids[2],
            data={"_csrf_token": "tok", "reason": "CUSTOMER_CANCELLED", "client_uuid": "u1"},
            headers={"X-Requested-With": "XMLHttpRequest"})
j = json.loads(r.data)
ok(r.status_code == 200 and j.get("already") and j.get("duplicate"),
   "replayed cancel is a no-op, flagged duplicate")

# ── completed work cannot be cancelled ────────────────────────────────────
r = cl.post("/stop/%d/cancel" % sids[0],
            data={"_csrf_token": "tok", "reason": "CUSTOMER_CANCELLED"},
            headers={"X-Requested-With": "XMLHttpRequest"})
ok(r.status_code == 409, "cancelling a completed stop is refused (409)")

# ── a driver cannot touch another driver's route ──────────────────────────
as_driver()
r = cl.post("/stop/%d/cancel" % sids2[0],
            data={"_csrf_token": "tok", "reason": "BOSS_SAID_CANCEL"},
            headers={"X-Requested-With": "XMLHttpRequest"})
ok(r.status_code == 403, "driver cannot cancel another driver's stop")

# ── the real scenario: boss texts "cancel it", driver cancels the route ───
as_driver()
r = cl.post("/route/%d/cancel" % rid,
            data={"_csrf_token": "tok", "reason": "BOSS_SAID_CANCEL", "client_uuid": "rc1"},
            headers={"X-Requested-With": "XMLHttpRequest"})
j = json.loads(r.data)
ok(r.status_code == 200 and j["success"], "driver can cancel their own route")
ok(j["cancelled_stops"] == 2, "only the 2 remaining stops were cancelled (got %s)"
   % j["cancelled_stops"])
ok(route_row(rid)["cancelled_at"] is not None, "route marked cancelled")
ok(route_row(rid)["cancel_source"] == "driver", "route cancel source is driver")
ok(stop_row(sids[0])["cancelled_at"] is None, "completed stop 1 untouched")
ok(stop_row(sids[1])["cancelled_at"] is None, "completed stop 2 untouched")
ok(stop_row(sids[0])["status"] == "completed", "completed stop stays completed/billable")

c = app.get_db()
snap = app._route_realtime_snapshot(c, rid, drv)
c.close()
ok(snap["route_cancelled"] is True, "snapshot flags the route as cancelled")
ok(snap["current_stop_id"] is None, "no current stop left on a cancelled route")

# ── driver cannot un-cancel; boss can ─────────────────────────────────────
as_driver()
r = cl.post("/route/%d/uncancel" % rid, data={"_csrf_token": "tok"})
ok(r.status_code in (302, 403), "driver un-cancel is blocked")
ok(route_row(rid)["cancelled_at"] is not None, "route still cancelled after driver attempt")

as_boss()
r = cl.post("/route/%d/uncancel" % rid, data={"_csrf_token": "tok"})
ok(r.status_code in (200, 302), "boss un-cancel accepted")
ok(route_row(rid)["cancelled_at"] is None, "route reinstated")
ok(stop_row(sids[3])["cancelled_at"] is None, "route-cancelled stop 4 restored")
ok(stop_row(sids[4])["cancelled_at"] is None, "route-cancelled stop 5 restored")
# The individually-cancelled stop 3 must NOT come back with the route.
ok(stop_row(sids[2])["cancelled_at"] is not None,
   "separately-cancelled stop stays cancelled after route reinstate")

# ── un-cancel a single stop ───────────────────────────────────────────────
r = cl.post("/stop/%d/uncancel" % sids[2], data={"_csrf_token": "tok"})
ok(r.status_code in (200, 302), "boss un-cancel stop accepted")
ok(stop_row(sids[2])["cancelled_at"] is None, "stop 3 restored")
ok(stop_row(sids[2])["cancel_reason"] is None, "reason cleared on restore")

# ── unknown reason code degrades instead of failing ───────────────────────
r = cl.post("/stop/%d/cancel" % sids[4],
            data={"_csrf_token": "tok", "reason": "NONSENSE_CODE"},
            headers={"X-Requested-With": "XMLHttpRequest"})
ok(r.status_code == 200, "unknown reason code still cancels")
ok(stop_row(sids[4])["cancel_reason"] == "OTHER", "unknown reason stored as OTHER")

# ── pages still render with cancelled stops present ───────────────────────
as_boss()
ok(cl.get("/route/%d" % rid).status_code == 200, "boss route page renders")
as_driver()
ok(cl.get("/driver").status_code == 200, "driver dashboard renders")
ok(cl.get("/driver/route/%d" % rid).status_code == 200, "cab view renders")

# ── driver-facing UI surfaces ─────────────────────────────────────────────
as_driver()
html = cl.get("/driver/route/%d" % rid).data.decode()
ok("cab-cancel-btn" in html, "cab view exposes the cancel control")
ok("Can&#39;t run this" in html or "Can't run this" in html, "cancel control is labelled for the cab")
ok("cab-interrupt" in html, "cab view carries the realtime interrupt overlay")
ok("BOSS_SAID_CANCEL" in html, "'Boss said cancel it' is an offered reason")
ok("/route/%d/cancel" % rid in html, "whole-route cancel is reachable from the cab")

# poll payload is the channel Cab View actually reads
j = json.loads(cl.get("/driver/route/%d/status" % rid).data)
ok("cancelled_ids" in j and "route_cancelled" in j, "poll carries the cancel signal")
ok(j["current_stop_id"] is not None, "poll now returns current_stop_id")

# cancelled route → terminal screen, not the stop card
as_driver()
cl.post("/route/%d/cancel" % rid, data={"_csrf_token": "tok", "reason": "BOSS_SAID_CANCEL"})
html = cl.get("/driver/route/%d" % rid).data.decode()
ok("Route Cancelled" in html, "driver sees a cancelled-route screen")
ok("cab-cancel-btn" not in html, "no cancel control on an already-cancelled route")
j = json.loads(cl.get("/driver/route/%d/status" % rid).data)
ok(j["route_cancelled"] is True, "poll reports the route as cancelled")

# ── the [hidden] trap ─────────────────────────────────────────────────────
# This app has no global `[hidden] { display:none !important }` rule -- every
# component that toggles `hidden` ships its own `[hidden]` override. Any class
# that sets `display:` and is used on a `hidden` element is therefore permanently
# on screen. That shipped once already: the cancel interrupt covered the whole
# Cab View and GOT IT looked dead, because tapping it reloaded into the same
# stuck overlay. This scan fails the build the next time it happens.
import re

as_driver(drv2)
cab_html = cl.get("/driver/route/%d" % rid2).data.decode()

css = "\n".join(re.findall(r"<style[^>]*>(.*?)</style>", cab_html, re.S))
rules = re.findall(r"([^{}]+)\{([^{}]*)\}", css)
display_classes, hidden_guarded = set(), set()
for sel, decl in rules:
    sel = sel.strip()
    if "display:" in decl.replace(" ", ""):
        for cls in re.findall(r"\.([A-Za-z0-9_-]+)(?!\[)", sel.split("[")[0]):
            display_classes.add(cls)
    for cls in re.findall(r"\.([A-Za-z0-9_-]+)\[hidden\]", sel):
        hidden_guarded.add(cls)

offenders = []
for tag in re.findall(r"<[a-zA-Z][^>]*?>", cab_html, re.S):
    m = re.search(r'class="([^"]*)"', tag)
    if not m:
        continue
    # Strip quoted attribute VALUES before looking for the boolean attribute.
    # Otherwise an onclick like "...('nav-pref-overlay').hidden=false;" reads
    # as a hidden element and reports a false offender.
    bare = re.sub(r'=\s*"[^"]*"', "=x", tag)
    bare = re.sub(r"=\s*'[^']*'", "=x", bare)
    if not re.search(r"\shidden(?=[\s/>])", bare):
        continue
    for cls in m.group(1).split():
        if cls in display_classes and cls not in hidden_guarded:
            offenders.append(cls)

ok(not offenders,
   "every hidden element's display: class has a [hidden] override (offenders: %s)"
   % sorted(set(offenders)))
ok("cab-interrupt[hidden]" in css, "the cancel interrupt specifically is guarded")

print("\nALL CANCEL TESTS PASSED")
