"""A vendor errand must never park the stop the driver is standing at.

2026-11-03. Two faults in the vendor-stop path, found while answering "how do
I fit Gregory's into a running route".

1. _insert_vendor_stop carefully respects a locked prefix -- completed stops
   PLUS the driver's single in-progress stop -- and then
   _reprioritize_for_vendor rebuilt the order from completed stops only,
   ignoring that rule. Reproduced on a three-stop route with the middle stop
   at driver_status='arrived':

       1. First      Pull    completed   HELD=no
       2. Gregory's  Vendor  open        HELD=no     <- jumped the queue
       3. PRO-MIT    Pull    arrived     HELD=YES    <- the stop he is at
       4. Later      Pull    pending     HELD=YES

   The driver is locked out of the stop he is physically working, with a can
   on the truck.

2. The boss's /api/dispatch/vendor-visit takes three modes -- first / now /
   line -- and the driver's self-dispatch was hardcoded to "drop everything".
   The person on the road, who can see whether he can fit it in, had the
   least control of anyone.

Run:  python3 tests/test_vendor_dispatch_modes.py
"""
import os
import sys
import tempfile
import importlib

TMP = tempfile.mkdtemp(prefix="haultra-vmodes-")
os.environ["DATABASE_PATH"] = os.path.join(TMP, "v.db")
os.environ["SECRET_KEY"] = "v"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")

FAILURES = []


def ok(cond, label):
    print(("PASS" if cond else "FAIL") + " - " + label, flush=True)
    if not cond:
        FAILURES.append(label)


app.init_db()
c0 = app.get_db()
cur = c0.cursor()
ts = app.now_ts()
cur.execute("INSERT INTO companies (name, slug, subscription_plan, subscription_status,"
            " max_drivers, created_at) VALUES (?,?,?,?,?,?)",
            ("V Co", "vco", "pro", "active", 10, ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id,"
            " is_active, created_at) VALUES (?,?,?,?,?,1,?)",
            ("v_drv", "x", "driver", "V Driver", co, ts))
drv = cur.lastrowid
cur.execute("INSERT INTO vendors (company_id, name, address, is_active, created_at)"
            " VALUES (?,?,?,1,?)", (co, "Gregory's", "9 Shop Rd", ts))
ven = cur.lastrowid
c0.commit()
c0.close()

# The endpoint resolves "the driver's route" as TODAY's route, and there can
# only be one per driver per day, so each fixture gets a driver of its own.
_DAY = [0]


def route_with_current_stop():
    """A route mid-shift: one stop done, one the driver is AT, one to come.
    Returns (route_id, stop_ids, driver_id)."""
    _DAY[0] += 1
    c = app.get_db()
    cu = c.cursor()
    cu.execute("INSERT INTO users (username, password_hash, role, full_name,"
               " company_id, is_active, created_at) VALUES (?,?,?,?,?,1,?)",
               ("v_drv_%d" % _DAY[0], "x", "driver", "V Drv %d" % _DAY[0], co, ts))
    d = cu.lastrowid
    cu.execute("INSERT INTO routes (company_id, route_date, route_name, created_by,"
               " assigned_to, status, created_at) VALUES (?,?,?,?,?,'in_progress',?)",
               (co, app.today_str(), "R", d, d, ts))
    rid = cu.lastrowid
    ids = {}
    for i, (nm, st, ds) in enumerate(
            [("First", "completed", "completed"),
             ("PRO-MIT", "open", "arrived"),
             ("Later", "open", "pending")], start=1):
        cu.execute("""INSERT INTO stops (route_id, stop_order, customer_name, address,
                      city, state, action, container_size, status, driver_status, created_at)
                      VALUES (?,?,?,?,'Norfolk','VA','Pull','20yd',?,?,?)""",
                   (rid, i, nm, "%d St" % i, st, ds, ts))
        ids[nm] = cu.lastrowid
    c.commit()
    c.close()
    return rid, ids, d


def layout(rid):
    c = app.get_db()
    rows = [dict(r) for r in c.execute(
        "SELECT stop_order, customer_name, action, status, driver_status, held_at"
        " FROM stops WHERE route_id=? ORDER BY stop_order", (rid,)).fetchall()]
    c.close()
    return rows


def show(rows):
    return " | ".join("%d.%s%s" % (r["stop_order"], r["customer_name"],
                                   "(HELD)" if r["held_at"] else "") for r in rows)


app.app.config["TESTING"] = True
cl = app.app.test_client()


def as_driver(d=None):
    with cl.session_transaction() as s:
        s.update(user_id=(d if d is not None else drv), company_id=co,
                 role="driver", roles=["driver"], _csrf_token="tok")


HJ = {"X-CSRF-Token": "tok"}

# ── 1. THE BUG: go now must not park the stop he is standing at ────
print("\n-- go now, mid-stop --")
rid, ids, d1 = route_with_current_stop()
as_driver(d1)
r = cl.post("/api/driver/vendor-self-dispatch",
            json={"vendor_id": ven, "mode": "now", "note": "cable"}, headers=HJ)
ok(r.status_code == 200, "self-dispatch accepted (got %d)" % r.status_code)
rows = layout(rid)
_cur = next((x for x in rows if x["customer_name"] == "PRO-MIT"), None)
ok(_cur is not None and not _cur["held_at"],
   "the stop the driver is AT is NOT held — %s" % show(rows))
_later = next((x for x in rows if x["customer_name"] == "Later"), None)
ok(_later is not None and _later["held_at"],
   "but the stops after it ARE held, which is what go-now means")
_ven = next((x for x in rows if x["action"] == "Vendor"), None)
ok(_ven is not None and not _ven["held_at"], "the vendor stop itself is not held")
ok(_cur and _ven and _cur["stop_order"] < _ven["stop_order"],
   "and the vendor comes AFTER the stop he is working, not before it — %s" % show(rows))

# ── 2. Go now with nothing in progress ─────────────────────────────
# Then the vendor legitimately becomes the current stop: there is no stop
# being worked for it to jump.
print("\n-- go now with no stop in progress --")
c = app.get_db()
cu = c.cursor()
cu.execute("INSERT INTO routes (company_id, route_date, route_name, created_by,"
           " assigned_to, status, created_at) VALUES (?,?,?,?,?,'in_progress',?)",
           (co, app.today_str(), "R2", drv, drv, ts))
rid2 = cu.lastrowid
for i, nm in enumerate(["A", "B"], start=1):
    cu.execute("""INSERT INTO stops (route_id, stop_order, customer_name, address, city,
                  state, action, container_size, status, driver_status, created_at)
                  VALUES (?,?,?,?,'Norfolk','VA','Pull','20yd','open','pending',?)""",
               (rid2, i, nm, "%d Rd" % i, ts))
c.commit()
c.close()
as_driver()
r = cl.post("/api/driver/vendor-self-dispatch",
            json={"vendor_id": ven, "mode": "now"}, headers=HJ)
ok(r.status_code == 200, "accepted (got %d)" % r.status_code)
rows2 = layout(rid2)
ok(rows2 and rows2[0]["action"] == "Vendor" and not rows2[0]["held_at"],
   "the vendor is first and unheld — %s" % show(rows2))
ok(all(x["held_at"] for x in rows2 if x["action"] != "Vendor"),
   "and both customer stops are held")

# ── 3. After this stop — nothing held ──────────────────────────────
print("\n-- after this stop --")
rid3, _, d3 = route_with_current_stop()
as_driver(d3)
r = cl.post("/api/driver/vendor-self-dispatch",
            json={"vendor_id": ven, "mode": "after"}, headers=HJ)
ok(r.status_code == 200, "accepted (got %d)" % r.status_code)
rows3 = layout(rid3)
ok(not any(x["held_at"] for x in rows3),
   "NOTHING is held — the route keeps running — %s" % show(rows3))
_cur3 = next(x for x in rows3 if x["customer_name"] == "PRO-MIT")
_ven3 = next(x for x in rows3 if x["action"] == "Vendor")
_lat3 = next(x for x in rows3 if x["customer_name"] == "Later")
ok(_cur3["stop_order"] < _ven3["stop_order"] < _lat3["stop_order"],
   "the vendor sits between the current stop and the next one — %s" % show(rows3))

# ── 4. Add to my route — at the end, nothing held ──────────────────
print("\n-- add to my route --")
rid4, _, d4 = route_with_current_stop()
as_driver(d4)
r = cl.post("/api/driver/vendor-self-dispatch",
            json={"vendor_id": ven, "mode": "line"}, headers=HJ)
ok(r.status_code == 200, "accepted (got %d)" % r.status_code)
rows4 = layout(rid4)
ok(not any(x["held_at"] for x in rows4), "nothing is held — %s" % show(rows4))
ok(rows4[-1]["action"] == "Vendor",
   "the vendor goes last, behind the work — %s" % show(rows4))

# ── 5. An old caller keeps the behaviour it was written against ────
# No mode still means "go now". That was deliberate when this path was built
# for breakdowns (test_driver_autonomy asserts it), and the fix above removed
# what made it costly: go-now no longer takes the stop he is standing at. The
# CAB leads with "after this stop" instead, so the driver gets the gentle
# option without changing what an existing caller does.
print("\n-- no mode: unchanged, but no longer destructive --")
rid5, _, d5 = route_with_current_stop()
as_driver(d5)
r = cl.post("/api/driver/vendor-self-dispatch", json={"vendor_id": ven}, headers=HJ)
ok(r.status_code == 200, "accepted with no mode given (got %d)" % r.status_code)
rows5 = layout(rid5)
_l5 = next(x for x in rows5 if x["customer_name"] == "Later")
ok(_l5["held_at"], "no mode still holds the stops ahead — %s" % show(rows5))
_c5 = next(x for x in rows5 if x["customer_name"] == "PRO-MIT")
ok(not _c5["held_at"],
   "but NOT the stop he is standing at — the part that was broken — %s" % show(rows5))

rid6, _, d6 = route_with_current_stop()
as_driver(d6)
cl.post("/api/driver/vendor-self-dispatch",
        json={"vendor_id": ven, "mode": "banana"}, headers=HJ)
_rows6 = layout(rid6)
ok(next(x for x in _rows6 if x["customer_name"] == "Later")["held_at"],
   "an unrecognised mode falls back the same way")
ok(not next(x for x in _rows6 if x["customer_name"] == "PRO-MIT")["held_at"],
   "and still spares the in-progress stop")

# The cab's own default is the gentle one.
ok('<option value="after" selected>' in app._CAB_VENDOR_MODE_HTML
   if hasattr(app, "_CAB_VENDOR_MODE_HTML") else True,
   "(cab default checked in the cab section below)")

# ── 6. The boss's path keeps its own behaviour ─────────────────────
print("\n-- the boss's modes still work --")
ok(hasattr(app, "_reprioritize_for_vendor"), "the hold helper is still there")
rid7, _, d7 = route_with_current_stop()
c = app.get_db()
cu = c.cursor()
cu.execute("INSERT INTO users (username, password_hash, role, full_name, company_id,"
           " is_active, created_at) VALUES (?,?,?,?,?,1,?)",
           ("v_boss_%d" % _DAY[0], "x", "boss", "V Boss", co, ts))
vboss = cu.lastrowid
c.commit()
c.close()
with cl.session_transaction() as s:
    s.update(user_id=vboss, company_id=co, role="boss",
             roles=["boss", "owner", "dispatcher"], _csrf_token="tok")
r = cl.post("/api/dispatch/vendor-visit",
            json={"driver_id": d7, "vendor_id": ven, "mode": "now"}, headers=HJ)
ok(r.status_code == 200, "boss go-now accepted (got %d)" % r.status_code)
rows7 = layout(rid7)
_cur7 = next((x for x in rows7 if x["customer_name"] == "PRO-MIT"), None)
ok(_cur7 is not None and not _cur7["held_at"],
   "and the boss's go-now ALSO leaves the in-progress stop alone — %s" % show(rows7))

# ── 7. The cab offers the choice ───────────────────────────────────
print("\n-- the cab --")
as_driver(d1)
html = cl.get("/driver/route/%d" % rid).get_data(as_text=True)
ok("vg-mode" in html, "the vendor modal has a mode control")
for label in ("After this stop", "Go now", "Add to my route"):
    ok(label in html, "it offers %r" % label)
_mode_block = html.split('id="vg-mode"', 1)[1][:400] if 'id="vg-mode"' in html else ""
ok('value="after" selected' in _mode_block,
   "and the cab pre-selects 'After this stop', the gentle one")

print("\n%d failure(s)" % len(FAILURES))
for f in FAILURES:
    print("  FAILED: " + f)
sys.exit(1 if FAILURES else 0)
