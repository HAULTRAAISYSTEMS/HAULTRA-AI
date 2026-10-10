"""Garbage routes: dispatch, driver fast flow, daily report (2026-10-10).

Covers: route_type migration, garbage dispatch validation, garbage/rolloff
separation, driver toter/HPU start->done+count, landfill arrive/depart+tons,
Previous Stop reopen on garbage, cab page render, daily report render.

Run:  ~/workspace/.haultra-venv/bin/python tests/test_garbage_routes.py
"""
import os
import sys
import tempfile
import importlib

TMP = tempfile.mkdtemp(prefix="haultra-garbage-")
os.environ["DATABASE_PATH"] = os.path.join(TMP, "g.db")
os.environ["SECRET_KEY"] = "g"
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
conn = app.get_db()
cur = conn.cursor()
ts = app.now_ts()
cur.execute("INSERT INTO companies (name, slug, subscription_plan, subscription_status, max_drivers, created_at)"
            " VALUES (?,?,?,?,?,?)", ("G Co", "gco", "pro", "active", 10, ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id, created_at)"
            " VALUES (?,?,?,?,?,?)", ("g_drv", "x", "driver", "G Driver", co, ts))
drv = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id, created_at)"
            " VALUES (?,?,?,?,?,?)", ("g_boss", "x", "boss", "G Boss", co, ts))
boss = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id, created_at)"
            " VALUES (?,?,?,?,?,?)", ("g_drv2", "x", "driver", "G Driver 2", co, ts))
drv2 = cur.lastrowid
conn.commit()

# Migration columns exist.
cols = {r["name"] for r in conn.execute("PRAGMA table_info(routes)").fetchall()}
ok("route_type" in cols, "routes.route_type column exists")
scols = {r["name"] for r in conn.execute("PRAGMA table_info(stops)").fetchall()}
for c in ("service_count", "started_at", "departed_at", "weight_tons", "not_before"):
    ok(c in scols, f"stops.{c} column exists")

app.app.config["TESTING"] = True
cl = app.app.test_client()


def login_as(uid, role):
    roles = [role]
    if role == "boss":
        roles = ["boss", "owner", "dispatcher", "customer_manager"]
    with cl.session_transaction() as s:
        s.update(user_id=uid, company_id=co, role=role, roles=roles, _csrf_token="tok")


def post(url, payload):
    return cl.post(url, json=payload, headers={"X-CSRF-Token": "tok"})


GSTOPS = [
    {"service_type": "toter", "address": "2545 Squadron Ct", "city": "VB",
     "notes": "", "not_before": ""},
    {"service_type": "hpu", "address": "800 Gas Light Ln", "city": "VB",
     "notes": "132 units", "not_before": "7am"},
    {"service_type": "landfill", "address": "GFL Transfer", "city": "Chesapeake",
     "notes": "", "not_before": ""},
]

# ── Boss dispatches a garbage route ────────────────────────────────────
login_as(boss, "boss")
r = post("/api/dispatch", {"route_type": "garbage", "driver_id": drv,
                            "route_date": "2026-10-10", "stops": GSTOPS})
j = r.get_json()
ok(r.status_code == 200 and j.get("success"), "garbage dispatch succeeds")
rid = j["route_id"]
rt = conn.execute("SELECT route_type FROM routes WHERE id=?", (rid,)).fetchone()["route_type"]
ok(rt == "garbage", "route tagged as garbage")
stops = [dict(x) for x in conn.execute(
    "SELECT id, action, city, not_before, notes FROM stops WHERE route_id=? ORDER BY stop_order",
    (rid,)).fetchall()]
ok([s["action"] for s in stops] == ["Toter", "Hand Pickup", "Landfill"],
   "stop actions mapped correctly")
ok(stops[1]["city"] == "VB" and stops[1]["not_before"] == "7am"
   and stops[1]["notes"] == "132 units",
   "city / not_before / notes stored")

# Bad service_type rejected.
r = post("/api/dispatch", {"route_type": "garbage", "driver_id": drv,
                            "route_date": "2026-10-10",
                            "stops": [{"service_type": "bogus", "address": "1 Main"}]})
ok(r.status_code == 400, "bad service_type rejected")

# Missing address rejected.
r = post("/api/dispatch", {"route_type": "garbage", "driver_id": drv,
                            "route_date": "2026-10-10",
                            "stops": [{"service_type": "toter", "address": ""}]})
ok(r.status_code == 400, "missing address rejected")

# Garbage and rolloff never share a route: driver already has an open garbage
# route today, so a rolloff dispatch creates a SEPARATE route.
r = post("/api/dispatch", {"driver_id": drv, "route_date": "2026-10-10",
                            "stops": [{"action": "PR", "address": "99 Roll St",
                                       "customer": "C", "container_size": "20yd"}]})
j2 = r.get_json()
ok(r.status_code == 200 and j2.get("success") and j2["route_id"] != rid,
   "rolloff dispatch creates a separate route (no mixing)")
ok(j2.get("appended") is False, "not appended to the garbage route")

# Second garbage dispatch appends to the existing garbage route.
r = post("/api/dispatch", {"route_type": "garbage", "driver_id": drv,
                            "route_date": "2026-10-10",
                            "stops": [{"service_type": "toter", "address": "1 Extra St",
                                       "city": "VB"}]})
j3 = r.get_json()
ok(j3.get("success") and j3["route_id"] == rid and j3.get("appended") is True,
   "second garbage dispatch appends to the garbage route")

# ── Driver fast flow ───────────────────────────────────────────────────
s1, s2, s3 = stops[0]["id"], stops[1]["id"], stops[2]["id"]
login_as(drv, "driver")

r = post(f"/api/stops/{s1}/garbage-start", {})
ok(r.status_code == 200 and r.get_json().get("success"), "toter start works")
sa = conn.execute("SELECT started_at, driver_status FROM stops WHERE id=?", (s1,)).fetchone()
ok(sa["started_at"] and sa["driver_status"] == "started", "started_at stamped")

r = post(f"/api/stops/{s1}/garbage-complete", {"count": 8, "note": "all behind building"})
ok(r.status_code == 200, "toter complete works")
sc = conn.execute(
    "SELECT status, service_count, notes, driver_status_before_complete FROM stops WHERE id=?",
    (s1,)).fetchone()
ok(sc["status"] == "completed" and sc["service_count"] == 8, "count recorded, stop completed")
ok("all behind building" in (sc["notes"] or ""), "note appended")
ok(sc["driver_status_before_complete"] == "started", "breadcrumb saved for Previous Stop")

# Previous Stop reopens right where the driver left off.
with cl.session_transaction() as s:
    s.update(user_id=drv, company_id=co, role="driver", roles=["driver"], _csrf_token="tok")
r = cl.post(f"/stop/{s1}/toggle", data={"intent": "reopen", "_csrf_token": "tok"})
sr = conn.execute("SELECT status, driver_status FROM stops WHERE id=?", (s1,)).fetchone()
ok(sr["status"] != "completed" and sr["driver_status"] == "started",
   "Previous Stop reopens garbage stop at 'started'")

# HPU flow.
r = post(f"/api/stops/{s2}/garbage-start", {})
ok(r.status_code == 200, "hpu start works")
r = post(f"/api/stops/{s2}/garbage-complete", {"count": 132})
sc2 = conn.execute("SELECT status, service_count FROM stops WHERE id=?", (s2,)).fetchone()
ok(sc2["status"] == "completed" and sc2["service_count"] == 132, "hpu count recorded")

# Landfill flow.
r = post(f"/api/stops/{s3}/landfill-arrive", {})
ok(r.status_code == 200, "landfill arrive works")
r = post(f"/api/stops/{s3}/landfill-depart", {"tons": 4.25})
sl = conn.execute(
    "SELECT status, weight_tons, arrived_at, departed_at FROM stops WHERE id=?",
    (s3,)).fetchone()
ok(sl["status"] == "completed" and abs(float(sl["weight_tons"]) - 4.25) < 0.001,
   "landfill tons recorded, stop completed")
ok(sl["arrived_at"] and sl["departed_at"], "landfill timestamps stamped")

# Wrong driver is blocked.
login_as(drv2, "driver")
r = post(f"/api/stops/{s1}/garbage-start", {})
ok(r.status_code == 404, "other driver's stop is not touchable")

# Wrong stop type blocked.
login_as(drv, "driver")
r = post(f"/api/stops/{s3}/garbage-start", {})
ok(r.status_code == 400, "landfill stop rejects toter endpoints")

# Held stop blocked.
conn.execute("UPDATE stops SET held_at=?, status='open' WHERE id=?", (ts, s1))
conn.commit()
r = post(f"/api/stops/{s1}/garbage-start", {})
ok(r.status_code == 400, "held stop cannot be started")
conn.execute("UPDATE stops SET held_at=NULL WHERE id=?", (s1,))
conn.commit()

# ── Cab page renders the garbage card ──────────────────────────────────
# Reopen s1 state: complete it again so the page shows the next current stop.
r = post(f"/api/stops/{s1}/garbage-complete", {"count": 8})
html = cl.get(f"/driver/route/{rid}").get_data(as_text=True)
ok("gbadge" in html and "g-start-btn" in html, "garbage cab page renders")
ok("TOTER" in html or "HPU" in html, "type badge shown")

# Not-before warning shows on the current stop card.
login_as(boss, "boss")
r = post("/api/dispatch", {"route_type": "garbage", "driver_id": drv2,
                            "route_date": "2026-10-10",
                            "stops": [{"service_type": "hpu", "address": "99 Early St",
                                       "city": "VB", "not_before": "8am"}]})
nb_rid = r.get_json()["route_id"]
login_as(drv2, "driver")
nb_html = cl.get(f"/driver/route/{nb_rid}").get_data(as_text=True)
ok("Not before 8am" in nb_html, "not-before warning shown")

# ── Daily report ───────────────────────────────────────────────────────
login_as(boss, "boss")
rep = cl.get(f"/route/{rid}/report").get_data(as_text=True)
ok("Daily Route Log" in rep, "report page renders")
ok("2545 Squadron Ct" in rep, "report lists stops")
ok("cans: 8" in rep and "bags: 132" in rep and "tons: 4.25" in rep,
   "report totals correct")

# ── Garbage dispatch page ──────────────────────────────────────────────
gp = cl.get("/garbage-dispatch").get_data(as_text=True)
ok("Garbage Dispatch" in gp and "gd-lines" in gp, "garbage dispatch page renders")

# ── Boss board visibility ────────────────────────────────────────────
# Nav has the Garbage link; the board shows the GARBAGE badge, Report link,
# and toter/HPU stop badges.
login_as(boss, "boss")
board = cl.get("/routes").get_data(as_text=True)
ok('href="/garbage-dispatch"' in board, "nav has Garbage Dispatch link")
ok("GARBAGE" in board, "board shows GARBAGE badge on the lane")
ok(f"/route/{nb_rid}/report" in board, "board links the daily report")
ok(">T<" in board or ">HPU<" in board, "board shows garbage stop badges")

conn.close()
print()
if FAILURES:
    print("FAILURES (%d):" % len(FAILURES))
    for f in FAILURES:
        print("  - " + f)
    sys.exit(1)
print("ALL CHECKS PASSED")
