"""Driver autonomy: vendor self-dispatch + upcoming-stop reorder (2026-10-10).

Vendor self-dispatch: the driver heads to a vendor on his own call — no boss
approval. The app inserts the vendor stop as current, holds the rest, and
notifies the boss (thread + alert). Vendor-complete releases holds and tells
the boss he's back in service.

Reorder: the driver may reshuffle upcoming stops only. Completed, current,
held, and cancelled stops stay locked. The boss is notified with what moved.

Run:  ~/workspace/.haultra-venv/bin/python tests/test_driver_autonomy.py
"""
import os
import sys
import tempfile
import importlib

TMP = tempfile.mkdtemp(prefix="haultra-autonomy-")
os.environ["DATABASE_PATH"] = os.path.join(TMP, "da.db")
os.environ["SECRET_KEY"] = "da"
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
            " VALUES (?,?,?,?,?,?)", ("DA Co", "daco", "pro", "active", 10, ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id, created_at)"
            " VALUES (?,?,?,?,?,?)", ("da_drv", "x", "driver", "DA Driver", co, ts))
drv = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id, created_at)"
            " VALUES (?,?,?,?,?,?)", ("da_boss", "x", "boss", "DA Boss", co, ts))
boss = cur.lastrowid
cur.execute("INSERT INTO vendors (company_id, name, phone, notes, address, is_active, created_at)"
            " VALUES (?,?,?,?,?,1,?)", (co, "Test Vendor", "555-0100", "", "99 Repair Rd", ts))
vendor_id = cur.lastrowid


def mkroute(name, nstops, status="in_progress"):
    cur.execute("INSERT INTO routes (company_id, route_date, route_name, created_by, assigned_to,"
                " status, created_at) VALUES (?,?,?,?,?,?,?)",
                (co, "2026-10-10", name, boss, drv, status, ts))
    rid = cur.lastrowid
    sids = []
    for i in range(1, nstops + 1):
        cur.execute("""INSERT INTO stops (route_id, stop_order, customer_name, address, city, state,
                       action, container_size, dump_location, notes, driver_status, status, created_at)
                       VALUES (?,?,?,?,'','VA','Pickup and Return','20yd','D','', 'pending','open', ?)""",
                    (rid, i, "cust%d" % i, "%d Main St" % i, ts))
        sids.append(cur.lastrowid)
    conn.commit()
    return rid, sids


def login_as(uid, role):
    with cl.session_transaction() as s:
        s.update(user_id=uid, company_id=co, role=role, roles=[role], _csrf_token="tok")


def post(url, payload):
    return cl.post(url, json=payload, headers={"X-CSRF-Token": "tok"})


def msgs(rid):
    return [dict(r) for r in conn.execute(
        "SELECT body, priority FROM messages WHERE route_id=? ORDER BY id", (rid,)).fetchall()]


def alerts():
    return [dict(r) for r in conn.execute(
        "SELECT kind, title FROM alerts WHERE company_id=? ORDER BY id", (co,)).fetchall()]


app.app.config["TESTING"] = True
cl = app.app.test_client()

# ── Vendor self-dispatch ────────────────────────────────────────────────
rid, sids = mkroute("VENDOR-RT", 3)
login_as(drv, "driver")
r = post("/api/driver/vendor-self-dispatch", {"vendor_id": vendor_id, "note": "tire"})
j = r.get_json()
ok(r.status_code == 200 and j.get("success"), "vendor self-dispatch succeeds")
vsid = j.get("vendor_stop_id")

vstop = dict(conn.execute("SELECT * FROM stops WHERE id=?", (vsid,)).fetchone())
ok(vstop["action"] == "Vendor" and vstop["customer_name"] == "Test Vendor",
   "vendor stop inserted with the picked vendor")
ok(vstop["address"] == "99 Repair Rd", "vendor stop carries the vendor address")

order = [dict(r) for r in conn.execute(
    "SELECT id, stop_order, held_at, status FROM stops WHERE route_id=? ORDER BY stop_order", (rid,)).fetchall()]
ok(order[0]["id"] == vsid and order[0]["held_at"] is None,
   "vendor stop is current (first, not held)")
ok(all(o["held_at"] for o in order[1:]),
   "remaining stops are held")
ok(any("headed to Test Vendor" in m["body"] for m in msgs(rid)),
   "boss notified on the route thread")
ok(any(a["kind"] == "VENDOR_SELF_DISPATCH" for a in alerts()),
   "boss alert raised for self-dispatch")

# No double vendor runs.
r = post("/api/driver/vendor-self-dispatch", {"vendor_name": "Other Shop"})
ok(r.status_code == 400, "second self-dispatch while one is open is rejected")

# Free-text vendor name on a fresh route (finish route 1 first — a driver has
# one active route, and driver_active_route_id picks it).
conn.execute("UPDATE routes SET status='completed' WHERE id=?", (rid,))
conn.commit()
rid2, _ = mkroute("VENDOR-RT2", 2)
login_as(drv, "driver")
r = post("/api/driver/vendor-self-dispatch", {"vendor_name": "Quick Fix Shop"})
j = r.get_json()
ok(r.status_code == 200 and j.get("success"), "free-text vendor name works")
v2 = dict(conn.execute("SELECT customer_name FROM stops WHERE id=?", (j["vendor_stop_id"],)).fetchone())
ok(v2["customer_name"] == "Quick Fix Shop", "free-text name stored on the vendor stop")

# Neither vendor_id nor name -> 400.
conn.execute("UPDATE routes SET status='completed' WHERE id=?", (rid2,))
conn.commit()
rid3, _ = mkroute("VENDOR-RT3", 2)
login_as(drv, "driver")
r = post("/api/driver/vendor-self-dispatch", {"note": "x"})
ok(r.status_code == 400, "missing vendor is rejected")

# Route not started -> 400.
conn.execute("UPDATE routes SET status='completed' WHERE id=?", (rid3,))
conn.commit()
rid4, _ = mkroute("VENDOR-RT4", 2, status="open")
login_as(drv, "driver")
r = post("/api/driver/vendor-self-dispatch", {"vendor_name": "Shop"})
ok(r.status_code == 400, "self-dispatch before route start is rejected")

# Vendor list endpoint.
r = cl.get("/api/driver/vendors")
j = r.get_json()
ok(r.status_code == 200 and any(v["name"] == "Test Vendor" for v in j["vendors"]),
   "driver can list company vendors")

# Vendor complete (repaired) releases holds + tells the boss.
login_as(drv, "driver")
r = post("/api/stops/%d/vendor-complete" % vsid, {"repaired": True})
ok(r.status_code == 200, "vendor complete succeeds")
held = conn.execute("SELECT COUNT(*) c FROM stops WHERE route_id=? AND held_at IS NOT NULL",
                    (rid,)).fetchone()["c"]
ok(held == 0, "holds released when back in service")
ok(any("back in service" in m["body"] for m in msgs(rid)),
   "boss notified the driver is back in service")

# ── Driver reorder ──────────────────────────────────────────────────────
rid5, s5 = mkroute("REORDER-RT", 5)
# stop 1 completed, stop 2 is current (open), 3/4/5 upcoming.
conn.execute("UPDATE stops SET status='completed', driver_status='completed' WHERE id=?", (s5[0],))
conn.commit()
login_as(drv, "driver")
r = post("/api/driver/route/%d/reorder" % rid5, {"stop_ids": [s5[4], s5[3], s5[2]]})
j = r.get_json()
ok(r.status_code == 200 and j.get("success"), "reorder of upcoming stops succeeds")
order = [r["id"] for r in conn.execute(
    "SELECT id FROM stops WHERE route_id=? ORDER BY stop_order", (rid5,)).fetchall()]
ok(order == [s5[0], s5[1], s5[4], s5[3], s5[2]],
   "completed + current stay locked, upcoming reversed")
ok(any("reordered" in m["body"] for m in msgs(rid5)),
   "boss notified of the reorder on the thread")
ok(any(a["kind"] == "DRIVER_REORDER" for a in alerts()),
   "boss alert raised for reorder")

# Completed stop in the list -> 400.
r = post("/api/driver/route/%d/reorder" % rid5,
         {"stop_ids": [s5[0], s5[4], s5[2]]})
ok(r.status_code == 400, "completed stop cannot be reordered")

# Current stop in the list -> 400.
r = post("/api/driver/route/%d/reorder" % rid5,
            {"stop_ids": [s5[1], s5[4], s5[2]]})
ok(r.status_code == 400, "current stop cannot be reordered")

# Missing a stop -> 400.
r = post("/api/driver/route/%d/reorder" % rid5, {"stop_ids": [s5[4], s5[3]]})
ok(r.status_code == 400, "incomplete stop list rejected")

# Wrong driver -> 404.
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id, created_at)"
            " VALUES (?,?,?,?,?,?)", ("da_drv2", "x", "driver", "Other", co, ts))
drv2 = cur.lastrowid
conn.commit()
login_as(drv2, "driver")
r = post("/api/driver/route/%d/reorder" % rid5, {"stop_ids": [s5[4], s5[3], s5[2]]})
ok(r.status_code == 404, "another driver's route is not reorderable")

# Held stops stay locked in place.
rid6, s6 = mkroute("REORDER-HELD", 4)
conn.execute("UPDATE stops SET status='completed' WHERE id=?", (s6[0],))
conn.execute("UPDATE stops SET held_at=? WHERE id IN (?,?)", (ts, s6[2], s6[3]))
conn.commit()
login_as(drv, "driver")
# unlocked = only s6[1] (current). Reordering a single stop is a no-op success.
r = post("/api/driver/route/%d/reorder" % rid6, {"stop_ids": [s6[1]]})
ok(r.status_code == 400, "current stop cannot be reordered even when held stops exist")
r = post("/api/driver/route/%d/reorder" % rid6, {"stop_ids": [s6[2], s6[1]]})
ok(r.status_code == 400, "held stop cannot be reordered")

# Unchanged order is a no-op success (no boss spam).
rid7, s7 = mkroute("REORDER-NOOP", 4)
conn.execute("UPDATE stops SET status='completed' WHERE id=?", (s7[0],))
conn.commit()
r = post("/api/driver/route/%d/reorder" % rid7, {"stop_ids": [s7[2], s7[3]]})
j = r.get_json()
ok(r.status_code == 200 and j.get("success") and j.get("unchanged"),
   "unchanged order returns no-op success")

conn.close()
print()
if FAILURES:
    print("FAILURES (%d):" % len(FAILURES))
    for f in FAILURES:
        print("  - " + f)
    sys.exit(1)
print("ALL CHECKS PASSED")
