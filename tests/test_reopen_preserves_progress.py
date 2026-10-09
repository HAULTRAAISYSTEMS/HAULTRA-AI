"""Reopen ("Previous Stop") preserves workflow progress.

2026-10-09: tapping "Previous Stop" reset driver_status to "pending", forcing
the driver to redo the entire stop including the dump ticket. Now the
pre-completion driver_status is saved on every completion path and restored
on reopen, so the driver lands back where he was.

Run:  ~/workspace/.haultra-venv/bin/python tests/test_reopen_preserves_progress.py
"""
import os
import sys
import tempfile
import importlib

TMP = tempfile.mkdtemp(prefix="haultra-reopen-")
os.environ["DATABASE_PATH"] = os.path.join(TMP, "ro.db")
os.environ["SECRET_KEY"] = "ro"
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
            " VALUES (?,?,?,?,?,?)", ("RO Co", "roco", "pro", "active", 10, ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id, created_at)"
            " VALUES (?,?,?,?,?,?)", ("ro_drv", "x", "driver", "RO Driver", co, ts))
drv = cur.lastrowid
cur.execute("INSERT INTO routes (company_id, route_date, route_name, created_by, assigned_to, status, created_at)"
            " VALUES (?,?,?,?,?,'in_progress',?)", (co, "2026-10-09", "RO", drv, drv, ts))
rid = cur.lastrowid


def mkstop(order, driver_status, note=""):
    cur.execute("""INSERT INTO stops (route_id, stop_order, customer_name, address, city, state, action,
                   container_size, dump_location, notes, driver_status, arrived_at, status, created_at)
                   VALUES (?,?,?,?, '', 'VA','Pickup and Return', '20yd', 'D', ?, ?, ?, 'open', ?)""",
                (rid, order, "cust%d" % order, "%d Test St" % order, note,
                 driver_status, ts if driver_status != "pending" else None, ts))
    conn.commit()
    return cur.lastrowid


def get(sid):
    return dict(conn.execute("SELECT status, driver_status, driver_status_before_complete"
                             " FROM stops WHERE id=?", (sid,)).fetchone())


app.app.config["TESTING"] = True
cl = app.app.test_client()


def login():
    with cl.session_transaction() as s:
        s.update(user_id=drv, company_id=co, role="driver", roles=["driver"],
                 _csrf_token="tok")


# ── 1. Complete via the main button, then reopen ─────────────────────────
s1 = mkstop(1, "need_box_in", note="use to swap")
login()
r = cl.post("/stop/%d/toggle" % s1, data={"intent": "complete", "_csrf_token": "tok"})
ok(r.status_code in (302, 303), "complete POST redirects")
g = get(s1)
ok(g["status"] == "completed" and g["driver_status"] == "completed", "stop completes")
ok(g["driver_status_before_complete"] == "need_box_in",
   "completion saves the pre-completion workflow state")

r = cl.post("/stop/%d/toggle" % s1, data={"intent": "reopen", "_csrf_token": "tok"})
g = get(s1)
ok(g["status"] == "open", "reopen flips status back to open")
ok(g["driver_status"] == "need_box_in",
   "reopen restores need_box_in (no ticket redo)")

# ── 2. Handoff auto-complete path also saves ────────────────────────────
s2 = mkstop(2, "need_box_in", note="use to swap")
s3 = mkstop(3, "pending")
conn.execute("UPDATE stops SET notes=? WHERE id=?", ("use to swap", s2))
conn.commit()
app._apply_route_chains(conn, rid)
conn.commit()
login()
r = cl.post("/stop/%d/driver-action" % s2,
            data={"action": "box_in", "_csrf_token": "tok"})
g = get(s2)
ok(g["status"] == "completed", "handoff tap completes the stop")
ok(g["driver_status_before_complete"] == "need_box_in",
   "handoff auto-complete saves the pre-completion state")
r = cl.post("/stop/%d/toggle" % s2, data={"intent": "reopen", "_csrf_token": "tok"})
g = get(s2)
ok(g["driver_status"] == "need_box_in",
   "reopen after handoff tap restores need_box_in")

# ── 3. Legacy stops (completed before this column existed) fall back ─────
s4 = mkstop(4, "arrived")
login()
cl.post("/stop/%d/toggle" % s4, data={"intent": "complete", "_csrf_token": "tok"})
conn.execute("UPDATE stops SET driver_status_before_complete=NULL WHERE id=?", (s4,))
conn.commit()
cl.post("/stop/%d/toggle" % s4, data={"intent": "reopen", "_csrf_token": "tok"})
g = get(s4)
ok(g["driver_status"] == "pending",
   "reopen with no saved state falls back to pending (old behavior)")

# ── 4. Idempotent double-complete does not clobber the breadcrumb ────────
s5 = mkstop(5, "going_to_dump")
login()
cl.post("/stop/%d/toggle" % s5, data={"intent": "complete", "_csrf_token": "tok"})
g1 = get(s5)
cl.post("/stop/%d/toggle" % s5, data={"intent": "complete", "_csrf_token": "tok",
                                      "X-Requested-With": "XMLHttpRequest"},
        headers={"X-Requested-With": "XMLHttpRequest"})
g2 = get(s5)
ok(g1["driver_status_before_complete"] == "going_to_dump"
   and g2["driver_status_before_complete"] == "going_to_dump",
   "double-complete keeps the original pre-completion state")
ok(g2["status"] == "completed", "double-complete stays completed (idempotent)")

conn.close()
print()
if FAILURES:
    print("FAILURES (%d):" % len(FAILURES))
    for f in FAILURES:
        print("  - " + f)
    sys.exit(1)
print("ALL CHECKS PASSED")
