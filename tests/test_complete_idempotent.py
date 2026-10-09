"""Driver "Complete Stop" must be IDEMPOTENT — a second tap on an already-
completed stop (double-tap on a bumpy road, or a retry after the first tap
succeeded but its response was lost) must NOT silently reopen the stop.
Only an explicit reopen intent ("Previous Stop", "Fix Last Stop", boss
"Reopen Stop") flips completed -> open.

Run:  ~/workspace/.haultra-venv/bin/python tests/test_complete_idempotent.py
"""
import os
import sys
import tempfile

TMPDIR = tempfile.mkdtemp(prefix="haultra-idem-")
os.environ["DATABASE_PATH"] = os.path.join(TMPDIR, "idempotent.db")
os.environ["SECRET_KEY"] = "testsecret123"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMPDIR, "uploads")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import app  # noqa: E402

FAILURES = []


def ok(cond, label):
    print(("PASS" if cond else "FAIL") + " - " + label, flush=True)
    if not cond:
        FAILURES.append(label)


def row(sid):
    c = app.get_db()
    try:
        return c.execute("SELECT * FROM stops WHERE id=?", (sid,)).fetchone()
    finally:
        c.close()


# ── Seed ───────────────────────────────────────────────────────────────
app.init_db()
conn = app.get_db()
cur = conn.cursor()
ts = app.now_ts()
today = app.today_str()
cur.execute(
    "INSERT INTO companies (name, slug, subscription_plan, subscription_status,"
    " max_drivers, created_at) VALUES (?,?,?,?,?,?)",
    ("Idem Co", "idemco", "pro", "active", 10, ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, company_id, created_at)"
            " VALUES (?,?,?,?,?)", ("i_boss", "x", "boss", co, ts))
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id, created_at)"
            " VALUES (?,?,?,?,?,?)", ("i_drv", "x", "driver", "Ida", co, ts))
drv = cur.lastrowid
cur.execute("INSERT INTO routes (company_id, route_date, route_name, created_by, assigned_to,"
            " status, started_at, created_at) VALUES (?,?,?,?,?,'in_progress',?,?)",
            (co, today, "IDEM", drv, drv, ts, ts))
rid = cur.lastrowid


def mkstop(order, name):
    cur.execute(
        """INSERT INTO stops (route_id, stop_order, customer_name, address, city, state,
                              action, container_size, status, driver_status, created_at)
           VALUES (?,?,?,?,'Virginia Beach','VA','Pickup and Return','30yd',
                   'open','need_box_in',?)""",
        (rid, order, name, "%d Test Way" % order, ts))
    return cur.lastrowid


s1 = mkstop(1, "First Stop")
s2 = mkstop(2, "Second Stop")
conn.commit()
conn.close()

app.app.config["TESTING"] = True
cl = app.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=drv, company_id=co, role="driver", _csrf_token="tok")


def post_toggle(sid, intent=None, xhr=False, replay=False, expected_status=None):
    data = {"_csrf_token": "tok"}
    if intent:
        data["intent"] = intent
    if expected_status:
        data["expected_status"] = expected_status
    hdrs = {}
    if xhr:
        hdrs["X-Requested-With"] = "XMLHttpRequest"
    if replay:
        hdrs["X-Sync-Replay"] = "1"
    return cl.post("/stop/%d/toggle" % sid, data=data, headers=hdrs)


# ── 1. Complete an open stop (form post, intent=complete) ──────────────
r = post_toggle(s1, intent="complete")
ok(r.status_code == 302, "complete intent on open stop redirects (302)")
ok(row(s1)["status"] == "completed", "open stop -> completed")

# ── 2. Tap Complete AGAIN (the double-tap / retry) — must NOT reopen ───
r = post_toggle(s1, intent="complete")
ok(r.status_code == 302, "second complete tap redirects, no error")
ok(row(s1)["status"] == "completed", "second complete tap does NOT reopen the stop")
ok(row(s1)["driver_status"] == "completed", "driver_status stays completed")

# ── 3. Same via the AJAX path the driver app actually uses ────────────
r = post_toggle(s1, intent="complete", xhr=True)
ok(r.status_code == 200, "XHR re-complete returns 200 (not a toggle, not an error)")
j = r.get_json()
ok(j.get("success") and j.get("new_status") == "completed",
   "XHR JSON reports success + new_status=completed (idempotent)")
ok(row(s1)["status"] == "completed", "XHR re-complete leaves stop completed")

# ── 4. Legacy callers with no intent field also must not reopen ────────
r = post_toggle(s1, xhr=True)
ok(r.get_json().get("new_status") == "completed" and row(s1)["status"] == "completed",
   "missing intent on completed stop is a safe no-op")

# ── 5. Explicit reopen intent still reopens (Previous Stop flow) ───────
# 2026-10-09: reopen now RESTORES the pre-completion workflow state
# (need_box_in here) instead of resetting to pending — the driver lands back
# where he was, no ticket redo.
r = post_toggle(s1, intent="reopen")
ok(r.status_code == 302, "reopen intent redirects")
ok(row(s1)["status"] == "open" and row(s1)["driver_status"] == "need_box_in",
   "reopen intent flips completed -> open and restores pre-completion state")

# ── 6. And completing the reopened stop works again ────────────────────
r = post_toggle(s1, intent="complete")
ok(row(s1)["status"] == "completed", "reopened stop can be completed again")

# ── 7. Sync replay of a completion for an already-completed stop ───────
# (first tap went through; retry arrives as a replay) -> 200, not 409.
r = post_toggle(s1, intent="complete", replay=True, expected_status="open")
ok(r.status_code == 200, "completion replay on completed stop -> 200, not 409")
ok(r.get_json().get("success") and r.get_json().get("new_status") == "completed",
   "replay JSON reports idempotent success")
ok(row(s1)["status"] == "completed", "replay leaves stop completed")

# ── 8. Reopen replay conflict behavior is unchanged ────────────────────
r = post_toggle(s1, intent="reopen", replay=True, expected_status="open")
ok(r.status_code == 409, "reopen replay with stale expected_status still 409s")

# ── 9. The card no longer offers a completed stop as current ───────────
h = cl.get("/driver/route/%d" % rid).get_data(as_text=True)
ok("STOP 2 OF 2" in h, "after s1 completes, current card is stop 2 (s1 stays done)")
r = post_toggle(s1, intent="complete", xhr=True)  # stray retry after advancing
h = cl.get("/driver/route/%d" % rid).get_data(as_text=True)
ok("STOP 2 OF 2" in h and row(s1)["status"] == "completed",
   "stray retry after advancing changes nothing")

# ── 10. Forms carry the intent fields ──────────────────────────────────
c = app.get_db()
c.execute("UPDATE stops SET driver_status='box_in', arrived_at=? WHERE id=?", (ts, s2))
c.commit()
c.close()
h = cl.get("/driver/route/%d" % rid).get_data(as_text=True)
ok('name="intent" value="complete"' in h, "Complete Stop form posts intent=complete")
ok('name="intent" value="reopen"' in h, "Previous Stop form posts intent=reopen")

print("ALL PASS" if not FAILURES else "FAILURES: %d" % len(FAILURES), flush=True)
sys.exit(1 if FAILURES else 0)
