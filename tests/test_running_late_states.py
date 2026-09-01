"""Every state the Running-late control can be in must say what it is.

The control used to render nothing at all once the driver's day had started.
With the default 'first_action' rule a day starts the moment a driver completes
their first stop, so a driver could reach for this mid-morning and find blank
space — indistinguishable from the feature being broken. Same failure shape as
the ETA chips, which registered a tap and showed nothing.
"""
import os, sys, tempfile, importlib

TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "late.db")
os.environ["SECRET_KEY"] = "late"
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
cur.execute("""INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,
               created_at,driver_day_start_rule,driver_day_end_rule)
               VALUES (?,?,?,?,?,?,?,?)""",
            ("Late Co", "lateco", "pro", "active", 5, ts, "manual", "manual")); co = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at)"
            " VALUES (?,?,?,?,?,?)", ("l_drv", "x", "driver", "Dave Miller", co, ts)); drv = cur.lastrowid
conn.commit()

_co = conn.execute("SELECT * FROM companies WHERE id=?", (co,)).fetchone()
cos = {k: _co[k] for k in _co.keys()}


def card(uid=None, role="driver"):
    # url_for() needs an app context, and the helper now checks session role --
    # it must not hand a driver form to someone the POST endpoint would bounce.
    from flask import session as _sess
    with app.app.test_request_context("/driver/clock"):
        _sess["user_id"] = uid or drv
        _sess["company_id"] = co
        _sess["role"] = role
        return app._driver_late_card_html(conn, co, uid or drv, today, cos, "tok")


# ── 1. Not started: the control is offered ────────────────────────────────
h = card()
ok("late-open" in h, "before the day starts, the Running late button is offered")
ok("late-chip" in h and "30 min" in h, "the ETA chips are there")

# ── 2. Already reported: says so, with the ETA back ───────────────────────
conn.execute("""INSERT INTO late_checkins (company_id,driver_id,work_date,eta,reason,created_at)
                VALUES (?,?,?,?,?,?)""", (co, drv, today, "30 min", "traffic", ts))
conn.commit()
h = card()
ok("late-open" not in h, "the button is replaced once a check-in is active")
ok("running late" in h.lower(), "it confirms dispatch has been told")
ok("30 min" in h and "traffic" in h, "and shows back what was sent")
conn.execute("DELETE FROM late_checkins WHERE company_id=?", (co,)); conn.commit()

# ── 3. Day started: EXPLAINS, never blank ────────────────────────────────
conn.execute("""INSERT INTO driver_clock_entries (company_id, driver_id, date, clock_in_at, created_at)
                VALUES (?,?,?,?,?)""", (co, drv, today, today + " 06:42:00", ts))
conn.commit()
h = card()
ok(h.strip() != "", "a driver mid-day is never shown blank space where the control was")
ok("Running late is for before your day starts" in h,
   "it explains why the control isn't available")
ok("6:42 AM" in h, "and names the time their day started (got: %s)" % h[-320:].replace(chr(10), " "))
ok("Cab View" in h, "and points at the thing to use instead")
ok("late-open" not in h, "but does not offer a button that would be refused")

# ── 4. Day complete: quiet ────────────────────────────────────────────────
conn.execute("UPDATE driver_clock_entries SET clock_out_at=? WHERE driver_id=? AND date=?",
             (today + " 17:10:00", drv, today))
conn.commit()
ok(card().strip() == "", "once the day is closed the explainer stops taking up space")
conn.close()

# ── 5. A manager on the driver page is told, not handed a dead form ───────
# /driver/clock is only @login_required while /late/checkin is @driver_required,
# so a boss could fill in the form and be redirected with nothing written and
# nothing logged -- a 302 that reads exactly like success.
conn = app.get_db()
cur = conn.cursor()
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at)"
            " VALUES (?,?,?,?,?,?)", ("l_boss", "x", "boss", "Tim Brown", co, ts))
boss = cur.lastrowid
conn.commit()

h = card(uid=boss, role="boss")
ok("late-open" not in h, "a manager is never shown a Running late form the POST would bounce")
ok("driver check-in" in h, "and is told why (got: %s)" % h[-200:].replace(chr(10), " "))
conn.close()

print("\nALL RUNNING-LATE STATE TESTS PASSED")
