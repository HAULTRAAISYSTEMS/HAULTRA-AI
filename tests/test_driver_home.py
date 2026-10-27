"""Driver home (dashboard) + Clock page redesign, 2026-10-27.

Covers the bugs fixed along the way:
  * the hours <script> on the driver dashboard was never closed, so the
    reorder / add-stop modals and their JS were swallowed as script text —
    Rearrange, Add Stop and stop-cancel did nothing
  * "Full route history" linked back to the same page
  * the Clocked In pill used a black-circle emoji
  * a customer name with an apostrophe broke the cancel button's JS

Run:  python tests/test_driver_home.py
"""
import os
import re
import sys
import tempfile

TMPDIR = tempfile.mkdtemp(prefix="haultra-drvhome-")
os.environ["DATABASE_PATH"] = os.path.join(TMPDIR, "d.db")
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


app.init_db()
conn = app.get_db(); cur = conn.cursor(); ts = app.now_ts(); today = app.today_str()
cur.execute("INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,created_at)"
            " VALUES ('HomeCo','homeco','pro','active',5,?)", (ts,)); co = cur.lastrowid
cur.execute("UPDATE companies SET driver_day_start_rule='manual', driver_day_end_rule='manual' WHERE id=?", (co,))
cur.execute("INSERT INTO users (username,password_hash,role,company_id,created_at) VALUES ('h_boss','x','boss',?,?)",
            (co, ts)); boss = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at)"
            " VALUES ('h_drv','x','driver','Tim Brown',?,?)", (co, ts)); drv = cur.lastrowid


def route(name, date, status, stops):
    cur.execute("INSERT INTO routes (company_id,route_date,route_name,created_by,assigned_to,status,created_at)"
                " VALUES (?,?,?,?,?,?,?)", (co, date, name, boss, drv, status, ts))
    rid = cur.lastrowid
    for k, (act, who, addr, st) in enumerate(stops):
        cur.execute("INSERT INTO stops (route_id,stop_order,customer_name,address,action,status,created_at)"
                    " VALUES (?,?,?,?,?,?,?)", (rid, k + 1, who, addr, act, st, ts))
    return rid


r_today = route("Today Run", today, "in_progress", [
    ("PR", "Marlyn", "12 Oak St", "completed"),
    ("Pickup and Return", "O'Neil Homes", "77 Battlefield Blvd", "open"),
    ("D", "EW", "11496 Shiloh Dr", "open")])
r_done = route("Old Run", "2026-01-05", "completed", [("P", "Done Co", "1 A St", "completed")])
for i in range(8):
    route(f"Filler {i}", "2025-12-%02d" % (i + 1), "completed", [("P", "F", "2 B St", "completed")])
conn.commit(); conn.close()

app.app.config["TESTING"] = True
cl = app.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=drv, company_id=co, role="driver", roles=["driver"], username="h_drv", _csrf_token="tok")

h = cl.get("/dashboard").data.decode()

# ── script structure: the modals must be HTML, not inside a script ────────
ok(h.count("<script") == h.count("</script>"), "every <script> on the dashboard is closed")
modal_at = h.find('id="drv-reorder-modal"')
last_open = h.rfind("<script", 0, modal_at)
ok(modal_at > 0 and h.rfind("</script>", 0, modal_at) > last_open,
   "reorder modal sits outside any script block")
ok("window.drvOpenReorder" in h and "window.drvCancelStop" in h, "dashboard JS still defines the actions")

# ── greeting, clock, up next ───────────────────────────────────────────────
ok("Tim" in h and re.search(r"Good (morning|afternoon|evening)", h), "greets the driver by first name")
ok("Off the clock" in h and "driver_clock_in_now" not in h and 'class="dv-clock-btn"' in h,
   "not clocked in: one big Clock In button")
nxt = h[h.find('class="dv-next"'):h.find("</section>", h.find('class="dv-next"'))]
ok(app.e("O'Neil Homes") in nxt and "Pickup &amp; Return" in nxt and "stop 2 of 3" in nxt,
   "Up Next shows the next open stop with the full action name")
ok("Continue route" in nxt and "/driver/route/%d" % r_today in nxt, "Up Next continues into Cab View")
ok("google.com/maps/dir/" in nxt and "77+Battlefield+Blvd" in nxt, "Up Next has a Navigate link to the stop")
ok('<div class="l">Stops left today</div>' in h and re.search(r'class="drv-stat left"><div class="n">2<', h),
   "stops-left counts today's open stops")

# ── lanes ──────────────────────────────────────────────────────────────────
ok(('data-name="%s" onclick="drvCancelStop(' % app.e("O'Neil Homes")) in h,
   "cancel passes the name via data-name (apostrophes can't break the JS)")
_lanes = re.split(r'<div class="dv-lane(?: is-done)?">', h)
done_lane = next(x for x in _lanes if "Old Run" in x)
ok("All 1 stops done" in done_lane and "drvOpenReorder" not in done_lane and "drvOpenAddStop" not in done_lane,
   "a finished route has no Reorder / Add stop and no stop list")
ok("Full route history" not in h and "?all=1" in h, "older routes link actually shows more (no self-link)")
h_all = cl.get("/dashboard?all=1").data.decode()
ok(h_all.count('class="dv-lane') > h.count('class="dv-lane') and "Show fewer routes" in h_all,
   "?all=1 lists older routes")

# ── clock page ─────────────────────────────────────────────────────────────
ck = cl.get("/driver/clock").data.decode()
ok("Tim Brown" in ck and "ha-avatar" in ck and "Add photo" in ck, "clock header has name + avatar + photo control")
ok('class="to-form"' in ck and 'name="start_date"' in ck and "Request time off" in ck,
   "time-off form uses the aligned grid layout")
cl.post("/driver/clock", data={"_csrf_token": "tok", "clock_action": "clock_in"})
ck2 = cl.get("/driver/clock").data.decode()
ok("&#9899;" not in ck2 and '<span class="ck-dot"></span>Clocked In' in ck2, "Clocked In pill uses a live dot, not ⚫")
ok("ck-elapsed" in ck2, "clocked in: live on-the-clock timer")
h2 = cl.get("/dashboard").data.decode()
ok("On the clock" in h2 and "Clock out" in h2, "dashboard shows the on-the-clock state")

print()
if FAILURES:
    print(f"{len(FAILURES)} FAILURE(S):")
    for f in FAILURES:
        print("  -", f)
    sys.exit(1)
print("ALL DRIVER HOME TESTS PASSED")
