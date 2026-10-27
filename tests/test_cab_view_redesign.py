"""Cab View redesign (2026-10-27): progress segments, Up Next, leg route,
Arrived above Message, previous-stop in the slim sub-bar, and the Complete
Stop rule that had lost its selector.

Run:  python tests/test_cab_view_redesign.py
"""
import os
import sys
import tempfile

TMPDIR = tempfile.mkdtemp(prefix="haultra-cab2-")
os.environ["DATABASE_PATH"] = os.path.join(TMPDIR, "c.db")
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
            " VALUES ('CabCo','cabco','pro','active',5,?)", (ts,)); co = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,company_id,created_at) VALUES ('c_boss','x','boss',?,?)",
            (co, ts)); boss = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at)"
            " VALUES ('c_drv','x','driver','Tim',?,?)", (co, ts)); drv = cur.lastrowid
cur.execute("INSERT INTO routes (company_id,route_date,route_name,created_by,assigned_to,status,started_at,created_at)"
            " VALUES (?,?,?,?,?,'in_progress',?,?)", (co, today, "Run", boss, drv, ts, ts)); rid = cur.lastrowid
STOPS = [("Pull", "Done One", "1 A St", "completed", None),
         ("Pickup and Return", "Crawl Master", "3213 West Neck Rd", "open", "Dominion"),
         ("Delivery", "EW", "11496 Shiloh Dr", "open", None),
         ("Swap", "Big Build", "100 Job Site Rd", "open", None)]
for k, (act, who, addr, st, dump) in enumerate(STOPS):
    cur.execute("INSERT INTO stops (route_id,stop_order,customer_name,address,action,container_size,status,"
                "driver_status,dump_location,created_at) VALUES (?,?,?,?,?,'30yd',?,?,?,?)",
                (rid, k + 1, who, addr, act, st, "completed" if st == "completed" else "pending", dump, ts))
conn.commit(); conn.close()

app.app.config["TESTING"] = True
cl = app.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=drv, company_id=co, role="driver", roles=["driver"], username="c_drv", _csrf_token="tok")

h = cl.get("/driver/route/%d" % rid).get_data(as_text=True)
ok('class="cab-card cab2 cab-phase-1"' in h, "running card uses the redesigned layout")
ok('<div class="cab2-segs" aria-hidden="true"><i class="d"></i><i class="c"></i><i></i><i></i></div>' in h,
   "progress shows one block per stop: done / current / to do")
ok('id="cab-progress-fill"' in h and 'id="cab-sticky-progress"' in h, "live-update hooks are still there")
nxt = h[h.find('class="cab2-next"'):]
ok("Up next" in nxt and "<b>EW</b>" in nxt and "11496 Shiloh Dr" in nxt and "+1" in nxt[:400],
   "Up Next names the following stop and how many more")
ok(h.find('id="cab-arrived-btn"') < h.find('id="msg-boss-btn"'), "Arrived sits right under Navigate, above Message")
ok('class="cab2-prev"' in h and "Previous stop" in h, "previous stop lives in the slim sub-bar")
ok('class="cab-leg-header" id="cab-leg-head"' in h, "leg header updates when the driver switches legs")
ok("Dominion" in h and "cab-leg-chip" in h, "dump leg shows in the leg route")
ok(".cab-primary-zone .cab-complete-btn:not([style])" in h, "Complete Stop has a real CSS rule again")
ok("\n      background: var(--orange, #FF6B1A) !important; color:#0A0A0A !important; border:none !important;" not in h,
   "orphaned selector-less CSS declaration removed")

print()
if FAILURES:
    print(f"{len(FAILURES)} FAILURE(S):")
    for f in FAILURES:
        print("  -", f)
    sys.exit(1)
print("ALL CAB VIEW REDESIGN TESTS PASSED")
