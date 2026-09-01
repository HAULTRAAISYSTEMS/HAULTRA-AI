import os, sys, tempfile, importlib
from datetime import date, timedelta

TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "to.db")
os.environ["SECRET_KEY"] = "to"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")

def ok(c, m):
    print(("PASS" if c else "FAIL") + " - " + m)
    if not c: raise SystemExit("FAILED: " + m)

# ---- 1. recurrence projection unit ----------------------------------------
mon = "2026-08-03"  # a Monday
wd = date.fromisoformat(mon).weekday()
fires = lambda freq, ended, d: app._recurring_fires(freq, date.fromisoformat(mon), wd,
                                                    date.fromisoformat(ended) if ended else None, date.fromisoformat(d))
ok([d for d in ["2026-08-03","2026-08-10","2026-08-17","2026-08-24","2026-08-31","2026-09-07"] if fires("biweekly",None,d)]
   == ["2026-08-03","2026-08-17","2026-08-31"], "biweekly every-other-Monday → Aug 3/17/31")
ok([d for d in ["2026-08-03","2026-08-10","2026-08-17"] if fires("weekly",None,d)]
   == ["2026-08-03","2026-08-10","2026-08-17"], "weekly → every Monday")
ok([d for d in ["2026-08-03","2026-09-07","2026-10-05"] if fires("monthly",None,d)]
   == ["2026-08-03","2026-09-07","2026-10-05"], "monthly-by-weekday → 1st Monday each month")
ok([d for d in ["2026-08-03","2026-08-17","2026-08-31"] if fires("biweekly","2026-08-20",d)]
   == ["2026-08-03","2026-08-17"], "ended_on excludes on/after")

# ---- setup company + boss + driver ----------------------------------------
conn = app.get_db(); cur = conn.cursor()
cur.execute("""INSERT INTO companies (name, slug, subscription_plan, subscription_status, max_drivers,
               trial_ends_at, created_at, timezone, driver_day_start_rule, driver_day_end_rule)
               VALUES (?,?,?,?,?,?,?,?,?,?)""",
            ("TO Co","toco","pro","active",10,None,app.now_ts(),"America/New_York","manual","manual"))
co = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("toboss","x","boss","Boss",co,app.now_ts())); boss=cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("totim","x","driver","Tim",co,app.now_ts())); tim=cur.lastrowid
conn.commit(); conn.close()

app.app.config["TESTING"]=True
cl = app.app.test_client()
def as_driver():
    with cl.session_transaction() as s:
        s.update(user_id=tim, role="driver", roles=["driver"], company_id=co, _csrf_token="tok")
def as_boss():
    with cl.session_transaction() as s:
        s.update(user_id=boss, role="boss", roles=["owner","dispatcher"], company_id=co, _csrf_token="tok")

today = date.fromisoformat(app.today_str())
# Far out, deliberately. The recurring-rule section below projects onto
# Mondays from next week through today+42, and these one-time absences used to
# sit at today+20/+21 — which lands exactly on the second recurring occurrence
# whenever today is a Monday. The override assertion then failed because the
# separate one-time absence still covered that date, and CI went red on a
# calendar coincidence rather than a real defect. Verified: the override
# behaviour itself is correct in isolation.
d1 = (today + timedelta(days=200)).isoformat()
d2 = (today + timedelta(days=201)).isoformat()

# ---- 2. driver request → pending → boss approve → approved -----------------
as_driver()
r = cl.post("/time-off/request", data={"_csrf_token":"tok","start_date":d1,"end_date":d2,"reason":"family"})
ok(r.status_code in (302,200), "driver time-off request accepted")
conn=app.get_db(); req=conn.execute("SELECT * FROM time_off_requests WHERE company_id=? AND driver_id=?",(co,tim)).fetchone(); conn.close()
ok(req and req["status"]=="pending", "request stored pending")
rid=req["id"]
# past-date rejected
r=cl.post("/time-off/request", data={"_csrf_token":"tok","start_date":(today-timedelta(days=2)).isoformat()})
conn=app.get_db(); n=conn.execute("SELECT COUNT(*) n FROM time_off_requests WHERE driver_id=?",(tim,)).fetchone()["n"]; conn.close()
ok(n==1, "past-date request rejected (no new row)")
# overlap duplicate rejected
r=cl.post("/time-off/request", data={"_csrf_token":"tok","start_date":d1,"end_date":d1})
conn=app.get_db(); n=conn.execute("SELECT COUNT(*) n FROM time_off_requests WHERE driver_id=?",(tim,)).fetchone()["n"]; conn.close()
ok(n==1, "overlapping duplicate request rejected")

as_boss()
r=cl.post(f"/time-off/{rid}/decide", data={"_csrf_token":"tok","decision":"approved","boss_note":"ok enjoy"})
conn=app.get_db()
row=conn.execute("SELECT status,boss_note FROM time_off_requests WHERE id=?",(rid,)).fetchone()
off=app._approved_off_on(conn, co, tim, d1)
conn.close()
ok(row["status"]=="approved" and row["boss_note"]=="ok enjoy", "boss approved with note")
ok(off is not None, "_approved_off_on true on approved date")

# ---- 3. Route Board OFF badge + reassign warning ---------------------------
# give tim a route on d1 so a lane exists
conn=app.get_db()
conn.execute("INSERT INTO routes (route_date,route_name,assigned_to,created_by,status,company_id,created_at) VALUES (?,?,?,?,?,?,?)",
             (d1,"r",tim,boss,"open",co,app.now_ts()))
rt=conn.execute("SELECT id FROM routes WHERE company_id=? AND assigned_to=?",(co,tim)).fetchone()["id"]
conn.execute("INSERT INTO stops (route_id,stop_order,customer_name,address,action,status,created_at) VALUES (?,?,?,?,?,?,?)",
             (rt,1,"C","1 Main","Pull","open",app.now_ts()))
conn.commit(); conn.close()
# reassign to tim on an off date → warning flash (still reassigns)
as_boss()
r=cl.post(f"/route/{rt}/reassign", data={"_csrf_token":"tok","driver_id":str(tim)}, follow_redirects=False)
ok(r.status_code in (302,200), "reassign to off driver still succeeds (warn not block)")

# ---- 4. deny + cancel + already-scheduled-off ------------------------------
as_driver()
d3=(today+timedelta(days=210)).isoformat()
cl.post("/time-off/request", data={"_csrf_token":"tok","start_date":d3})
conn=app.get_db(); rid3=conn.execute("SELECT id FROM time_off_requests WHERE driver_id=? AND start_date=?",(tim,d3)).fetchone()["id"]; conn.close()
as_boss(); cl.post(f"/time-off/{rid3}/decide", data={"_csrf_token":"tok","decision":"denied","boss_note":"need you"})
conn=app.get_db(); st=conn.execute("SELECT status FROM time_off_requests WHERE id=?",(rid3,)).fetchone()["status"]; conn.close()
ok(st=="denied","deny path works")
# cancel while pending
as_driver()
d4=(today+timedelta(days=220)).isoformat()
cl.post("/time-off/request", data={"_csrf_token":"tok","start_date":d4})
conn=app.get_db(); rid4=conn.execute("SELECT id FROM time_off_requests WHERE driver_id=? AND start_date=?",(tim,d4)).fetchone()["id"]; conn.close()
cl.post(f"/time-off/{rid4}/cancel", data={"_csrf_token":"tok"})
conn=app.get_db(); gone=conn.execute("SELECT COUNT(*) n FROM time_off_requests WHERE id=?",(rid4,)).fetchone()["n"]; conn.close()
ok(gone==0,"cancel-while-pending removes the request")

# ---- 5. recurring create + approve + override ------------------------------
# make a future Monday
fut = today + timedelta(days=(7 - today.weekday()) % 7 or 7)   # next Monday
while fut.weekday()!=0: fut+=timedelta(days=1)
as_driver()
cl.post("/recurring-off/create", data={"_csrf_token":"tok","frequency":"biweekly","start_date":fut.isoformat()})
conn=app.get_db(); rule=conn.execute("SELECT * FROM recurring_days_off WHERE driver_id=?",(tim,)).fetchone(); conn.close()
ok(rule and rule["status"]=="pending","driver-created recurring rule is pending")
as_boss(); cl.post(f"/recurring-off/{rule['id']}/action", data={"_csrf_token":"tok","act":"approve"})
conn=app.get_db()
occ2 = (fut + timedelta(days=14)).isoformat()
m=app._time_off_for_range(conn, co, tim, fut, fut+timedelta(days=42))
conn.close()
ok(m.get(fut.isoformat(),{}).get("status")=="approved" and m.get(occ2,{}).get("status")=="approved",
   "approved recurring projects onto matching future Mondays")
# override the 2nd occurrence → flips to working
as_boss(); cl.post(f"/recurring-off/{rule['id']}/action", data={"_csrf_token":"tok","act":"override","off_date":occ2})
conn=app.get_db(); m2=app._time_off_for_range(conn, co, tim, fut, fut+timedelta(days=42)); conn.close()
ok(fut.isoformat() in m2 and occ2 not in m2, "override flips that one date to working, rest unchanged")

# ---- 6. late check-in + clock-in clears it ---------------------------------
as_driver()
r=cl.post("/late/checkin", data={"_csrf_token":"tok","eta":"7:30","reason":"traffic"})
ok(r.status_code in (302,200),"late check-in accepted (not clocked in)")
conn=app.get_db()
la=app._late_active(conn, co, tim, app.today_str(), {"driver_day_start_rule":"manual","driver_day_end_rule":"manual"})
conn.close()
ok(la is not None and la["eta"]=="7:30","late check-in active with ETA 7:30")
# clock in → clears
r=cl.post("/driver/clock", data={"_csrf_token":"tok","clock_action":"clock_in"})
conn=app.get_db()
la2=app._late_active(conn, co, tim, app.today_str(), {"driver_day_start_rule":"manual","driver_day_end_rule":"manual"})
conn.close()
ok(la2 is None,"clocking in auto-clears the late check-in")
# late blocked once clocked in
r=cl.post("/late/checkin", data={"_csrf_token":"tok","eta":"8:00"})
conn=app.get_db(); active=conn.execute("SELECT COUNT(*) n FROM late_checkins WHERE driver_id=? AND cleared_at IS NULL",(tim,)).fetchone()["n"]; conn.close()
ok(active==0,"late check-in blocked when already clocked in")

# ---- 7. pages render -------------------------------------------------------
as_boss()
cal=cl.get("/team-time-off")
ok(cal.status_code==200 and b"Team Time Off" in cal.data,"team calendar renders")
as_driver()
clk=cl.get("/driver/clock")
ok(clk.status_code==200 and b"Time Off" in clk.data,"driver clock page renders Time Off card")

# ---- 8. weekly-hours OFF row ----------------------------------------------
_st = {"workweek_start_day":"Monday","driver_day_start_rule":"manual","driver_day_end_rule":"manual"}
conn=app.get_db()
wk = app.company_week_start_for(_st, app._company_local_now(_st))
summ = app.get_driver_week_summary(conn, tim, wk, _st, app._company_local_now(_st))
conn.close()
# Pick a day with no punches. The card only renders an OFF row when the driver
# did NOT work that day ("day['date'] in _off and not day['start']"), and an
# earlier section of this file clocks the driver in today — which is days[0]
# whenever today is the first day of the workweek. Asserting on days[0]
# therefore failed on Mondays for a reason that has nothing to do with time off.
offday = next((d["date"] for d in summ["days"] if not d["start"]), summ["days"][-1]["date"])
card = app.render_week_hours_card(summ, "/driver/clock", 0, off_dates={offday})
ok("OFF" in card, "weekly-hours card renders an OFF row for an approved-off day")

print("\nALL TIME-OFF TESTS PASSED")
