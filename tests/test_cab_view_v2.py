import os, sys, tempfile, importlib
TMP=tempfile.mkdtemp()
os.environ["DATABASE_PATH"]=os.path.join(TMP,"v2.db"); os.environ["SECRET_KEY"]="v2"
os.environ["UPLOAD_FOLDER"]=os.path.join(TMP,"up"); os.makedirs(os.environ["UPLOAD_FOLDER"],exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app=importlib.import_module("app")
def ok(c,m):
    print(("PASS" if c else "FAIL")+" - "+m)
    if not c: raise SystemExit("FAILED: "+m)

app.init_db()
conn=app.get_db();cur=conn.cursor();ts=app.now_ts();today=app.today_str()
cur.execute("INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,created_at) VALUES (?,?,?,?,?,?)",("V2","v2co","pro","active",10,ts));co=cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,company_id,created_at) VALUES (?,?,?,?,?)",("v_boss","x","boss",co,ts));boss=cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",("v_drv","x","driver","Dave",co,ts));drv=cur.lastrowid
cur.execute("INSERT INTO routes (company_id,route_date,route_name,created_by,assigned_to,status,started_at,created_at) VALUES (?,?,?,?,?,'in_progress',?,?)",(co,today,"R",boss,drv,ts,ts));rid=cur.lastrowid
cur.execute("""INSERT INTO stops (route_id,stop_order,customer_name,address,city,state,action,container_size,dump_location,status,driver_status,active_leg,created_at)
   VALUES (?,?,?,?,?,?,?,?,?,?,?, 'primary', ?)""",(rid,1,"Marlyn","3104 Elm","Norfolk","VA","Pickup and Return","30yd","Dominion","open","pending",ts))
sid=cur.execute("SELECT id FROM stops LIMIT 1").fetchone()[0]
conn.commit();conn.close()

# _action_badge_code unit
ok(app._action_badge_code("Pickup and Return")=="pr", "PR code")
ok(app._action_badge_code("Pull")=="p", "P code")
ok(app._action_badge_code("Delivery")=="d", "D code")
ok(app._action_badge_code("Swap")=="s", "S code")
ok(app._action_badge_code("Relocate")=="r", "R code")
ok(app._action_badge_code("Yard")=="yard", "YARD code")

app.app.config["TESTING"]=True
cl=app.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=drv, company_id=co, role="driver", _csrf_token="tok")
def cab(): return cl.get("/driver/route/%d"%rid).get_data(as_text=True)

# ---- Phase 1 (en route) ----
h=cab()
ok("cab-phase-1" in h, "renders phase 1 when not arrived")
ok('class="cab-primary' in h and "Tap to Navigate" in h, "phase 1 primary = Tap to Navigate")
ok(h.count('class="cab-primary')==1, "exactly one cab-primary element in phase 1 (%d)"%h.count('class="cab-primary'))
ok("Arrived at Stop" in h and "cab-neutral cab-arrived-btn" in h, "phase 1 Arrived button is neutral")
ok('class="cab-navstrip"' not in h, "phase 1 has no nav strip")
ok('badge-pr' in h, "action badge uses palette code class (badge-pr)")
# leg chip separator: label + value in separate spans (no literal 'DUMPDominion')
ok('cab-leg-chip-lbl' in h and 'cab-leg-chip-sub' in h, "leg chip label + value are separate spans")
ok('DUMPDominion' not in h and 'PICKUP AND RETURNMarlyn' not in h, "no concatenated leg text")

# ---- Tap Arrived → phase 2 ----
r=cl.post("/stop/%d/driver-action"%sid, data={"_csrf_token":"tok","action":"arrived"})
ok(app.get_db().execute("SELECT arrived_at FROM stops WHERE id=?",(sid,)).fetchone()["arrived_at"] is not None, "arrived_at persisted server-side")
h=cab()
ok("cab-phase-2" in h, "renders phase 2 after arrival")
ok('class="cab-navstrip"' in h and "Navigate" in h, "phase 2 collapses nav to a strip")
ok('class="cab-primary-zone"' in h and "Complete" in h, "phase 2 shows Complete in the primary zone")
ok("Not here yet" in h and 'value="unarrive"' in h, "phase 2 has the 'Not here yet' undo")

# ---- Force-quit simulation: a fresh GET still shows phase 2 (arrived_at persists) ----
with cl.session_transaction() as s:
    s.update(user_id=drv, company_id=co, role="driver", _csrf_token="tok")
ok("cab-phase-2" in cab(), "force-quit + reopen stays in phase 2")

# ---- Undo arrival → phase 1 ----
r=cl.post("/stop/%d/driver-action"%sid, data={"_csrf_token":"tok","action":"unarrive"})
row=app.get_db().execute("SELECT driver_status,arrived_at FROM stops WHERE id=?",(sid,)).fetchone()
ok(row["driver_status"]=="pending" and row["arrived_at"] is None, "unarrive resets to pending + clears arrived_at")
ok("cab-phase-1" in cab(), "after 'Not here yet' the card returns to phase 1")

# ---- No red/teal in the badge palette classes ----
theme=open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),"static/css/haultra-theme.css")).read()
import re
badge_block=theme[theme.index("--badge-ink"):theme.index("--radius")]
for bad in ["#FF5252","#00E5CC"]:
    ok(bad not in badge_block, "no reserved color %s in badge tokens"%bad)

# ---- Route Board badge picks up the palette ----
with cl.session_transaction() as s:
    s.update(user_id=boss, company_id=co, role="boss", roles=["owner","dispatcher"], _csrf_token="tok")
board=cl.get("/routes").get_data(as_text=True)
ok("badge-pr" in board, "Route Board badge uses the new palette code class")

print("\nALL CAB-VIEW-V2 TESTS PASSED")
