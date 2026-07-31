import os, sys, tempfile, importlib, io
TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "a.db")
os.environ["SECRET_KEY"] = "a"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")

def ok(c, m):
    print(("PASS" if c else "FAIL") + " - " + m)
    if not c: raise SystemExit("FAILED: " + m)

# ---- helper unit -----------------------------------------------------------
h_photo = app.avatar_html({"id": 5, "full_name": "Tim Brown", "username": "tim",
                           "avatar_path": "static/uploads/avatars/av_5_x.jpg"}, 32)
ok("<img" in h_photo and 'src="/avatar/5"' in h_photo,
   "avatar_html renders a protected avatar URL")
h_init = app.avatar_html({"id": 5, "full_name": "Tim Brown", "username": "tim", "avatar_path": None}, 32)
ok("ha-avatar-initials" in h_init and ">TB<" in h_init, "no photo → deterministic initials avatar (TB)")
ok("<img" not in h_init, "initials fallback is never a broken <img>")
ok(app._avatar_color(5) == app._avatar_color(5), "avatar color deterministic per id")

# ---- setup -----------------------------------------------------------------
conn = app.get_db(); cur = conn.cursor()
cur.execute("""INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,trial_ends_at,created_at,driver_day_start_rule,driver_day_end_rule)
               VALUES (?,?,?,?,?,?,?,?,?)""",("ACo","aco","pro","active",10,None,app.now_ts(),"manual","manual")); co=cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("aboss","x","boss","The Boss",co,app.now_ts())); boss=cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("atim","x","driver","Tim Brown",co,app.now_ts())); tim=cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("amarcus","x","driver","Marcus Lee",co,app.now_ts())); marc=cur.lastrowid
cur.execute("INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,created_at) VALUES (?,?,?,?,?,?)",
            ("OtherCo","otherco","pro","active",10,app.now_ts())); other_co=cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("outsider","x","driver","Other Driver",other_co,app.now_ts())); outsider=cur.lastrowid
# truck + inspection by tim
cur.execute("INSERT INTO trucks (company_id,name,created_at) VALUES (?,?,?)",(co,"Truck 7",app.now_ts())); truck=cur.lastrowid
cur.execute("INSERT INTO inspections (company_id,truck_id,driver_id,type,overall,signature_name,created_at) VALUES (?,?,?,?,?,?,?)",
            (co,truck,tim,"pre_trip","safe","Tim",app.now_ts()))
# route today for tim + a stop + a message from tim
cur.execute("INSERT INTO routes (route_date,route_name,assigned_to,created_by,status,company_id,created_at) VALUES (?,?,?,?,?,?,?)",
            (app.today_str(),"r",tim,boss,"in_progress",co,app.now_ts())); rt=cur.lastrowid
cur.execute("INSERT INTO stops (route_id,stop_order,customer_name,address,action,status,driver_status,created_at) VALUES (?,?,?,?,?,?,?,?)",
            (rt,1,"C","1 Main","Pull","open","pending",app.now_ts()))
cur.execute("INSERT INTO messages (route_id,sender_user_id,body,created_at) VALUES (?,?,?,?)",(rt,tim,"on my way",app.now_ts()))
# tim off today so team-time-off day detail lists him
cur.execute("INSERT INTO time_off_requests (company_id,driver_id,start_date,end_date,status,created_at) VALUES (?,?,?,?,'approved',?)",
            (co,tim,app.today_str(),app.today_str(),app.now_ts()))
conn.commit(); conn.close()

app.app.config["TESTING"]=True; cl=app.app.test_client()
def as_boss():
    with cl.session_transaction() as s: s.update(user_id=boss,role="boss",roles=["owner","dispatcher"],company_id=co,_csrf_token="tok")
def as_tim():
    with cl.session_transaction() as s: s.update(user_id=tim,role="driver",roles=["driver"],company_id=co,_csrf_token="tok")

# ---- upload: driver sets own photo ----------------------------------------
as_tim()
jpg = (b"\xff\xd8\xff\xe0" + b"0"*200 + b"\xff\xd9")
r = cl.post(f"/api/users/{tim}/avatar", data={"_csrf_token":"tok","photo":(io.BytesIO(jpg),"avatar.jpg")},
            content_type="multipart/form-data", headers={"X-CSRF-Token":"tok"})
ok(r.status_code==200 and r.get_json().get("success"), "driver uploads own avatar")
conn=app.get_db(); ap=conn.execute("SELECT avatar_path FROM users WHERE id=?",(tim,)).fetchone()["avatar_path"]; conn.close()
ok(ap and "avatars/av_%d_" % tim in ap, "avatar_path stored in DB")
ok(os.path.isfile(os.path.join(app.AVATAR_FOLDER, os.path.basename(ap))), "avatar file written to disk")
conn=app.get_db(); conn.execute("UPDATE users SET avatar_path=? WHERE id=?", (ap, outsider)); conn.commit(); conn.close()
ok(cl.get("/" + ap).status_code == 404, "raw static upload URL is blocked")
ok(cl.get(f"/avatar/{tim}").status_code == 200, "protected same-company avatar URL works")
ok(cl.get(f"/avatar/{outsider}").status_code == 404, "avatar endpoint does not cross company boundaries")

# ---- driver cannot set another driver's avatar ----------------------------
r = cl.post(f"/api/users/{marc}/avatar", data={"_csrf_token":"tok","photo":(io.BytesIO(jpg),"a.jpg")},
            content_type="multipart/form-data", headers={"X-CSRF-Token":"tok"})
ok(r.status_code==403, "driver cannot upload another driver's avatar")

# ---- boss can set any driver's avatar -------------------------------------
as_boss()
r = cl.post(f"/api/users/{marc}/avatar", data={"_csrf_token":"tok","photo":(io.BytesIO(jpg),"m.jpg")},
            content_type="multipart/form-data", headers={"X-CSRF-Token":"tok"})
ok(r.status_code==200, "boss uploads a driver's avatar")

# ---- displays render the avatar --------------------------------------------
board = cl.get("/routes/board-partial").get_data(as_text=True)
ok((f'/avatar/{tim}') in board, "Route Board lane shows the driver's protected photo")
team = cl.get("/team").get_data(as_text=True)
ok("ha-avatar" in team and ("Add photo" in team or "Change" in team or "Photo" in team),
   "Team page shows avatars + an upload control")
th = cl.get("/boss/team-hours").get_data(as_text=True)
ok("ha-avatar" in th, "Team Hours rows show avatars")
tto = cl.get(f"/team-time-off?day={app.today_str()}").get_data(as_text=True)
ok("ha-avatar" in tto, "Team Time Off day detail shows avatars")
msgs = cl.get(f"/route/{rt}/messages").get_json()["messages"]
ok(msgs and msgs[0]["sender_avatar"] == f"/avatar/{tim}" and msgs[0]["sender_initial"]=="TB" and msgs[0]["sender_color"],
   "message thread JSON carries sender avatar/initial/color")
truckp = cl.get(f"/trucks/{truck}").get_data(as_text=True)
ok("ha-avatar" in truckp, "Truck detail shows the inspecting driver's avatar")

# ---- driver clock header shows own avatar + control -----------------------
as_tim()
clk = cl.get("/driver/clock").get_data(as_text=True)
ok("ha-avatar" in clk and ("Change photo" in clk or "Add photo" in clk), "clock page header has avatar + control")

# ---- remove → initials fallback -------------------------------------------
r = cl.post(f"/api/users/{tim}/avatar/remove", data={"_csrf_token":"tok"}, headers={"X-CSRF-Token":"tok"})
ok(r.status_code==200, "remove avatar accepted")
conn=app.get_db(); ap2=conn.execute("SELECT avatar_path FROM users WHERE id=?",(tim,)).fetchone()["avatar_path"]; conn.close()
ok(ap2 is None, "avatar_path cleared on remove")
as_boss()
board2 = cl.get("/routes/board-partial").get_data(as_text=True)
ok("ha-avatar-initials" in board2, "after removal the lane falls back to an initials avatar (never broken)")

print("\nALL DRIVER-AVATAR TESTS PASSED")
