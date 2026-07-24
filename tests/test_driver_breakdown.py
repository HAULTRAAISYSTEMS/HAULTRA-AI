import os, sys, tempfile, importlib, io
TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "bd.db")
os.environ["SECRET_KEY"] = "b"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")

def ok(c, m):
    print(("PASS" if c else "FAIL") + " - " + m)
    if not c: raise SystemExit("FAILED: " + m)

# ---- helper units ----------------------------------------------------------
ok("Flat tire" in app.BREAKDOWN_ISSUE_TYPES and "Hydraulics" in app.BREAKDOWN_ISSUE_TYPES,
   "issue-type picker options defined")

# ---- setup: today's scenario -----------------------------------------------
conn = app.get_db(); cur = conn.cursor()
cur.execute("""INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,trial_ends_at,created_at,driver_day_start_rule,driver_day_end_rule)
               VALUES (?,?,?,?,?,?,?,?,?)""",("BDCo","bdco","pro","active",10,None,app.now_ts(),"manual","manual")); co=cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("bdboss","x","boss","The Boss",co,app.now_ts())); boss=cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("bdtim","x","driver","Tim Brown",co,app.now_ts())); tim=cur.lastrowid
cur.execute("INSERT INTO trucks (company_id,name,created_at) VALUES (?,?,?)",(co,"Truck 7",app.now_ts())); truck=cur.lastrowid
# vendor "maypaw" with a saved (navigable) address
cur.execute("INSERT INTO vendors (company_id,name,address,is_active,created_at) VALUES (?,?,?,1,?)",
            (co,"maypaw","88 Shop Ln, Suffolk",app.now_ts())); maypaw=cur.lastrowid
# Tim did a pre-trip on Truck 7 this morning → establishes his truck.
cur.execute("INSERT INTO inspections (company_id,truck_id,driver_id,type,overall,signature_name,created_at) VALUES (?,?,?,?,?,?,?)",
            (co,truck,tim,"pre_trip","safe","Tim",app.now_ts()))
# Active route today with a live stop (the dump site he's working).
cur.execute("INSERT INTO routes (route_date,route_name,assigned_to,created_by,status,company_id,created_at) VALUES (?,?,?,?,?,?,?)",
            (app.today_str(),"r",tim,boss,"in_progress",co,app.now_ts())); rt=cur.lastrowid
cur.execute("INSERT INTO stops (route_id,stop_order,customer_name,address,action,container_size,status,driver_status,created_at) VALUES (?,?,?,?,?,?,?,?,?)",
            (rt,1,"Dump Site","1 Landfill Rd","Dump","20yd","open","pending",app.now_ts())); dump_stop=cur.lastrowid
conn.commit(); conn.close()

# the driver's truck is resolvable from his latest inspection (what the endpoint uses)
conn=app.get_db()
_last=conn.execute("SELECT truck_id FROM inspections WHERE driver_id=? ORDER BY id DESC LIMIT 1",(tim,)).fetchone()
ok(_last and _last["truck_id"]==truck, "driver's truck resolvable from his latest inspection"); conn.close()

app.app.config["TESTING"]=True; cl=app.app.test_client()
def as_boss():
    with cl.session_transaction() as s: s.update(user_id=boss,role="boss",roles=["owner","dispatcher"],company_id=co,_csrf_token="tok")
def as_tim():
    with cl.session_transaction() as s: s.update(user_id=tim,role="driver",roles=["driver"],company_id=co,_csrf_token="tok")

# ---- 1. DRIVER taps Flat tire + photo at the dump site ---------------------
as_tim()
jpg = (b"\xff\xd8\xff\xe0" + b"0"*200 + b"\xff\xd9")
r = cl.post("/api/breakdown/report",
            data={"_csrf_token":"tok","issue_type":"Flat tire","note":"flat right rear",
                  "container":"1234","lat":"36.8508","lng":"-76.2859",
                  "photo":(io.BytesIO(jpg),"breakdown.jpg")},
            content_type="multipart/form-data", headers={"X-CSRF-Token":"tok"})
ok(r.status_code==200 and r.get_json().get("success"), "driver reports a breakdown")
item_id = r.get_json()["item_id"]

conn=app.get_db()
row=conn.execute("""SELECT ii.label, ii.result, ii.defect_status, ii.note, i.is_breakdown, i.truck_id, i.driver_id
                      FROM inspection_items ii JOIN inspections i ON ii.inspection_id=i.id WHERE ii.id=?""",(item_id,)).fetchone()
ok(row and row["label"]=="Flat tire" and row["result"]=="defect" and row["defect_status"]=="open",
   "breakdown stored as an OPEN driver-reported defect")
ok(row["is_breakdown"]==1 and row["truck_id"]==truck and row["driver_id"]==tim, "on a synthetic breakdown inspection for the right truck/driver")
ok(row["note"] and "1234" in row["note"] and "maps.google" in row["note"], "note carries container # and a GPS maps link")
msg=conn.execute("SELECT body,priority,defect_item_id FROM messages WHERE route_id=? ORDER BY id DESC LIMIT 1",(rt,)).fetchone()
ok(msg and msg["priority"]=="urgent" and msg["defect_item_id"]==item_id and "BREAKDOWN" in msg["body"] and "Flat tire" in msg["body"],
   "boss gets an URGENT alert on the route thread")
ph=conn.execute("SELECT COUNT(*) n FROM maintenance_photos WHERE defect_item_id=?",(item_id,)).fetchone()["n"]
ok(ph==1, "driver's photo attached via the maintenance-photo pipeline")
conn.close()

# ---- 2. BOSS surfaces: route board chip + actionable maintenance card -------
as_boss()
board = cl.get("/routes/board-partial").get_data(as_text=True)
ok("BREAKDOWN" in board, "Route Board lane shows the red ⚠ BREAKDOWN chip")
mnt = cl.get("/maintenance").get_data(as_text=True)
ok("DRIVER BREAKDOWN" in mnt and "Flat tire" in mnt and "Tim Brown" in mnt, "Maintenance shows the breakdown card with driver + issue")
ok("No vendor" in mnt and ("Send to vendor" in mnt or "showSend" in mnt), "card offers vendor dispatch + 'No vendor — continue route'")

# breakdown must NOT masquerade as a DVIR in the driver's inspection history
as_tim()
myinsp = cl.get("/my-inspections").get_data(as_text=True)
ok("out of service" not in myinsp.lower() or "Flat tire" not in myinsp, "breakdown excluded from DVIR inspection history")

# ---- 3. BOSS picks maypaw, Go NOW (reuses the defect vendor-dispatch) --------
as_boss()
r = cl.post(f"/api/defects/{item_id}/resolve",
            json={"_csrf_token":"tok","action":"sent","vendor_id":maypaw,"dispatch":"now"},
            headers={"X-CSRF-Token":"tok"})
ok(r.status_code==200 and r.get_json().get("dispatch",{}).get("dispatched"), "boss dispatches driver to maypaw Go NOW")
conn=app.get_db()
vstop=conn.execute("SELECT id,address,vendor_id,action,stop_order FROM stops WHERE route_id=? AND action='Vendor'",(rt,)).fetchone()
ok(vstop and vstop["vendor_id"]==maypaw and "Shop Ln" in (vstop["address"] or ""),
   "vendor stop inserted into the route with the navigable saved address")
vs=conn.execute("SELECT vendor_status FROM inspection_items WHERE id=?",(item_id,)).fetchone()["vendor_status"]
ok(vs=="scheduled", "status walked BREAKDOWN → VENDOR SCHEDULED")
conn.close()
# chip flips from BREAKDOWN to the vendor lifecycle pill
board2 = cl.get("/routes/board-partial").get_data(as_text=True)
ok("BREAKDOWN" not in board2, "BREAKDOWN chip clears once dispatched (vendor pills take over)")

# ---- 4. lifecycle walk: EN ROUTE → AT VENDOR → Repaired=yes -----------------
# make the vendor stop current (finish the dump stop), then the Cab View bumps EN ROUTE
conn=app.get_db(); conn.execute("UPDATE stops SET status='completed', completed_at=? WHERE id=?",(app.now_ts(),dump_stop)); conn.commit(); conn.close()
as_tim()
ok(cl.get(f"/driver/route/{rt}").status_code==200, "driver opens Cab View with the vendor stop current")
conn=app.get_db(); ok(conn.execute("SELECT vendor_status FROM inspection_items WHERE id=?",(item_id,)).fetchone()["vendor_status"]=="en_route","→ EN ROUTE"); conn.close()
r=cl.post(f"/api/stops/{vstop['id']}/vendor-arrive", json={"_csrf_token":"tok"}, headers={"X-CSRF-Token":"tok"})
ok(r.status_code==200, "driver marks arrival at maypaw")
conn=app.get_db(); ok(conn.execute("SELECT vendor_status FROM inspection_items WHERE id=?",(item_id,)).fetchone()["vendor_status"]=="at_vendor","→ AT VENDOR"); conn.close()
r=cl.post(f"/api/stops/{vstop['id']}/vendor-complete", json={"_csrf_token":"tok","repaired":True,"note":"new tire on"}, headers={"X-CSRF-Token":"tok"})
ok(r.status_code==200, "driver finishes the vendor visit — Repaired = yes")
conn=app.get_db()
fin=conn.execute("SELECT defect_status,vendor_status FROM inspection_items WHERE id=?",(item_id,)).fetchone()
ok(fin["defect_status"]=="repaired" and fin["vendor_status"] is None, "Repaired = yes closes the breakdown")
conn.close()

# ---- 5. RECORD: the truck's maintenance log shows the full event ------------
as_boss()
truckp = cl.get(f"/trucks/{truck}").get_data(as_text=True)
ok("Flat tire" in truckp, "Maintenance log records the breakdown (issue type) on the truck")
mnt2 = cl.get("/maintenance").get_data(as_text=True)
ok("DRIVER BREAKDOWN" not in mnt2, "resolved breakdown no longer sits in Open Defects")

# ---- 6. 'No vendor — continue route' path ----------------------------------
as_tim()
r = cl.post("/api/breakdown/report", data={"_csrf_token":"tok","issue_type":"Other","note":"loose mirror"},
            content_type="multipart/form-data", headers={"X-CSRF-Token":"tok"})
item2 = r.get_json()["item_id"]
as_boss()
r = cl.post(f"/api/breakdown/{item2}/continue", json={"_csrf_token":"tok","note":"finish the day, fix at yard"},
            headers={"X-CSRF-Token":"tok"})
ok(r.status_code==200 and r.get_json().get("success"), "boss answers 'No vendor — continue route'")
conn=app.get_db()
st=conn.execute("SELECT defect_status FROM inspection_items WHERE id=?",(item2,)).fetchone()["defect_status"]
ok(st=="deferred", "continue-route clears the breakdown (deferred, no vendor stop)")
drv_msg=conn.execute("SELECT body FROM messages WHERE route_id=? ORDER BY id DESC LIMIT 1",(rt,)).fetchone()["body"]
ok("Continue your route" in drv_msg, "driver told to continue")
noveh=conn.execute("SELECT COUNT(*) n FROM stops WHERE route_id=? AND action='Vendor' AND vendor_id IS NULL",(rt,)).fetchone()["n"]
ok(noveh==0, "no vendor stop was inserted for the continue-route answer")
conn.close()

print("\nALL DRIVER-BREAKDOWN TESTS PASSED")
