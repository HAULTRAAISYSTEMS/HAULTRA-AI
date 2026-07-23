import os, sys, tempfile, importlib
TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "v.db")
os.environ["SECRET_KEY"] = "v"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")

def ok(c, m):
    print(("PASS" if c else "FAIL") + " - " + m)
    if not c: raise SystemExit("FAILED: " + m)

# ---- rename check ----------------------------------------------------------
src = open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),"app.py")).read()
ok("Paste Dispatch Text" in src and "Paste Boss Text" not in src, "button renamed to 'Paste Dispatch Text'")
ok("Paste dispatch text here" in src and "Paste boss text here" not in src, "placeholder renamed")

# ---- setup -----------------------------------------------------------------
conn = app.get_db(); cur = conn.cursor()
cur.execute("""INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,trial_ends_at,created_at)
               VALUES (?,?,?,?,?,?,?)""",("VenCo","venco","pro","active",10,None,app.now_ts())); co=cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("venboss","x","boss","B",co,app.now_ts())); boss=cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("vendrv","x","driver","D",co,app.now_ts())); drv=cur.lastrowid
# existing address-less vendor (like Gregorys)
cur.execute("INSERT INTO vendors (company_id,name,is_active,created_at) VALUES (?,?,1,?)",(co,"Gregorys",app.now_ts())); greg=cur.lastrowid
# truck + inspection + open defect linked to driver
cur.execute("INSERT INTO trucks (company_id,name,created_at) VALUES (?,?,?)",(co,"Truck 1",app.now_ts())); truck=cur.lastrowid
cur.execute("INSERT INTO inspections (company_id,truck_id,driver_id,type,overall,signature_name,created_at) VALUES (?,?,?,?,?,?,?)",(co,truck,drv,"pre_trip","defects_safe","D",app.now_ts())); insp=cur.lastrowid
cur.execute("""INSERT INTO inspection_items (inspection_id,label,result,defect_status) VALUES (?,?,?,?)""",(insp,"Brakes","defect","open")); item=cur.lastrowid
# active route for the driver so dispatch can insert a stop
cur.execute("INSERT INTO routes (route_date,route_name,assigned_to,created_by,status,company_id,created_at) VALUES (?,?,?,?,?,?,?)",
            (app.today_str(),"r",drv,boss,"in_progress",co,app.now_ts())); rt=cur.lastrowid
cur.execute("INSERT INTO stops (route_id,stop_order,customer_name,address,action,status,driver_status,created_at) VALUES (?,?,?,?,?,?,?,?)",
            (rt,1,"C","1 Main","Pull","open","pending",app.now_ts()))
conn.commit(); conn.close()

app.app.config["TESTING"]=True; cl=app.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=boss, role="boss", roles=["owner","dispatcher"], company_id=co, _csrf_token="tok")

# ---- vendor create with address + learn_location ---------------------------
r = cl.post("/api/vendors", json={"_csrf_token":"tok","name":"maypaw","address":"88 Shop Ln, Suffolk","phone":"757"})
ok(r.status_code==200 and r.get_json().get("success"), "create vendor with address")
conn=app.get_db()
mp=conn.execute("SELECT address FROM vendors WHERE company_id=? AND name='maypaw'",(co,)).fetchone()
inbook=conn.execute("SELECT COUNT(*) n FROM saved_addresses WHERE company_id=? AND customer_name='maypaw'",(co,)).fetchone()["n"]
conn.close()
ok(mp["address"]=="88 Shop Ln, Suffolk", "vendor address stored")
ok(inbook==1, "vendor address joined the address book (quick-add)")

# quick-add suggestion finds the vendor
r=cl.get("/api/address-suggestions?q=maypaw")
ok(any("88 Shop Ln" in (d.get("address") or "") for d in r.get_json()), "vendor is quick-addable via suggestions")

# ---- update existing address-less vendor (Gregorys) ------------------------
r = cl.post(f"/api/vendors/{greg}/update", json={"_csrf_token":"tok","name":"Gregorys","address":"1400 Repair Rd, Norfolk"})
ok(r.status_code==200, "update vendor address accepted")
conn=app.get_db(); ga=conn.execute("SELECT address FROM vendors WHERE id=?",(greg,)).fetchone()["address"]; conn.close()
ok(ga=="1400 Repair Rd, Norfolk", "Gregorys now has an address")

# ---- dispatch uses the vendor's saved address ------------------------------
r = cl.post(f"/api/defects/{item}/resolve", json={"_csrf_token":"tok","action":"sent","vendor_id":greg,"dispatch":"now"})
ok(r.status_code==200 and r.get_json().get("success"), "dispatch driver to Gregorys accepted")
conn=app.get_db()
vs=conn.execute("SELECT customer_name,address FROM stops WHERE route_id=? AND action='Vendor'",(rt,)).fetchone()
conn.close()
ok(vs and vs["address"]=="1400 Repair Rd, Norfolk", "vendor stop uses the vendor's saved address (navigable), not the name")
ok(vs["customer_name"]=="Gregorys", "vendor stop labelled with the vendor name")

# ---- no-address vendor: quick-fill saves back + stop uses it ---------------
# fresh address-less vendor + fresh defect
conn=app.get_db(); cur=conn.cursor()
cur.execute("INSERT INTO vendors (company_id,name,is_active,created_at) VALUES (?,?,1,?)",(co,"NoAddr Shop",app.now_ts())); na=cur.lastrowid
cur.execute("INSERT INTO inspections (company_id,truck_id,driver_id,type,overall,signature_name,created_at) VALUES (?,?,?,?,?,?,?)",(co,truck,drv,"pre_trip","defects_safe","D",app.now_ts())); insp2=cur.lastrowid
cur.execute("INSERT INTO inspection_items (inspection_id,label,result,defect_status) VALUES (?,?,?,?)",
            (insp2,"Lights","defect","open")); item2=cur.lastrowid
conn.commit(); conn.close()
r = cl.post(f"/api/defects/{item2}/resolve", json={"_csrf_token":"tok","action":"sent","vendor_id":na,
            "dispatch":"after_current","vendor_address":"5 Fix St, Hampton"})
ok(r.status_code==200, "dispatch with inline vendor_address accepted")
conn=app.get_db()
na_addr=conn.execute("SELECT address FROM vendors WHERE id=?",(na,)).fetchone()["address"]
vs2=conn.execute("SELECT address FROM stops WHERE route_id=? AND vendor_id=?",(rt,na)).fetchone()
conn.close()
ok(na_addr=="5 Fix St, Hampton", "inline quick-fill saved the address back to the vendor record")
ok(vs2 and vs2["address"]=="5 Fix St, Hampton", "vendor stop uses the just-entered address")

# ---- parser vocab includes vendors -----------------------------------------
conn=app.get_db(); ctx=app._parse_vocab_context(conn, co); conn.close()
ok("KNOWN VENDORS" in ctx and "Gregorys" in ctx and "1400 Repair Rd" in ctx,
   "parser vocabulary lists vendors with addresses (so 'gregorys' resolves)")

# ---- vendors page renders address + no-address prompt ----------------------
html=cl.get("/vendors").get_data(as_text=True)
ok("1400 Repair Rd, Norfolk" in html, "vendors page shows the address")
# make a fresh address-less vendor and confirm the nudge renders
cl.post("/api/vendors", json={"_csrf_token":"tok","name":"Bare Shop"})
html2=cl.get("/vendors").get_data(as_text=True)
ok("No address" in html2, "address-less vendor shows a 'No address' nudge on its card")

print("\nALL VENDOR-ADDRESS TESTS PASSED")
