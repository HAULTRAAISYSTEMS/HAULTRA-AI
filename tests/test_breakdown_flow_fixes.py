import os, sys, tempfile, importlib
TMP=tempfile.mkdtemp()
os.environ.update(DATABASE_PATH=os.path.join(TMP,"f.db"), SECRET_KEY="f", UPLOAD_FOLDER=os.path.join(TMP,"up"))
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app=importlib.import_module("app")

def ok(c,m):
    print(("PASS" if c else "FAIL")+" - "+m)
    if not c: raise SystemExit("FAILED: "+m)

# ---- setup: driver on Truck 7, route = Baycliff → West Neck -----------------
conn=app.get_db(); cur=conn.cursor()
cur.execute("INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,trial_ends_at,created_at) VALUES (?,?,?,?,?,?,?)",("F","f","pro","active",10,None,app.now_ts())); co=cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",("fb","x","boss","Boss",co,app.now_ts())); boss=cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",("fd","x","driver","Dan",co,app.now_ts())); drv=cur.lastrowid
cur.execute("INSERT INTO trucks (company_id,name,created_at) VALUES (?,?,?)",(co,"Truck 7",app.now_ts())); truck=cur.lastrowid
cur.execute("INSERT INTO vendors (company_id,name,address,is_active,created_at) VALUES (?,?,?,1,?)",(co,"maypaw","88 Shop Ln, Suffolk",app.now_ts())); maypaw=cur.lastrowid
cur.execute("INSERT INTO vendors (company_id,name,is_active,created_at) VALUES (?,?,1,?)",(co,"NoAddr Shop",app.now_ts())); noaddr=cur.lastrowid
cur.execute("INSERT INTO inspections (company_id,truck_id,driver_id,type,overall,signature_name,created_at) VALUES (?,?,?,?,?,?,?)",(co,truck,drv,"pre_trip","safe","D",app.now_ts()))
cur.execute("INSERT INTO routes (route_date,route_name,assigned_to,created_by,status,company_id,created_at) VALUES (?,?,?,?,?,?,?)",(app.today_str(),"r",drv,boss,"in_progress",co,app.now_ts())); rt=cur.lastrowid
cur.execute("INSERT INTO stops (route_id,stop_order,customer_name,address,action,status,driver_status,created_at) VALUES (?,?,?,?,?,?,?,?)",(rt,1,"Baycliff","1 Baycliff Rd","Pull","open","pending",app.now_ts())); baycliff=cur.lastrowid
cur.execute("INSERT INTO stops (route_id,stop_order,customer_name,address,action,status,driver_status,created_at) VALUES (?,?,?,?,?,?,?,?)",(rt,2,"West Neck","2 West Neck Rd","Pull","open","pending",app.now_ts())); westneck=cur.lastrowid
conn.commit(); conn.close()

app.app.config["TESTING"]=True; cl=app.app.test_client()
def as_boss():
    with cl.session_transaction() as s: s.update(user_id=boss,role="boss",roles=["owner","dispatcher"],company_id=co,_csrf_token="t")
def as_drv():
    with cl.session_transaction() as s: s.update(user_id=drv,role="driver",roles=["driver"],company_id=co,_csrf_token="t")

def report(issue="Flat tire"):
    as_drv()
    r=cl.post("/api/breakdown/report",data={"_csrf_token":"t","issue_type":issue,"note":"flat","container":"1234","lat":"36.85","lng":"-76.28"},content_type="multipart/form-data",headers={"X-CSRF-Token":"t"})
    return r.get_json()["item_id"]

# ============================================================================
# FIX 1 — vendor stop bound to vendor record; require a vendor
# ============================================================================
item=report()
as_boss()
# dispatch with NO vendor → refused, no nameless stop created
r=cl.post(f"/api/defects/{item}/resolve", json={"_csrf_token":"t","action":"sent","dispatch":"now"}, headers={"X-CSRF-Token":"t"})
ok(r.status_code==200 and r.get_json().get("dispatch",{}).get("dispatched") is False, "dispatch with no vendor is refused")
conn=app.get_db(); nstop=conn.execute("SELECT COUNT(*) n FROM stops WHERE route_id=? AND action='Vendor'",(rt,)).fetchone()["n"]; conn.close()
ok(nstop==0, "no nameless 'the vendor' stop is created when no vendor is picked")

# dispatch WITH maypaw Go NOW → stop bound to vendor with name + navigable address
r=cl.post(f"/api/defects/{item}/resolve", json={"_csrf_token":"t","action":"sent","vendor_id":maypaw,"dispatch":"now"}, headers={"X-CSRF-Token":"t"})
ok(r.status_code==200 and r.get_json()["dispatch"]["dispatched"], "dispatch to maypaw Go NOW accepted")
conn=app.get_db()
vs=conn.execute("SELECT customer_name,address,vendor_id FROM stops WHERE route_id=? AND action='Vendor'",(rt,)).fetchone()
conn.close()
ok(vs and vs["vendor_id"]==maypaw, "vendor stop carries vendor_id")
ok(vs["customer_name"]=="maypaw" and vs["customer_name"]!="the vendor", "stop shows the vendor NAME")
ok("88 Shop Ln" in (vs["address"] or ""), "stop shows the vendor ADDRESS (Navigate has a target)")

# inline add-address for an address-less vendor saves back + stop uses it
item2=report("Brakes")
as_boss()
r=cl.post(f"/api/defects/{item2}/resolve", json={"_csrf_token":"t","action":"sent","vendor_id":noaddr,"dispatch":"after_current","vendor_address":"5 Fix St, Hampton"}, headers={"X-CSRF-Token":"t"})
ok(r.status_code==200, "dispatch with inline vendor_address accepted")
conn=app.get_db()
na=conn.execute("SELECT address FROM vendors WHERE id=?",(noaddr,)).fetchone()["address"]
vs2=conn.execute("SELECT address FROM stops WHERE route_id=? AND vendor_id=?",(rt,noaddr)).fetchone()
conn.close()
ok(na=="5 Fix St, Hampton", "inline address saved back to the address-less vendor")
ok(vs2 and vs2["address"]=="5 Fix St, Hampton", "vendor stop uses the just-entered address")

# reset the route for a clean Fix 2 replay
conn=app.get_db()
conn.execute("DELETE FROM stops WHERE route_id=? AND action='Vendor'",(rt,))
conn.execute("UPDATE stops SET held_at=NULL, status='open', driver_status='pending' WHERE route_id=?",(rt,))
conn.execute("UPDATE inspection_items SET defect_status='deferred' WHERE defect_status='open'")
conn.commit(); conn.close()

# ============================================================================
# FIX 2 — Go NOW reprioritizes: vendor CURRENT, others HELD
# ============================================================================
item3=report()
as_boss()
r=cl.post(f"/api/defects/{item3}/resolve", json={"_csrf_token":"t","action":"sent","vendor_id":maypaw,"dispatch":"now"}, headers={"X-CSRF-Token":"t"})
ok(r.get_json()["dispatch"].get("held")==2, "Go NOW put the 2 remaining stops on hold")
conn=app.get_db()
vstop=conn.execute("SELECT id,stop_order,held_at FROM stops WHERE route_id=? AND action='Vendor'",(rt,)).fetchone()
rows={r2["customer_name"]:r2 for r2 in conn.execute("SELECT customer_name,stop_order,held_at,status FROM stops WHERE route_id=?",(rt,)).fetchall()}
# current = first non-completed by order
cur_stop=conn.execute("SELECT customer_name FROM stops WHERE route_id=? AND status!='completed' ORDER BY stop_order LIMIT 1",(rt,)).fetchone()["customer_name"]
conn.close()
ok(cur_stop=="maypaw" and vstop["held_at"] is None, "vendor stop is the driver's CURRENT stop")
ok(rows["Baycliff"]["held_at"] and rows["West Neck"]["held_at"], "Baycliff + West Neck are HELD")

# held stop cannot be completed
as_drv()
r=cl.post(f"/stop/{baycliff}/toggle", data={"_csrf_token":"t"}, headers={"X-CSRF-Token":"t","X-Requested-With":"XMLHttpRequest"})
ok(r.status_code==409 and (r.get_json() or {}).get("error")=="held", "held stop is blocked from completion")

# route board shows the held state
as_boss()
board=cl.get("/routes/board-partial").get_data(as_text=True)
ok(">Held<" in board or "Held<" in board, "Route Board shows a Held pill")
ok("Release holds" in board, "Route Board offers a manual Release holds")

# Repaired = yes → holds release, Baycliff resumes as current
as_drv()
r=cl.post(f"/api/stops/{vstop['id']}/vendor-arrive", json={"_csrf_token":"t"}, headers={"X-CSRF-Token":"t"})
r=cl.post(f"/api/stops/{vstop['id']}/vendor-complete", json={"_csrf_token":"t","repaired":True}, headers={"X-CSRF-Token":"t"})
ok(r.status_code==200, "Repaired = yes accepted")
conn=app.get_db()
held_left=conn.execute("SELECT COUNT(*) n FROM stops WHERE route_id=? AND held_at IS NOT NULL",(rt,)).fetchone()["n"]
resume=conn.execute("SELECT customer_name FROM stops WHERE route_id=? AND status!='completed' ORDER BY stop_order LIMIT 1",(rt,)).fetchone()["customer_name"]
conn.close()
ok(held_left==0, "Repaired = yes released all holds")
ok(resume=="Baycliff", "Baycliff resumes as the current stop")
# now a released stop CAN complete
r=cl.post(f"/stop/{baycliff}/toggle", data={"_csrf_token":"t"}, headers={"X-CSRF-Token":"t","X-Requested-With":"XMLHttpRequest"})
ok(r.status_code==200 and r.get_json().get("success"), "released stop completes normally")

# manual release endpoint
conn=app.get_db(); conn.execute("UPDATE stops SET held_at=? WHERE id=?",(app.now_ts(),westneck)); conn.commit(); conn.close()
as_boss()
r=cl.post(f"/api/routes/{rt}/release-holds", json={"_csrf_token":"t"}, headers={"X-CSRF-Token":"t"})
ok(r.status_code==200 and r.get_json().get("released")==1, "boss manual release clears holds")

# ============================================================================
# FIX 3 — Open link works + maps URL is tappable
# ============================================================================
conn=app.get_db(); insp=conn.execute("SELECT inspection_id FROM inspection_items WHERE id=?",(item3,)).fetchone()["inspection_id"]; conn.close()
as_boss()
ir=cl.get(f"/inspection/{insp}")
ok(ir.status_code==200, "breakdown defect detail (Open link target) loads")
irtext=ir.get_data(as_text=True)
ok("Breakdown (driver-reported)" in irtext, "detail view labels it a Breakdown, not a Pre-trip inspection")
ok('href="https://maps.google.com' in irtext, "GPS location renders as a tappable link on the detail view")
# open defects card: Open link + linkified maps URL
item4=report("Engine")
as_boss()
mp=cl.get("/maintenance").get_data(as_text=True)
ok("Open →" in mp, "breakdown card exposes an Open → link")
ok('href="https://maps.google.com' in mp, "GPS location is tappable on the boss card too")

print("\nALL BREAKDOWN-FLOW-FIX TESTS PASSED")
