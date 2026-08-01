import os, sys, tempfile, importlib
TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "ds.db")
os.environ["SECRET_KEY"] = "ds"
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
cur.execute("INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,created_at) VALUES (?,?,?,?,?,?)",
            ("DsCo","dsco","pro","active",10,ts)); co = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,company_id,created_at) VALUES (?,?,?,?,?)",
            ("ds_boss","x","boss",co,ts)); boss = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,company_id,created_at) VALUES (?,?,?,?,?)",
            ("ds_drv","x","driver",co,ts)); drv = cur.lastrowid
# Holland has an address in dump_locations; Dominion does not.
cur.execute("INSERT INTO dump_locations (company_id,name,address,city,state,zip_code,active,created_at) VALUES (?,?,?,?,?,?,1,?)",
            (co,"Holland","100 Dump Rd","Suffolk","VA","23434",ts))
cur.execute("INSERT INTO routes (company_id,route_date,route_name,created_by,assigned_to,status,created_at) VALUES (?,?,?,?,?,'open',?)",
            (co,today,"R1",boss,drv,ts)); rid = cur.lastrowid
def stop(o, dump="", ret=""):
    cur.execute("""INSERT INTO stops (route_id,stop_order,customer_name,address,action,container_size,dump_location,return_destination,status,driver_status,created_at)
                   VALUES (?,?,?,?,?,?,?,?,?,?,?)""",
                (rid,o,"C%d"%o,"%d Main"%o,"Pull","20yd",dump,ret,"open","pending",ts)); return cur.lastrowid
s_holland = stop(1, "Holland", "Yard")
s_dominion = stop(2, "Dominion", "")
s_none = stop(3, "", "")
conn.commit(); conn.close()

# VERIFY: run migration twice → no error, no duplicate sites
app.init_db(); app.init_db()

conn = app.get_db()
def sites():
    return conn.execute("SELECT id,customer_name,kind,address FROM saved_addresses WHERE company_id=? AND kind IN ('dump','yard') ORDER BY customer_name",(co,)).fetchall()
names = [ (s["customer_name"] or "").lower() for s in sites() ]
ok(sorted(names) == ["dominion","holland","yard"], "migration created one record per distinct site (%s)" % names)
ok(len(names) == len(set(names)), "no duplicate sites after running migration twice")

# VERIFY: historical dump stop now has dump_site_id + still renders identically
holland_site = [s for s in sites() if (s["customer_name"] or "").lower()=="holland"][0]
row = conn.execute("SELECT dump_site_id, dump_location, return_site_id FROM stops WHERE id=?", (s_holland,)).fetchone()
ok(row["dump_site_id"] == holland_site["id"], "historical 'Holland' stop got dump_site_id")
ok((row["dump_location"] or "") == "Holland", "dump_location name string is kept populated (renders identically)")
ok(row["return_site_id"] is not None, "return site 'Yard' linked too")
# render-with-fallback helper: name identical to the string
disp_name, disp_addr = app._stop_dump_display(conn, conn.execute("SELECT * FROM stops WHERE id=?", (s_holland,)).fetchone())
ok(disp_name == "Holland", "FK-first display name equals the original string")
ok(disp_addr == "100 Dump Rd", "Holland address enriched from dump_locations, read via FK")
# Dominion has no address (allowed)
dom_site = [s for s in sites() if (s["customer_name"] or "").lower()=="dominion"][0]
ok(not (dom_site["address"] or "").strip(), "Dominion migrated with no address (allowed)")
conn.close()

# VERIFY: boss adds an address to Dominion in Settings → stop picks it up with NO re-parse
app.app.config["TESTING"] = True
cl = app.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=boss, company_id=co, role="boss", roles=["owner","dispatcher"], _csrf_token="tok")
r = cl.post("/address-book/%d/update" % dom_site["id"],
            data={"_csrf_token":"tok","action":"address","address":"55 Landfill Way","city":"Norfolk","state":"VA","zip":"23502"})
ok(r.status_code in (302,303), "boss address save redirects")
conn = app.get_db()
# The stop that links to Dominion now resolves to the new address WITHOUT touching the stop.
picked = conn.execute("""SELECT sa.address FROM stops s JOIN saved_addresses sa ON s.dump_site_id=sa.id WHERE s.id=?""",
                      (s_dominion,)).fetchone()
ok(picked and picked["address"] == "55 Landfill Way", "stop picks up the boss-entered address via FK, no re-parse")
_, addr2 = app._stop_dump_display(conn, conn.execute("SELECT * FROM stops WHERE id=?", (s_dominion,)).fetchone())
ok(addr2 == "55 Landfill Way", "FK-first helper returns the freshly-entered address")
conn.close()

# VERIFY: parse/dispatch a brand-new dump site → location created + stop links to it
with cl.session_transaction() as s:
    s.update(user_id=boss, company_id=co, role="boss", roles=["owner","dispatcher"], _csrf_token="tok")
payload = {"driver_id": drv, "stops": [
    {"action":"P","address":"9 Oak St","customer":"Bob","container_size":"30yd",
     "dump_leg":"BrandNew Transfer","return_leg":"","notes":"","confidence":"high","reviewed":True},
], "_csrf_token":"tok"}
r = cl.post("/api/dispatch", json=payload, headers={"X-CSRF-Token":"tok"})
ok(r.status_code == 200 and r.get_json().get("success"), "dispatch with a new dump site succeeds (%s)" % r.status_code)
conn = app.get_db()
newsite = conn.execute("SELECT id FROM saved_addresses WHERE company_id=? AND kind='dump' AND lower(customer_name)='brandnew transfer'",(co,)).fetchone()
ok(newsite is not None, "parsing a brand-new dump site created a location record")
linked = conn.execute("SELECT dump_site_id FROM stops WHERE dump_location='BrandNew Transfer'").fetchone()
ok(linked and linked["dump_site_id"] == newsite["id"], "the new stop links to the freshly created dump site")
conn.close()

# The boss editor page renders the dump/yard sites with a needs-address indicator.
html = cl.get("/yard-setup").get_data(as_text=True)
ok("Dump Sites &amp; Yards" in html and "site-locations" in html, "Settings shows the Dump Sites & Yards editor")
ok("needs address" in html, "a 'needs address' indicator is present for address-less sites")
ok("BrandNew Transfer" in html, "the new dump site is listed in the editor")

print("\nALL DUMP-SITE-LOCATION TESTS PASSED")
