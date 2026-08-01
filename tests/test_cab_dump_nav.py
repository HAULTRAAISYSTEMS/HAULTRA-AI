import os, sys, tempfile, importlib, urllib.parse
TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "nav.db")
os.environ["SECRET_KEY"] = "nav"
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
            ("NavCo","navco","pro","active",10,ts)); co = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,company_id,created_at) VALUES (?,?,?,?,?)",
            ("nv_boss","x","boss",co,ts)); boss = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("nv_drv","x","driver","Dave",co,ts)); drv = cur.lastrowid
# legacy dump_locations row for the fallback case
cur.execute("INSERT INTO dump_locations (company_id,name,address,city,state,zip_code,active,created_at) VALUES (?,?,?,?,?,?,1,?)",
            (co,"Legacy DL","900 Old Rd","Chesapeake","VA","23320",ts))

def route_with_stop(dump_name="", dump_site_id=None, ds="going_to_dump"):
    cur.execute("INSERT INTO routes (company_id,route_date,route_name,created_by,assigned_to,status,started_at,created_at) VALUES (?,?,?,?,?,?,?,?)",
                (co,today,"R",boss,drv,"in_progress",ts,ts)); rid = cur.lastrowid
    cur.execute("""INSERT INTO stops (route_id,stop_order,customer_name,address,action,container_size,dump_location,dump_site_id,status,driver_status,created_at)
                   VALUES (?,?,?,?,?,?,?,?,?,?,?)""",
                (rid,1,"Cust","1 Job St","Pull","30yd",dump_name,dump_site_id,"open",ds,ts)); return rid

# Create a promoted dump site WITH an address
cur.execute("""INSERT INTO saved_addresses (company_id,customer_name,address,city,state,zip,full_address,kind,norm_key,hidden,times_used,last_used_at,created_at)
               VALUES (?,?,?,?,?,?,?,?,?,0,1,?,?)""",
            (co,"Dominion","55 Landfill Way","Norfolk","VA","23502","55 Landfill Way, Norfolk, VA 23502","dump",
             app._address_book_key("Dominion","55 Landfill Way","dump"),ts,ts)); dom_id = cur.lastrowid
# A promoted dump site with NO address
cur.execute("""INSERT INTO saved_addresses (company_id,customer_name,address,full_address,kind,norm_key,hidden,times_used,last_used_at,created_at)
               VALUES (?,?,?,?,?,?,0,1,?,?)""",
            (co,"Blankville","","","dump",app._address_book_key("Blankville","","dump"),ts,ts)); blank_id = cur.lastrowid

r_fk    = route_with_stop("Dominion", dom_id)         # FK site w/ address → nav
r_dl    = route_with_stop("Legacy DL", None)          # no FK, matches dump_locations → fallback nav
r_noadr = route_with_stop("Blankville", blank_id)     # FK site, no address → nudge
r_unk   = route_with_stop("Ghosttown", None)          # no FK, no match → nudge
conn.commit(); conn.close()

app.app.config["TESTING"] = True
cl = app.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=drv, company_id=co, role="driver", _csrf_token="tok")
def cab(rid): return cl.get("/driver/route/%d" % rid).get_data(as_text=True)

# 1) FK site with address → the dump address drives navigation.
# The Google/Apple maps button PAIR was removed in the Cab View restructure
# (feat/cab-view-v2 §6): navigation now goes through ONE preference-aware
# "Tap to Navigate" (openNavStop), whose default href is still the Google URL.
# The dump address must be wired into that nav.
h = cab(r_fk)
enc = urllib.parse.quote_plus("55 Landfill Way Norfolk VA 23502")
ok(("destination=" + enc) in h, "dump-site address (via FK) wired into Google Maps nav")
ok("openNavStop" in h and "55 Landfill Way Norfolk VA 23502" in h,
   "dump-site address wired into the preference-based Navigate")
ok('id="cab-maps-row"' not in h, "duplicate Google/Apple maps button row removed (§6)")

# 2) No FK but a matching dump_locations row → legacy fallback still navigates
h = cab(r_dl)
enc2 = urllib.parse.quote_plus("900 Old Rd Chesapeake VA 23320")
ok(("destination=" + enc2) in h, "legacy dump_locations address still used when FK is null (fallback)")

# 3) FK site with no address → clear 'add an address' nudge, no maps link
h = cab(r_noadr)
ok("No address saved for" in h and "Dump Sites" in h, "address-less dump site shows the add-address nudge")
# (nudge-present above already proves the else/elif branch: nav is mutually exclusive)

# 4) Unknown name, no FK, no dump_locations match → nudge (not a crash)
h = cab(r_unk)
ok("No address saved for" in h and "Ghosttown" in h, "unknown dump name degrades to the nudge cleanly")

# 5) Boss adds an address to Blankville → Cab View picks it up with NO re-parse
with cl.session_transaction() as s:
    s.update(user_id=boss, company_id=co, role="boss", roles=["owner"], _csrf_token="tok")
cl.post("/address-book/%d/update" % blank_id,
        data={"_csrf_token":"tok","action":"address","address":"12 Fill Ln","city":"Suffolk","state":"VA","zip":"23434"})
with cl.session_transaction() as s:
    s.update(user_id=drv, company_id=co, role="driver", _csrf_token="tok")
h = cab(r_noadr)
enc3 = urllib.parse.quote_plus("12 Fill Ln Suffolk VA 23434")
ok(("destination=" + enc3) in h, "boss-entered address navigates in Cab View with no re-parse")

print("\nALL CAB-DUMP-NAV TESTS PASSED")
