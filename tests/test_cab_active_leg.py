import os, sys, tempfile, importlib, urllib.parse
TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "leg.db")
os.environ["SECRET_KEY"] = "leg"
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
            ("LegCo","legco","pro","active",10,ts)); co = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,company_id,created_at) VALUES (?,?,?,?,?)",
            ("lg_boss","x","boss",co,ts)); boss = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("lg_drv","x","driver","Dave",co,ts)); drv = cur.lastrowid
# Promoted dump site WITH address (Dominion) and one WITHOUT (Blankville)
def site(name, addr=""):
    full = ", ".join(p for p in [addr, "Norfolk", "VA"] if p) if addr else ""
    cur.execute("""INSERT INTO saved_addresses (company_id,customer_name,address,city,state,full_address,kind,norm_key,hidden,times_used,last_used_at,created_at)
                   VALUES (?,?,?,?,?,?,?,?,0,1,?,?)""",
                (co,name,addr,"Norfolk" if addr else "","VA" if addr else "",full,"dump",
                 app._address_book_key(name,addr,"dump"),ts,ts)); return cur.lastrowid
dom = site("Dominion","55 Landfill Way")
blank = site("Blankville","")

cur.execute("INSERT INTO routes (company_id,route_date,route_name,created_by,assigned_to,status,started_at,created_at) VALUES (?,?,?,?,?,'in_progress',?,?)",
            (co,today,"R",boss,drv,ts,ts)); rid = cur.lastrowid
def stop(o, cust, addr, dump="", dump_id=None, ret="", ds="pending", status="open"):
    cur.execute("""INSERT INTO stops (route_id,stop_order,customer_name,address,city,state,action,container_size,
                   dump_location,dump_site_id,return_destination,status,driver_status,active_leg,created_at)
                   VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?, 'primary', ?)""",
                (rid,o,cust,addr,"Norfolk","VA","Pickup and Return","30yd",dump,dump_id,ret,status,ds,ts)); return cur.lastrowid
# PR stop with a dump leg (Dominion, has address) + return leg (yard-ish text)
s_pr   = stop(1, "Acme", "1 Job St", dump="Dominion", dump_id=dom, ret="")
# PR stop whose dump has no address (Blankville)
s_noad = stop(2, "Beta", "2 Work Rd", dump="Blankville", dump_id=blank)
# Single-leg plain stop
s_solo = stop(3, "Gamma", "3 Solo Ave")
conn.commit(); conn.close()

app.app.config["TESTING"] = True
cl = app.app.test_client()
def as_driver():
    with cl.session_transaction() as s:
        s.update(user_id=drv, company_id=co, role="driver", _csrf_token="tok")
as_driver()
def cab(): return cl.get("/driver/route/%d" % rid).get_data(as_text=True)

# ---- helper unit test ----
srow = dict(app.get_db().execute("SELECT * FROM stops WHERE id=?", (s_pr,)).fetchone())
legs, active = app._cab_stop_legs(srow, "1 Job St, Norfolk, VA",
                                  {dom: {"name":"Dominion","address":"55 Landfill Way, Norfolk, VA"}}, {})
ok([l["key"] for l in legs] == ["primary","dump"], "helper builds primary+dump legs (%s)" % [l["key"] for l in legs])
ok(active["key"] == "primary", "active defaults to primary")
ok(legs[1]["address"] == "55 Landfill Way, Norfolk, VA", "dump leg carries the site address")

# Single-leg helper → one leg only
solo = dict(app.get_db().execute("SELECT * FROM stops WHERE id=?", (s_solo,)).fetchone())
slegs, _ = app._cab_stop_legs(solo, "3 Solo Ave, Norfolk, VA", {}, {})
ok(len(slegs) == 1, "single-leg stop yields exactly one leg")

# ---- render: current stop is s_pr (first non-completed) ----
h = cab()
ok('id="cab-legs-switch"' in h, "multi-leg stop renders the leg switcher")
ok('data-leg="primary"' in h and 'data-leg="dump"' in h, "switcher has primary + dump chips")
ok('LEG 1 OF 2' in h, "header shows LEG 1 OF 2")
enc = urllib.parse.quote_plus("1 Job St Norfolk VA")
ok(("destination=" + enc) in h, "initial nav points at the customer (primary) address")
# the dump address is available to the client for instant switch (embedded in data-legs)
ok("55 Landfill Way" in h, "dump site address embedded for client-side leg switch")

# ---- switch to dump leg (persist) ----
r = cl.post("/stop/%d/active-leg" % s_pr, data={"_csrf_token":"tok","leg":"dump"}, headers={"X-Requested-With":"fetch"})
ok(r.status_code == 200 and r.get_json().get("ok"), "active-leg POST persists (%s)" % r.status_code)
val = app.get_db().execute("SELECT active_leg FROM stops WHERE id=?", (s_pr,)).fetchone()["active_leg"]
ok(val == "dump", "active_leg stored as dump")
# reload → server renders dump as active, nav now points at the dump address
h = cab()
enc_d = urllib.parse.quote_plus("55 Landfill Way Norfolk VA")
ok(("destination=" + enc_d) in h, "after switch, server-rendered nav points at the dump address")
ok('LEG 2 OF 2 &middot; DUMP' in h or 'LEG 2 OF 2' in h, "header reflects the dump leg")

# ---- reversible: switch back to primary ----
r = cl.post("/stop/%d/active-leg" % s_pr, data={"_csrf_token":"tok","leg":"primary"}, headers={"X-Requested-With":"fetch"})
ok(app.get_db().execute("SELECT active_leg FROM stops WHERE id=?", (s_pr,)).fetchone()["active_leg"] == "primary",
   "leg switch is reversible (back to primary)")

# ---- missing-address guard: s_noad's dump has no address ----
# make s_noad the current stop by completing s_pr
cl.post("/stop/%d/toggle" % s_pr, data={"_csrf_token":"tok"})
h = cab()   # now current stop is s_noad
ok('id="cab-legs-switch"' in h, "second PR stop also shows the switcher")
# switch it to dump and re-render
cl.post("/stop/%d/active-leg" % s_noad, data={"_csrf_token":"tok","leg":"dump"}, headers={"X-Requested-With":"fetch"})
h = cab()
ok('id="cab-noaddr"' in h and 'No address saved for' in h, "address-less dump leg shows the missing-address hint")
ok('cab-copy-btn' in h and 'disabled' in h, "copy button disabled when active leg has no address")

# ---- reset on complete: next stop opens on primary, not inherited 'dump' ----
# s_noad active_leg is 'dump'; complete it → current becomes s_solo (single-leg)
cl.post("/stop/%d/toggle" % s_noad, data={"_csrf_token":"tok"})
solo_leg = app.get_db().execute("SELECT active_leg FROM stops WHERE id=?", (s_solo,)).fetchone()["active_leg"]
ok(solo_leg == "primary", "next stop did NOT inherit 'dump' — opens on primary")
h = cab()
ok('id="cab-legs-switch"' not in h, "single-leg stop shows NO switcher (looks like today)")
ok('LEG ' not in h.split('cab-card')[1] if 'cab-card' in h else True, "single-leg stop shows no leg badge")

# ---- unknown leg value rejected ----
r = cl.post("/stop/%d/active-leg" % s_solo, data={"_csrf_token":"tok","leg":"bogus"}, headers={"X-Requested-With":"fetch"})
ok(r.status_code == 400, "unknown leg value rejected (400)")

print("\nALL CAB-ACTIVE-LEG TESTS PASSED")
