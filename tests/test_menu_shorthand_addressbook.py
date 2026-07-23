import os, sys, tempfile, importlib
TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "m.db")
os.environ["SECRET_KEY"] = "m"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")

def ok(c, m):
    print(("PASS" if c else "FAIL") + " - " + m)
    if not c: raise SystemExit("FAILED: " + m)

# ---- item 3a: name cleaner unit -------------------------------------------
cn = app._clean_customer_name
ok(cn("Gc Com , Set 30 To The Side While You Do This")[0] == "Gc Com",
   "instruction-laden name → 'Gc Com'")
ok("set 30" in cn("Gc Com , Set 30 To The Side While You Do This")[1].lower(),
   "overflow captured for the note")
ok(cn("Serv Pro") == ("Serv Pro", ""), "clean name unchanged, no overflow")
ok(cn("recovery") == ("recovery", ""), "single-word name unchanged")
ok(len(cn("A B C D E F G H I J K L M N O P Q R S T U V")[0]) <= 40, "long name capped to ~40 chars")

# ---- setup -----------------------------------------------------------------
conn = app.get_db(); cur = conn.cursor()
cur.execute("""INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,trial_ends_at,created_at)
               VALUES (?,?,?,?,?,?,?)""",("MCo","mco","pro","active",10,None,app.now_ts())); co=cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("mboss","x","boss","B",co,app.now_ts())); boss=cur.lastrowid

# Simulate LEGACY data from before the dedupe index existed.
cur.execute("DROP INDEX IF EXISTS idx_parse_vocab_pair")
# item 2: seed duplicate shorthand rows (~14x hamp→Hampton) BEFORE re-init runs
for _ in range(14):
    cur.execute("INSERT INTO parse_vocab (company_id,term,expansion,kind,created_at) VALUES (?,?,?,'shorthand',?)",
                (co,"hamp","Hampton",app.now_ts()))
cur.execute("INSERT INTO parse_vocab (company_id,term,expansion,kind,created_at) VALUES (?,?,?,'shorthand',?)",
            (co,"HAMP","hampton",app.now_ts()))  # case variant of same mapping

# item 3: seed dup address-book rows (Recovery / recovery same address) + Serv Pro two sites + instruction name + no-name
def sa(name, addr, city, used):
    nk = app._normalize_addr(", ".join(p for p in [addr, city] if p))
    cur.execute("""INSERT INTO saved_addresses (company_id,customer_name,address,city,full_address,norm_key,
                   hidden,times_used,last_used_at,created_at) VALUES (?,?,?,?,?,?,0,?,?,?)""",
                (co,name,addr,city,(addr+", "+city),nk,used,app.now_ts(),app.now_ts()))
    return cur.lastrowid
sa("Recovery","6403 Granby St","Norfolk",3)
sa("recovery","6403 Granby St","Norfolk",5)
sa("Serv Pro","527 J Clyde Morris Blvd","Newport News",4)
sa("Serv Pro","100 Other Rd","Suffolk",2)          # legit 2nd site — must stay
sa("Gc Com , Set 30 To The Side While You Do This","111 Trash Ln","Norfolk",1)
sa("","2476 Bayview Ave","Norfolk",1)              # no-name
conn.commit(); conn.close()

# re-run init_db to fire the cleanup/merge migrations
app.init_db()

conn = app.get_db()
# item 2: shorthand deduped to one 'hamp' row for the company
hamp = conn.execute("SELECT COUNT(*) n FROM parse_vocab WHERE company_id=? AND LOWER(term)='hamp'",(co,)).fetchone()["n"]
ok(hamp == 1, "duplicate 'hamp' shorthand collapsed to a single row")
# item 3: Recovery/recovery merged; Serv Pro two sites intact
rec = conn.execute("SELECT COUNT(*) n, SUM(times_used) t FROM saved_addresses WHERE company_id=? AND norm_key=?",
                   (co, app._normalize_addr("6403 Granby St, Norfolk"))).fetchone()
ok(rec["n"] == 1, "Recovery + recovery merged to one row")
ok(rec["t"] == 8, "merged usage summed (3+5=8)")
serv = conn.execute("SELECT COUNT(*) n FROM saved_addresses WHERE company_id=? AND customer_name='Serv Pro'",(co,)).fetchone()["n"]
ok(serv == 2, "both Serv Pro sites intact (same name, different address NOT merged)")
gc = conn.execute("SELECT customer_name FROM saved_addresses WHERE company_id=? AND address='111 Trash Ln'",(co,)).fetchone()["customer_name"]
ok(gc == "Gc Com", "instruction-text name scrubbed to 'Gc Com'")
conn.close()

# ---- item 2: re-learning 'hamp' via the boss endpoint bumps, no new row ----
app.app.config["TESTING"]=True; cl=app.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=boss, role="boss", roles=["owner","dispatcher"], company_id=co, _csrf_token="tok")
cl.post("/parse-vocab/add", data={"_csrf_token":"tok","term":"hamp","expansion":"Hampton"})
conn=app.get_db()
row=conn.execute("SELECT COUNT(*) n, MAX(times_used) u FROM parse_vocab WHERE company_id=? AND LOWER(term)='hamp'",(co,)).fetchone()
conn.close()
ok(row["n"] == 1, "re-learning 'hamp' added no row (still one)")
ok((row["u"] or 0) >= 2, "re-learning bumped times_used")

# ---- item 1: More menu grouped sections in the exact order -----------------
html = cl.get("/", follow_redirects=True).get_data(as_text=True)
def pos(t): return html.find(t)
order = ["Team Hours","Team Time Off","🚛 Trucks","🔧 Vendors","🛠 Maintenance","👥 Team","🏗 Yard Setup","⚙ Settings","Logout"]
positions = [pos(t) for t in order]
ok(all(p != -1 for p in positions), "all More-menu items present")
ok(positions == sorted(positions), "More-menu items in the exact required order")
ok("topnav-more-head" in html and pos("Team") < pos("Fleet") < pos("Setup"),
   "three grouped section headers (Team, Fleet, Setup) render in order")
ok(pos(chr(34)+"topnav-more-sep"+chr(34)) < pos("⏻ Logout") and pos(chr(34)+"topnav-more-sep"+chr(34)) > pos("⚙ Settings"),
   "separator sits between Settings and Logout")

# ---- item 3c: no-name entry shows the street label -------------------------
ab = cl.get("/yard-setup").get_data(as_text=True)
ok("2476 Bayview Ave" in ab and "(no name)" not in ab,
   "no-name address book entry shows the street label, not '(no name)'")

print("\nALL MENU/SHORTHAND/ADDRESSBOOK TESTS PASSED")
