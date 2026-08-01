import os, sys, tempfile, importlib, json, types
TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "ocr.db")
os.environ["SECRET_KEY"] = "ocr"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
os.environ["ANTHROPIC_API_KEY"] = "test-key"
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# ---- Fake anthropic module so no network / real key is needed ----
fake = types.ModuleType("anthropic")
class _Resp:
    def __init__(self, text): self.content = [types.SimpleNamespace(type="text", text=text)]
class _Msgs:
    def create(self, **kw):
        mode = fake.MODE
        if mode == "raise":
            raise RuntimeError("simulated 500")
        return _Resp(fake.REPLY)
class Anthropic:
    def __init__(self, **kw): self.messages = _Msgs()
fake.Anthropic = Anthropic
fake.MODE = "ok"; fake.REPLY = "{}"
for name in ("APITimeoutError","APIConnectionError","RateLimitError","APIStatusError"):
    setattr(fake, name, type(name, (Exception,), {}))
sys.modules["anthropic"] = fake

app = importlib.import_module("app")

def ok(c, m):
    print(("PASS" if c else "FAIL") + " - " + m)
    if not c: raise SystemExit("FAILED: " + m)

app.init_db()
conn = app.get_db(); cur = conn.cursor(); ts = app.now_ts(); today = app.today_str()
cur.execute("INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,created_at) VALUES (?,?,?,?,?,?)",
            ("OcrCo","ocrco","pro","active",10,ts)); co = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,company_id,created_at) VALUES (?,?,?,?,?)",("o_boss","x","boss",co,ts)); boss=cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",("o_drv","x","driver","Dave",co,ts)); drv=cur.lastrowid
cur.execute("INSERT INTO routes (company_id,route_date,route_name,created_by,assigned_to,status,started_at,created_at) VALUES (?,?,?,?,?,'in_progress',?,?)",(co,today,"R",boss,drv,ts,ts)); rid=cur.lastrowid
def mkstop(o, dump="Dominion"):
    cur.execute("""INSERT INTO stops (route_id,stop_order,customer_name,address,action,container_size,dump_location,status,driver_status,active_leg,created_at)
       VALUES (?,?,?,?,?,?,?,?,?, 'primary', ?)""",(rid,o,"C%d"%o,"%d St"%o,"Pull","30yd",dump,"open","going_to_dump",ts)); return cur.lastrowid
s1=mkstop(1); s2=mkstop(2); s3=mkstop(3); s4=mkstop(4)
conn.commit(); conn.close()

app.app.config["TESTING"] = True
cl = app.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=drv, company_id=co, role="driver", _csrf_token="tok")

# a tiny but non-empty jpeg-ish payload; the fake model ignores content
IMG = b"\xff\xd8\xff\xe0" + b"scale-ticket-bytes" * 40
def post_ocr(stop_id, data=IMG, ctype="image/jpeg", fname="t.jpg"):
    return cl.post("/api/dump-ticket/ocr",
                   data={"_csrf_token":"tok","stop_id":str(stop_id),
                         "photo":(__import__("io").BytesIO(data), fname, ctype)},
                   content_type="multipart/form-data")
def ticket(stop_id): return app.get_db().execute("SELECT * FROM dump_tickets WHERE stop_id=?",(stop_id,)).fetchone()

# ---- unit: net sanity ----
f, c = app._normalize_ocr_ticket({"gross_lbs":42000,"tare_lbs":18000,"net_lbs":30000,"net_tons":12.0,
                                  "ticket_number":"A1","confidence":{"gross_lbs":"high","tare_lbs":"high","net_lbs":"high"}})
ok(c.get("net_lbs")=="low", "net that disagrees with gross-tare is flagged low")
f2, c2 = app._normalize_ocr_ticket({"gross_lbs":42000,"tare_lbs":18000,"net_lbs":24000,"confidence":{"net_lbs":"high"}})
ok(c2.get("net_lbs")=="high", "net that reconciles keeps its confidence")

# ---- 1) clear ticket → ok:true, fields prefilled, sanity checks ----
fake.MODE="ok"
fake.REPLY = json.dumps({"ticket_number":"T-5567","site_name":"Dominion","date":"2026-08-01",
    "gross_lbs":42000,"tare_lbs":18000,"net_lbs":24000,"net_tons":12.0,"fee_usd":86.50,"material":"C&D",
    "confidence":{"ticket_number":"high","gross_lbs":"high","tare_lbs":"high","net_tons":"high","fee_usd":"high"},
    "unreadable":False})
r = post_ocr(s1); j = r.get_json()
ok(r.status_code==200 and j.get("ok") and not j.get("unreadable"), "clear ticket → ok:true (%s)" % r.status_code)
ok(j["fields"]["ticket_number"]=="T-5567" and j["fields"]["net_tons"]==12.0 and j["fields"]["fee_usd"]==86.5,
   "clear ticket fields parsed (ticket#, net tons, fee)")
ok(ticket(s1)["photo_path"], "photo saved + attached to the dump ticket row")
ok(ticket(s1)["ai_prefilled"]==1, "row marked ai_prefilled")

# ---- 2) unreadable (photo of not-a-ticket) → ok:true unreadable, photo saved, no crash ----
fake.MODE="ok"; fake.REPLY = json.dumps({"ticket_number":None,"site_name":None,"gross_lbs":None,
    "net_tons":None,"fee_usd":None,"confidence":{},"unreadable":True})
r = post_ocr(s2); j = r.get_json()
ok(r.status_code==200 and j.get("ok") and j.get("unreadable"), "non-ticket → unreadable, still 200")
ok(ticket(s2)["photo_path"], "unreadable case still saved the photo")

# ---- 3) model 500 → ok:false, photo saved, no red error ----
fake.MODE="raise"
r = post_ocr(s3); j = r.get_json()
ok(r.status_code==200 and j.get("ok") is False and j.get("reason")=="error", "model 500 → 200 ok:false")
ok(ticket(s3)["photo_path"], "on model error the photo is still saved (image is the record)")

# ---- 4) bad JSON from model → ok:false parse, photo saved ----
fake.MODE="ok"; fake.REPLY = "here are your numbers: not json at all"
r = post_ocr(s4); j = r.get_json()
ok(j.get("ok") is False and j.get("reason")=="parse", "unparseable model output → ok:false parse")
ok(ticket(s4)["photo_path"], "parse-failure still saved the photo")

# ---- 5) markdown-fenced JSON is tolerated ----
fake.REPLY = "```json\n" + json.dumps({"ticket_number":"Z9","confidence":{"ticket_number":"medium"},"unreadable":False}) + "\n```"
r = post_ocr(s1); j = r.get_json()
ok(j.get("ok") and j["fields"]["ticket_number"]=="Z9", "fenced JSON stripped + parsed")

# ---- 6) daily cap guard ----
conn=app.get_db(); conn.execute("UPDATE companies SET ocr_daily_cap=1 WHERE id=?",(co,)); conn.commit(); conn.close()
# reset the limiter window rows for a clean count
conn=app.get_db(); conn.execute("DELETE FROM auth_rate_limits WHERE scope='dump_ticket_ocr'"); conn.commit(); conn.close()
fake.MODE="ok"; fake.REPLY = json.dumps({"ticket_number":"CAP1","confidence":{"ticket_number":"high"},"unreadable":False})
r1 = post_ocr(s1)
fake.MODE="raise"   # ensure a 2nd real call would be visible; cap should prevent it
r2 = post_ocr(s2); j2 = r2.get_json()
ok(r1.get_json().get("ok") is True, "under cap: first OCR call runs")
ok(j2.get("ok") is False and j2.get("reason")=="cap", "over daily cap → ok:false cap (no model call)")
ok(ticket(s2)["photo_path"], "over-cap case still saved the photo")

# ---- 7) no API key → ok:false, photo saved ----
conn=app.get_db(); conn.execute("UPDATE companies SET ocr_daily_cap=NULL WHERE id=?",(co,)); conn.commit(); conn.close()
_saved_key = os.environ.pop("ANTHROPIC_API_KEY", None)
r = post_ocr(s3); j = r.get_json()
ok(j.get("ok") is False and j.get("reason")=="no_ai", "no API key → ok:false no_ai")
ok(ticket(s3)["photo_path"], "no-key case still saved the photo")
os.environ["ANTHROPIC_API_KEY"]=_saved_key

# ---- 8) blank/too-large/bad-type guards ----
r = cl.post("/api/dump-ticket/ocr", data={"_csrf_token":"tok","stop_id":str(s1)}, content_type="multipart/form-data")
ok(r.get_json().get("ok") is False and r.get_json().get("reason")=="no_photo", "missing photo → ok:false no_photo")
r = post_ocr(s1, ctype="application/pdf", fname="x.pdf")
ok(r.status_code==415, "non image/* type rejected (415)")

# ---- 9) save POST persists fee/material + needs_review from ocr_queued ----
r = cl.post("/stop/%d/dump-ticket" % s1, data={"_csrf_token":"tok","dump_site":"Dominion","net_tons":"12",
    "ticket_number":"T-5567","fee_usd":"86.50","material":"C&D","ocr_queued":"1"})
row = ticket(s1)
ok(row["fee_usd"]==86.5 and (row["material"] or "")=="C&D", "save persists fee_usd + material")
ok(row["needs_review"]==1, "ocr_queued=1 marks the ticket needs_review")
# a normal confirmed save clears needs_review
cl.post("/stop/%d/dump-ticket" % s1, data={"_csrf_token":"tok","dump_site":"Dominion","net_tons":"12","ticket_number":"T-5567"})
ok(ticket(s1)["needs_review"]==0, "confirmed save (no ocr_queued) clears needs_review")

# ---- 10) the form renders the camera capture button + review line ----
html = cl.get("/stop/%d/dump-ticket" % s2).get_data(as_text=True)
ok('id="f-ocr-photo"' in html and 'capture="environment"' in html, "form has the camera-capture input")
ok('Photo of Ticket' in html and 'Check the numbers before saving' in html, "form has the button + review line")
ok('/api/dump-ticket/ocr' in html, "form wires the OCR endpoint")

print("\nALL TICKET-OCR TESTS PASSED")
