"""A shop errand written in dispatch text becomes a real SHOP leg.

2026-11-03, straight off the route. The boss texted

    Can 2058 stop at Gregory's to get the cable looked at

it came through the parser, and the entire errand survived only as prose in
the stop note. The driver read the note and re-entered the shop by hand. Same
shape as lot numbers and can numbers sitting in a customer name: a real thing
living in a field that cannot act on it.

The trigger is a vendor the boss ALREADY HAS ON FILE -- the same move that
settled can-vs-lot, which is to ask the data the app already holds rather than
invent a heuristic. A name only reaches the vendors table because somebody
put it there.

The dangerous half is the false positive. "dump at United" appears on half
the stops in this system, and United is on the vendor list as well as being a
dump site. Detecting a shop visit there would hang a bogus errand on most of
a day's work -- worse than not having the feature. That case, and the rest of
the ways this could fire wrongly, are most of what is below.

Run:  python3 tests/test_parsed_shop_instruction.py
"""
import os
import sys
import tempfile
import importlib

TMP = tempfile.mkdtemp(prefix="haultra-parseshop-")
os.environ["DATABASE_PATH"] = os.path.join(TMP, "ps.db")
os.environ["SECRET_KEY"] = "ps"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")

FAILURES = []


def ok(cond, label):
    print(("PASS" if cond else "FAIL") + " - " + label, flush=True)
    if not cond:
        FAILURES.append(label)


VENDORS = [(1, "Gregory's"), (2, "Maypaw Diesel"), (3, "Bay"), (4, "United")]

# ── 1. The reported text ───────────────────────────────────────────
print("\n-- the boss's actual words --")
hit = app.detect_shop_instruction(
    "Can 2058 stop at Gregory's to get the cable looked at", VENDORS)
ok(hit is not None, "an errand is found")
ok(hit and hit["vendor_name"] == "Gregory's", "it is Gregory's (got %r)"
   % (hit.get("vendor_name") if hit else None))
ok(hit and hit["reason"] == "get the cable looked at",
   "the reason reads cleanly, no leading 'to' (got %r)" % (hit.get("reason") if hit else None))
ok(hit and hit["position"] == "after_dump", "and defaults to after the dump")

print("\n-- other ways he writes it --")
for text, want_reason in [
    ("swing by Gregorys and have them shorten the cable", "shorten the cable"),
    ("go by Gregory's", ""),
    ("take it to Maypaw Diesel for a hydraulic line", "for a hydraulic line"),
]:
    h = app.detect_shop_instruction(text, VENDORS)
    ok(h is not None, "%r is read as an errand" % text)
    ok(h and h["reason"] == want_reason,
       "   reason %r (got %r)" % (want_reason, h.get("reason") if h else None))

# An apostrophe typed or not typed must not matter.
ok(app.detect_shop_instruction("stop at Gregorys", VENDORS) is not None,
   "'Gregorys' without the apostrophe still matches")

print("\n-- when he says where it goes --")
h = app.detect_shop_instruction("stop at Gregory's before you dump to fix the cable", VENDORS)
ok(h and h["position"] == "before_dump",
   "'before you dump' puts the shop first (got %r)" % (h.get("position") if h else None))
h = app.detect_shop_instruction("on the way to the dump swing by Gregory's", VENDORS)
ok(h and h["position"] == "before_dump", "so does 'on the way to the dump'")

# ── 2. THE FALSE POSITIVES ─────────────────────────────────────────
# This is the half that decides whether the feature is worth having.
print("\n-- what must NOT be read as an errand --")
must_not = [
    ("dump at United", "the dump site is not an errand -- this is on half the stops"),
    ("dumping at Bay", "same, with a short name"),
    ("dumped at United then home", "past tense, still the dump"),
    ("left it in the bay area", "a short vendor name inside an ordinary word"),
    ("20yd pull", "no vendor at all"),
    ("", "empty text"),
    ("call the office", "a name that is on no vendor list"),
]
for text, why in must_not:
    ok(app.detect_shop_instruction(text, VENDORS) is None,
       "%r -> nothing (%s)" % (text, why))

ok(app.detect_shop_instruction("stop at Gregory's", []) is None,
   "with no vendors on file, nothing is ever detected")

# A short name needs an errand verb; a long one does not.
ok(app.detect_shop_instruction("go by Bay for parts", VENDORS) is not None,
   "'go by Bay' matches -- the verb carries the short name")
ok(app.detect_shop_instruction("parked in the Bay lot", VENDORS) is None,
   "'the Bay lot' does not -- no verb, name too short to stand alone")

# The longest match wins, so a more specific vendor is not shadowed.
LONGER = VENDORS + [(5, "Gregory's Truck Service")]
h = app.detect_shop_instruction("stop at Gregory's Truck Service for a weld", LONGER)
ok(h and h["vendor_name"] == "Gregory's Truck Service",
   "the longest matching vendor name wins (got %r)" % (h.get("vendor_name") if h else None))

# A name already doing a job on this stop is not an errand.
ok(app.detect_shop_instruction("stop at United", VENDORS, skip_names=["United"]) is None,
   "a vendor that is THIS stop's dump site is skipped")

# ── 3. End to end through /api/dispatch ────────────────────────────
print("\n-- dispatching the boss's text --")
app.init_db()
conn = app.get_db()
cur = conn.cursor()
ts = app.now_ts()
cur.execute("INSERT INTO companies (name, slug, subscription_plan, subscription_status,"
            " max_drivers, created_at) VALUES (?,?,?,?,?,?)",
            ("Parse Co", "parseco", "pro", "active", 10, ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id,"
            " is_active, created_at) VALUES (?,?,?,?,?,1,?)",
            ("p_boss", "x", "boss", "P Boss", co, ts))
boss = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id,"
            " is_active, created_at) VALUES (?,?,?,?,?,1,?)",
            ("p_drv", "x", "driver", "P Driver", co, ts))
drv = cur.lastrowid
for nm, ad in (("Gregory's", "5812 Curlew Dr, Norfolk VA"), ("United", "1 Landfill Rd")):
    cur.execute("INSERT INTO vendors (company_id, name, address, is_active, created_at)"
                " VALUES (?,?,?,1,?)", (co, nm, ad, ts))
conn.commit()
conn.close()

app.app.config["TESTING"] = True
cl = app.app.test_client()
with cl.session_transaction() as s:
    s.update(user_id=boss, company_id=co, role="boss",
             roles=["boss", "owner", "dispatcher"], _csrf_token="tok")
HJ = {"X-CSRF-Token": "tok"}

r = cl.post("/api/dispatch", json={"driver_id": drv, "route_date": "2026-11-20", "stops": [
    {"action": "PR", "address": "440 Mariners Way", "customer": "PRO-MIT",
     "container_size": "20yd", "dump_leg": "United",
     "notes": "Can 2058 stop at Gregory's to get the cable looked at"},
    {"action": "P", "address": "9 Plain St", "customer": "Someone Else",
     "container_size": "20yd", "dump_leg": "United", "notes": "dump at United"},
]}, headers=HJ)
ok(r.status_code == 200, "dispatch accepted (got %d)" % r.status_code)

c = app.get_db()
rid = c.execute("SELECT id FROM routes WHERE company_id=? ORDER BY id DESC LIMIT 1",
                (co,)).fetchone()["id"]
rows = [dict(x) for x in c.execute(
    "SELECT customer_name, notes, shop_leg, shop_addr, shop_can, shop_note, shop_source,"
    " shop_leg_pos FROM stops WHERE route_id=? ORDER BY stop_order", (rid,)).fetchall()]
c.close()

ok(len(rows) == 2, "both stops persisted (got %d)" % len(rows))
_pm = rows[0]
ok((_pm["shop_leg"] or "") == "Gregory's",
   "the PRO-MIT stop got a SHOP leg for Gregory's (got %r)" % _pm["shop_leg"])
ok("Curlew" in (_pm["shop_addr"] or ""),
   "with the vendor's address, so Navigate works (got %r)" % _pm["shop_addr"])
ok((_pm["shop_note"] or "") == "get the cable looked at",
   "the reason is on the LEG (got %r)" % _pm["shop_note"])
ok((_pm["shop_source"] or "") == "parsed",
   "marked as read from dispatch text (got %r)" % _pm["shop_source"])
ok((_pm["shop_can"] or "") == "2058",
   "and the can named in the text rides along (got %r)" % _pm["shop_can"])

# The note is the boss's words, untouched -- and the reason is NOT repeated
# into it, which is what made the cab print the same thing twice.
ok("Gregory" in (_pm["notes"] or ""), "the boss's note is left as he wrote it")
ok("Shop:" not in (_pm["notes"] or ""),
   "the reason is not appended to the note as well (got %r)" % _pm["notes"])

_other = rows[1]
ok(not (_other["shop_leg"] or ""),
   "'dump at United' got NO shop leg (got %r)" % _other["shop_leg"])

# ── 4. It renders, and says where it came from ─────────────────────
print("\n-- the cab --")
# The cab shows the stop card once the route is running.
c = app.get_db()
c.execute("UPDATE routes SET status='in_progress' WHERE id=?", (rid,))
c.execute("UPDATE stops SET driver_status='arrived' WHERE route_id=? AND stop_order=1", (rid,))
c.commit()
c.close()
with cl.session_transaction() as s:
    s.update(user_id=drv, company_id=co, role="driver", roles=["driver"],
             _csrf_token="tok")
html = cl.get("/driver/route/%d" % rid).get_data(as_text=True)
ok("SHOP" in html, "a SHOP chip renders")
ok("Gregory" in html, "naming the shop")
ok("LEG 1 OF 3" in html,
   "primary + dump + shop = 3 legs (no return leg on this stop)")

# While the SHOP leg is the active one, the cab says what it is for and that
# the app read it out of the dispatch text rather than someone typing it.
# Teal is reserved for AI-parsed content, so the marker uses it.
c = app.get_db()
c.execute("UPDATE stops SET active_leg='shop' WHERE route_id=? AND stop_order=1", (rid,))
c.commit()
c.close()
html2 = cl.get("/driver/route/%d" % rid).get_data(as_text=True)
ok("FROM DISPATCH" in html2,
   "the shop leg is marked as read from the boss's text")
ok("get the cable looked at" in html2,
   "and says what the shop is for")
ok("var(--teal)" in html2.split("FROM DISPATCH")[0][-400:],
   "in teal, the colour reserved for AI-parsed content")

# ── 5. A hand-added leg is never overwritten by the parser ─────────
print("\n-- a driver's own choice wins --")
c = app.get_db()
sid = c.execute("SELECT id FROM stops WHERE route_id=? ORDER BY stop_order LIMIT 1",
                (rid,)).fetchone()["id"]
c.execute("UPDATE stops SET shop_leg='Maypaw Diesel', shop_source='driver' WHERE id=?", (sid,))
c.commit()
_row = c.execute("SELECT * FROM stops WHERE id=?", (sid,)).fetchone()
_res = app.apply_parsed_shop_leg(c, co, sid, "stop at Gregory's to fix the cable", _row)
_after = dict(c.execute("SELECT shop_leg, shop_source FROM stops WHERE id=?", (sid,)).fetchone())
c.close()
ok(_res == "", "the parser declines a stop that already has a shop leg")
ok(_after["shop_leg"] == "Maypaw Diesel" and _after["shop_source"] == "driver",
   "the driver's own shop stop is left exactly as he set it (got %r)" % (_after,))

print("\n%d failure(s)" % len(FAILURES))
for f in FAILURES:
    print("  FAILED: " + f)
sys.exit(1 if FAILURES else 0)
