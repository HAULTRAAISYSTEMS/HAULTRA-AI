"""Parser must understand the boss's "addition" dispatch text and organize it into
a proper route:

    One addition today. Before final delivery
    Pr 980 meander rd,port, 757 restorstion 30yd dump dominion and then deliver garwood to end the day

Expected: NO bogus stop for the directive line; the PR stop gets
placement_note "Before final delivery"; "and then deliver garwood" becomes its
own Delivery stop resolved from the address book with notes "end of day";
the typo'd customer "757 restorstion" resolves to "757 Restoration"; the
comma-glued city "rd,port," still expands to Portsmouth.

Run:  ~/workspace/.haultra-venv/bin/python tests/test_parser_addition_text.py
"""
import os
import sys
import tempfile

TMPDIR = tempfile.mkdtemp(prefix="haultra-addtext-")
os.environ["DATABASE_PATH"] = os.path.join(TMPDIR, "addtext.db")
os.environ["SECRET_KEY"] = "testsecret123"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMPDIR, "uploads")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import app  # noqa: E402

FAILURES = []


def ok(cond, label):
    print(("PASS" if cond else "FAIL") + " - " + label, flush=True)
    if not cond:
        FAILURES.append(label)


# ── Seed ───────────────────────────────────────────────────────────────
app.init_db()
conn = app.get_db()
cur = conn.cursor()
ts = app.now_ts()
cur.execute(
    "INSERT INTO companies (name, slug, subscription_plan, subscription_status,"
    " max_drivers, created_at) VALUES (?,?,?,?,?,?)",
    ("Add Co", "addco", "pro", "active", 10, ts))
co = cur.lastrowid
for nm, ad, ct in [("Garwood", "1405 Garwood Ave", "Virginia Beach"),
                   ("757 Restoration", "980 Meander Rd", "Portsmouth"),
                   ("Napo", "1013 Paragon Way", "Suffolk")]:
    cur.execute(
        "INSERT INTO saved_addresses (company_id, customer_name, address, city,"
        " state, kind, times_used, created_at, last_used_at)"
        " VALUES (?,?,?,?,'VA','customer',5,?,?)",
        (co, nm, ad, ct, ts, ts))
conn.commit()


def parse(text):
    return app.parse_route_text(text, conn, co)


BOSS_TEXT = """One addition today. Before final delivery
Pr 980 meander rd,port, 757 restorstion 30yd dump dominion and then deliver garwood to end the day"""

# ── 1. The boss's text → exactly 2 stops ───────────────────────────────
stops = parse(BOSS_TEXT)
ok(len(stops) == 2, "boss text yields exactly 2 stops (got %d)" % len(stops))

s1, s2 = stops[0], stops[1]
ok(s1["action"] == "Pickup and Return", "stop 1 action is Pickup and Return")
ok(s1["address"].lower() == "980 meander rd", "stop 1 address is 980 meander rd")
ok(s1["city"] == "Portsmouth", "stop 1 comma-glued 'port' expands to Portsmouth")
ok(s1["customer_name"] == "757 Restoration",
   "stop 1 typo 'restorstion' resolves to saved '757 Restoration'")
ok(s1["container_size"] == "30yd", "stop 1 container 30yd")
ok(s1["dump_location"] == "Dominion", "stop 1 dump leg Dominion")
ok("dump" not in s1["customer_name"].lower() and "dump" not in s1["address"].lower(),
   "stop 1 has no leftover 'dump' word in name/address")
ok(s1["placement_note"].lower() == "before final delivery",
   "stop 1 carries placement note 'before final delivery'")
ok(s1["confidence_label"] == "high", "stop 1 is high confidence")

ok(s2["action"] == "Delivery", "'and then deliver garwood' is its own Delivery stop")
ok(s2["address"] == "1405 Garwood Ave", "stop 2 address resolved from saved 'Garwood'")
ok(s2["city"] == "Virginia Beach", "stop 2 city Virginia Beach")
ok("end of day" in (s2["notes"] or "").lower(),
   "stop 2 notes 'end of day' (optimize pins it last)")

# ── 2. Directive line alone → no bogus stop ────────────────────────────
stops = parse("One addition today. Before final delivery")
ok(len(stops) == 0, "directive-only line produces no stop")

# ── 3. 'and then return it to X' must NOT split (multi-leg rule) ───────
stops = parse("Pr 527 j clyde morris blvd,newpt, Serv pro 30yd dump holland and then return it to paragon")
ok(len(stops) == 1, "'and then return it to X' stays one stop (got %d)" % len(stops))
if stops:
    ok(stops[0]["dump_location"] == "Holland", "dump leg Holland kept")
    ok(stops[0].get("return_destination") == "paragon" or "paragon" in (stops[0].get("notes") or "").lower(),
       "return-to-paragon captured, not split into a stop")

# ── 4. Normal "Customer, 123 Street" CSV order still works ─────────────
stops = parse("Serv Pro, 527 J Clyde Morris Blvd, Newport News")
ok(len(stops) == 1, "normal CSV line yields 1 stop")
if stops:
    ok(stops[0]["customer_name"] == "Serv Pro", "normal CSV customer first")
    ok("527" in stops[0]["address"], "normal CSV address second")

# ── 5. Comma-glued city without spaces ─────────────────────────────────
stops = parse("Pr 7021 harbor view blvd,suff,Ew 40yd dump holland")
ok(len(stops) == 1, "comma-glued line yields 1 stop")
if stops:
    ok(stops[0]["city"] == "Suffolk", "comma-glued 'suff' expands to Suffolk")
    ok(stops[0]["customer_name"] == "Ew", "customer parsed after comma-glued city")

# ── 6. Fuzzy match must not false-positive on short names ──────────────
stops = parse("Pr 1013 paragon way,suff, Napo 30yd dump holland")
ok(len(stops) == 1, "short-name line yields 1 stop")
if stops:
    ok(stops[0]["customer_name"] == "Napo", "short name 'Napo' not fuzzy-rewritten")

# ── 7. EOD suffix variants ─────────────────────────────────────────────
stops = parse("Deliver 1405 garwood ave end of day")
ok(len(stops) == 1 and "end of day" in (stops[0]["notes"] or "").lower(),
   "'end of day' suffix lands in notes")

conn.close()
print()
if FAILURES:
    print("FAILURES: %d" % len(FAILURES))
    sys.exit(1)
print("all addition-text checks passed")
