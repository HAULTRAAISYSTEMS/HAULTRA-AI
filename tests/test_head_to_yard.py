""""head to yard once returned" moves the TRUCK, not the can (fix/head-to-yard-not-return-leg).

Reported from the cab 2026-11-16, off this dispatch text:

    Pr 520 kings borough sq,ches, velocity 30yd dump dominion and head to
    yard once returned

parsed as PR Velocity -> Dump: Dominion -> **Return: 2545 Squadron Ct** (the
yard).

    "the ai parser takes it as I'm returning the container to the yard but
     that's not what he's saying"

He is right, and the cost is the customer's. A PR returns the SAME can to the
customer it was pulled from; that is what the second R stands for. Sending the
return leg to the yard turns the job into a pull and leaves Velocity standing
there with no container — a service failure the board would show as a clean
green stop.

The two sentences differ by their verb and their subject:

    "return it to the yard"        -> the CAN goes to the yard   (return_leg)
    "head to yard once returned"   -> the TRUCK goes to the yard (end of day)

and "once returned" is itself the tell: the return has ALREADY happened, to
the customer, before the driver heads anywhere.

The prompt's existing line — '"return it to the yard to end the day" (no named
place) also stays a return_leg' — is correct and must keep working. This file
pins both readings so neither fix eats the other.
"""
import os, sys, tempfile, importlib
TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "h2y.db")
os.environ["SECRET_KEY"] = "h2y"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")

def ok(c, m):
    print(("PASS" if c else "FAIL") + " - " + m)
    if not c:
        raise SystemExit("FAILED: " + m)

app.init_db()
conn = app.get_db(); cur = conn.cursor(); ts = app.now_ts()
cur.execute("""INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,
               yard_address,yard_city,created_at) VALUES (?,?,?,?,?,?,?,?)""",
            ("YardCo", "yardco2", "pro", "active", 10, "2545 Squadron Ct", "Virginia Beach", ts))
co = cur.lastrowid
cur.execute("""INSERT INTO saved_addresses (company_id,customer_name,address,full_address,kind,
               norm_key,hidden,times_used,last_used_at,created_at)
               VALUES (?,?,?,?,?,?,0,1,?,?)""",
            (co, "Yard", "2545 Squadron Ct", "2545 Squadron Ct, Virginia Beach", "yard",
             app._address_book_key("Yard", "2545 Squadron Ct", "yard"), ts, ts))
conn.commit(); conn.close()


# ── 1. the phrase test itself ──────────────────────────────────────────────
# Driver movement: the truck goes to the yard.
for _t in ["and head to yard once returned",
           "head back to the yard once returned",
           "then head to the yard",
           "go back to the yard after",
           "dump dominion and head to yard when returned",
           "drive back to the yard once it's returned"]:
    ok(app._is_driver_move_to_yard(_t),
       "driver movement: %r" % _t)

# Can movement: the container goes to the yard. These must NOT match, or the
# 2026-10-24 Alix rule breaks and empties stop going back to the yard.
for _t in ["return it to the yard to end the day",
           "take it back to the yard",
           "bring the can back to the yard",
           "dump dominion then return it to the yard",
           "drop the empty at the yard"]:
    ok(not app._is_driver_move_to_yard(_t),
       "can movement, left alone: %r" % _t)

ok(not app._is_driver_move_to_yard(""), "empty text is not driver movement")


# ── 2. the guard on the parsed stop ────────────────────────────────────────
_raw = "Pr 520 kings borough sq,ches, velocity 30yd dump dominion and head to yard once returned"
_stops = [{
    "action": "PR", "address": "520 Kingsborough Sq, Chesapeake", "customer": "Velocity",
    "container_size": "30yd", "dump_leg": "Dominion",
    "return_leg": "2545 Squadron Ct, Virginia Beach",
    "notes": "", "raw": _raw, "confidence": "high",
}]
_out = app._ensure_head_to_yard_not_return(_stops, co)
ok(len(_out) == 1, "the guard keeps the stop — it never drops work")
ok((_out[0].get("return_leg") or "") == "",
   "the return leg to the yard is removed — the can goes back to VELOCITY, "
   "which is what the second R in PR means (the reported bug)")
ok((_out[0].get("dump_leg") or "") == "Dominion",
   "the dump leg is untouched — Dominion is still where it gets emptied")
ok(_out[0]["action"] == "PR", "and it is still a PR")
ok("yard" in (_out[0].get("notes") or "").lower(),
   "the instruction survives in the notes — the driver still needs to know "
   "where he is going when he is done")
ok("end of day" in (_out[0].get("notes") or "").lower(),
   "marked end of day, which is what heading to the yard after the last "
   "return actually is")

# The legitimate return-to-yard is untouched.
_keep = [{
    "action": "PR", "address": "520 Kingsborough Sq, Chesapeake", "customer": "Velocity",
    "container_size": "30yd", "dump_leg": "Dominion",
    "return_leg": "2545 Squadron Ct, Virginia Beach",
    "notes": "", "raw": "Pr 520 kings borough sq dump dominion then return it to the yard",
}]
_kept = app._ensure_head_to_yard_not_return(_keep, co)
ok(_kept[0].get("return_leg") == "2545 Squadron Ct, Virginia Beach",
   "'return it to the yard' KEEPS its return leg — that one really does send "
   "the can to the yard, and the Alix rule from 2026-10-24 depends on it")

# A return leg to a real customer address is never touched, whatever the text.
_cust = [{
    "action": "PR", "address": "520 Kingsborough Sq, Chesapeake", "customer": "Velocity",
    "dump_leg": "Dominion", "return_leg": "11496 Shiloh Dr, Virginia Beach",
    "notes": "", "raw": "pr 520 kings borough dump dominion return to shiloh then head to yard",
}]
ok(app._ensure_head_to_yard_not_return(_cust, co)[0]["return_leg"]
   == "11496 Shiloh Dr, Virginia Beach",
   "a return leg to a CUSTOMER address is left alone even when the text also "
   "says head to the yard — only a yard return leg is suspect")

# A Delivery has no return leg to confuse; nothing should change.
_del = [{"action": "D", "address": "806 Curtis Saunders Rd, Chesapeake",
         "customer": "Heartland", "return_leg": "", "notes": "ask onsite for placement",
         "raw": "Del 806 Curtis Saunders rd,ches, heartland 30yd ask onsite for placement"}]
_dout = app._ensure_head_to_yard_not_return(_del, co)
ok((_dout[0].get("return_leg") or "") == "" and _dout[0]["action"] == "D",
   "the Delivery on the same dispatch is untouched")


# ── 3. the prompt teaches it too ───────────────────────────────────────────
c = app.get_db()
prompt = app._build_parse_system_prompt(c, co)
c.close()
ok("head to" in prompt.lower(),
   "the prompt names the 'head to the yard' wording")
ok("once returned" in prompt.lower(),
   "and 'once returned', which is the tell that the can is already back with "
   "the customer")
ok("return it to the yard to end the day" in prompt,
   "while the existing can-goes-to-the-yard rule is still taught — the two "
   "readings have to coexist")

print("ALL HEAD-TO-YARD TESTS PASSED")
