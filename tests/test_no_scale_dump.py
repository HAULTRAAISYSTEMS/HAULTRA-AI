"""Save a dump ticket with what you actually know (feat/no-scale-dump-sites).

Reported from the cab 2026-11-18, stopped at a concrete yard:

    "I dont think that the enter ticket section should not make you have to put
     in the ticket number before you move on .. some landfills don't give out
     tickets but I still put in the container number and time I'm here and
     leave.. I think I should be able to put in the info I know and hit save
     ticket instead of skip ticket after I put in the info."

He had the dump site, can 2036, in at 9:22 and out at 9:37 — and the form
refused him: "Enter net tons (or fill scale-in and scale-out to auto-calculate
it)." His only way past was "Skip — Continue Without Ticket", which is the
wrong word for a dump that really happened.

The server never required net tons at ALL, and already knew which sites issue
tickets. The browser was the strictest thing in the stack, and stricter than
the world.

Why the site has no scale, which is the part that decides the billing: clean
concrete is not waste to a recycler, it is feedstock — they crush it into
saleable base rock. Those yards charge a flat per-load fee or nothing and
never weigh a truck. So `tons x rate` is the wrong MODEL for such a site, not
a missing number, and a tonless dump priced that way silently bills $0.
"""
import os, sys, tempfile, importlib
TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "noscale.db")
os.environ["SECRET_KEY"] = "noscale"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")

def ok(c, m):
    print(("PASS" if c else "FAIL") + " - " + m)
    if not c:
        raise SystemExit("FAILED: " + m)

import datetime as _dt
_TODAY = app.now_ts()[:10]
def _day(n):
    return (_dt.date.fromisoformat(_TODAY) + _dt.timedelta(days=n)).isoformat()

app.init_db()
conn = app.get_db(); cur = conn.cursor(); ts = app.now_ts()
cur.execute("""INSERT INTO companies (name,slug,subscription_plan,subscription_status,max_drivers,
               created_at) VALUES (?,?,?,?,?,?)""",
            ("ConcreteCo", "concreteco", "pro", "active", 10, ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("c_boss", "x", "boss", "Boss", co, ts)); boss = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("c_drv", "x", "driver", "Tim Hendrix", co, ts)); drv = cur.lastrowid
# Branscome: a real dump site record, still on the default per-ton pricing.
cur.execute("""INSERT INTO saved_addresses (company_id,customer_name,address,full_address,kind,
               norm_key,hidden,times_used,last_used_at,created_at,issues_tickets)
               VALUES (?,?,?,?,?,?,0,1,?,?,1)""",
            (co, "Branscome", "5225 Learning Cir", "5225 Learning Cir, Virginia Beach", "dump",
             app._address_book_key("Branscome", "5225 Learning Cir", "dump"), ts, ts))
site_id = cur.lastrowid
# A disposal rate IS configured — so a tonless dump really does lose money.
cur.execute("INSERT INTO rate_cards (company_id, service, tier, cents) VALUES (?,?,?,?)",
            (co, "disposal", "*", 5500))
cur.execute("INSERT INTO rate_cards (company_id, service, tier, cents) VALUES (?,?,?,?)",
            (co, "pull", "standard", 40000))
conn.commit(); conn.close()

app.app.config["TESTING"] = True
cl = app.app.test_client()
HJ = {"X-CSRF-Token": "tok"}
def as_boss():
    with cl.session_transaction() as s:
        s.update(user_id=boss, company_id=co, role="boss", roles=["owner", "dispatcher"], _csrf_token="tok")
def as_driver():
    with cl.session_transaction() as s:
        s.update(user_id=drv, company_id=co, role="driver", roles=["driver"], _csrf_token="tok")

as_boss()
r = cl.post("/api/dispatch", json={"driver_id": drv, "route_date": _TODAY, "stops": [
    {"action": "P", "address": "5225 Learning Cir, Virginia Beach", "customer": "Sussex",
     "container_size": "30yd", "dump_leg": "Branscome"},
]}, headers=HJ)
ok(r.status_code == 200, "a pull with a Branscome dump leg dispatches — status %s" % r.status_code)
c = app.get_db()
rid = c.execute("SELECT id FROM routes WHERE company_id=?", (co,)).fetchone()["id"]
sid = c.execute("SELECT id FROM stops WHERE route_id=?", (rid,)).fetchone()["id"]
c.execute("UPDATE stops SET dump_site_id=?, driver_status='going_to_dump' WHERE id=?",
          (site_id, sid))
c.commit(); c.close()


# ── 1. the pricing model ───────────────────────────────────────────────────
_rc = {("disposal", "*"): 5500}
ok(app._stop_disposal_cents(_rc, "Pull", 6.0) == 33000,
   "per_ton is untouched: 6 tons at $55 is $330 — no existing company's "
   "invoice moves because of this change")
ok(app._stop_disposal_cents(_rc, "Pull", 0) == 0,
   "per_ton with no weight is still $0 — that is the silence being fixed, "
   "not by inventing a number but by letting the site say it has no scale")
ok(app._stop_disposal_cents(_rc, "Pull", 0, "flat", 7500) == 7500,
   "flat charges per LOAD — $75 whether or not anyone weighed the truck")
ok(app._stop_disposal_cents(_rc, "Pull", 6.0, "flat", 7500) == 7500,
   "and flat ignores weight even when a weight happens to exist")
ok(app._stop_disposal_cents(_rc, "Pull", 6.0, "free", 0) == 0,
   "free is free — clean concrete is feedstock, plenty of yards take it for "
   "nothing")
ok(app._stop_disposal_cents(_rc, "Delivery", 6.0, "flat", 7500) == 0,
   "a Delivery never disposes of anything, whatever the site charges")
ok(app._stop_disposal_cents(_rc, "Pull", 0, "nonsense", 9999) == 0,
   "an unknown mode falls back to per_ton rather than inventing a charge")


# ── 2. first visit: the site is still MARKED as issuing tickets ───────────
# issues_tickets defaults to 1 as a fail-safe, so a site nobody has corrected
# yet still asks for a ticket. That part is right — what was wrong is that the
# driver had no idea it was a setting, and no way to say otherwise from the
# cab. The refusal now names the way out.
as_driver()
_payload = {
    "_csrf_token": "tok",
    "dump_site": "Branscome",
    "can_number": "2036",
    "arrival_time": "9:22 AM",
    "departure_time": "9:37 AM",
    # no net tons, no scale weights, no ticket number — exactly what he had
}
r = cl.post("/stop/%d/dump-ticket" % sid, data=dict(_payload), follow_redirects=True)
_body = r.get_data(as_text=True)
ok("Flat fee per load" in _body or "no scale" in _body.lower(),
   "the refusal tells him the site's pricing is a setting he can fix, "
   "rather than just demanding paper he was never given")

# He taps "Free to dump" — Branscome takes his clean concrete for nothing.
r = cl.post("/api/dump-site/%d/terms" % site_id, json={"mode": "free"}, headers=HJ)
ok(r.status_code == 200 and r.get_json().get("ok"),
   "a DRIVER can set the site's terms from the cab — he is the one standing "
   "at the scale house, and an office task for that evening never gets done")

# ── 3. now he saves exactly what he knows ─────────────────────────────────
r = cl.post("/stop/%d/dump-ticket" % sid, data=dict(_payload), follow_redirects=True)
ok(r.status_code in (200, 302), "the ticket saves with no tons and no ticket number "
   "— status %s (this is the reported bug)" % r.status_code)

c = app.get_db()
_t = c.execute("SELECT * FROM dump_tickets WHERE stop_id=?", (sid,)).fetchone()
ok(_t is not None, "a dump ticket row really exists — the record is kept, not skipped")
_t = dict(_t)
ok(_t["can_number"] == "2036",
   "the can number survives, which is what keeps the box in/out chain intact "
   "for the rest of the day")
ok((_t["arrival_time"] or "") == "9:22 AM" and (_t["departure_time"] or "") == "9:37 AM",
   "so do the times he actually recorded")
ok(not (_t["net_tons"] or 0), "and tons are simply absent, not faked")
ok((_t["ticket_number"] or "").startswith("HT-"),
   "an internal reference is generated in place of a site ticket: %s"
   % _t["ticket_number"])
ok("TH" in (_t["ticket_number"] or ""),
   "stamped with the driver's initials, so two drivers at one site never "
   "collide")
c.close()


# ── 3b. the invoice refuses to go quiet ───────────────────────────────────
# A DIFFERENT site, still on the per_ton default and never corrected, with a
# completed dump that recorded no weight. This is the case that bills $0 in
# silence — the one the note exists for. (Branscome above is already marked
# free, so it is correctly silent.)
c = app.get_db()
_cur = c.cursor()
_cur.execute("""INSERT INTO saved_addresses (company_id,customer_name,address,full_address,kind,
                norm_key,hidden,times_used,last_used_at,created_at,issues_tickets)
                VALUES (?,?,?,?,?,?,0,1,?,?,0)""",
             (co, "Dominion", "1 Dominion Way", "1 Dominion Way, Chesapeake", "dump",
              app._address_book_key("Dominion", "1 Dominion Way", "dump"), ts, ts))
site2 = _cur.lastrowid
_cur.execute("""INSERT INTO stops (route_id, stop_order, customer_name, address, action,
                container_size, dump_site_id, status, created_at)
                VALUES (?,?,?,?,?,?,?, 'completed', ?)""",
             (rid, 90, "Ashdon", "11496 Shiloh Dr", "Pull", "30yd", site2, app.now_ts()))
c.commit()
c.execute("UPDATE stops SET status='completed' WHERE id=?", (sid,))
c.commit()
_lines = app._build_invoice_lines_for_route(c, co, rid)
c.close()
_note = [l for l in _lines if "no weight recorded" in (l.get("description") or "")]
ok(len(_note) == 1,
   "a weight-priced site that produced no weight is called out on the "
   "invoice — disposal is tons x rate, so it would otherwise bill $0 in "
   "silence and surface only when the month was closed")
ok(_note[0]["amount_cents"] == 0,
   "as a zero line — a note that something is wrong, never an invented charge")
ok("flat or free" in _note[0]["description"],
   "and it says what to do about it")


# ── 4. and if it turns out they do charge, a flat fee prices it ───────────
as_driver()
r = cl.post("/api/dump-site/%d/terms" % site_id,
            json={"mode": "flat", "flat_cents": 7500}, headers=HJ)
ok(r.status_code == 200 and r.get_json().get("ok"),
   "the same control switches the site to a flat per-load fee")
c = app.get_db()
_s = dict(c.execute("SELECT * FROM saved_addresses WHERE id=?", (site_id,)).fetchone())
ok(_s["disposal_mode"] == "flat" and _s["disposal_flat_cents"] == 7500,
   "the site now bills $75 a load")
ok(int(_s["issues_tickets"]) == 0,
   "and stops demanding a weigh ticket — a yard with no scale has nothing to "
   "print one from")
_lines2 = app._build_invoice_lines_for_route(c, co, rid)
c.close()
_disp = [l for l in _lines2 if l.get("kind") == "disposal"]
ok(len(_disp) == 1 and _disp[0]["amount_cents"] == 7500,
   "and that same completed dump now bills $75 instead of nothing")
ok("flat per load" in _disp[0]["description"],
   "described honestly — no fabricated tonnage on the customer's invoice")
ok(not any("no weight recorded" in (l.get("description") or "")
           and l.get("stop_id") == sid for l in _lines2),
   "and the warning retires itself for THAT stop, because nothing is wrong "
   "with it any more — the still-uncorrected Dominion stop keeps warning")
ok(any("no weight recorded" in (l.get("description") or "")
       and l.get("stop_id") != sid for l in _lines2),
   "which is how you can tell the note tracks the site's own terms rather "
   "than being switched off wholesale")

# Scoping: a driver cannot retune a customer's address, only a dump site.
c = app.get_db()
_cur = c.cursor()
_cur.execute("""INSERT INTO saved_addresses (company_id,customer_name,address,full_address,kind,
                norm_key,hidden,times_used,last_used_at,created_at)
                VALUES (?,?,?,?,?,?,0,1,?,?)""",
             (co, "Sussex", "5225 Learning Cir", "5225 Learning Cir, VB", "customer",
              app._address_book_key("Sussex", "5225 Learning Cir", "customer"), ts, ts))
cust_id = _cur.lastrowid
c.commit(); c.close()
r = cl.post("/api/dump-site/%d/terms" % cust_id, json={"mode": "free"}, headers=HJ)
ok(r.status_code == 404, "a customer address is not a dump site and is refused")
r = cl.post("/api/dump-site/%d/terms" % site_id, json={"mode": "banana"}, headers=HJ)
ok(r.status_code == 400, "an unknown pricing mode is refused")


# ── 5. the form stops lying about what it needs ────────────────────────────
c = app.get_db()
sid2 = c.execute("SELECT id FROM stops WHERE route_id=?", (rid,)).fetchone()["id"]
c.execute("UPDATE stops SET status='open', driver_status='going_to_dump' WHERE id=?", (sid2,))
c.commit(); c.close()
as_driver()
_form = cl.get("/stop/%d/dump-ticket" % sid2).get_data(as_text=True)
ok("DUMP TICKET" in _form.upper(), "the dump ticket form renders")
ok("Enter net tons (or fill scale-in" not in _form,
   "the form no longer carries the rule that blocked him — net tons is never "
   "required, because the server never required it either")
ok("SITE_ISSUES_TICKETS" in _form,
   "the browser now validates against the SITE's policy instead of inventing "
   "a stricter one than the server it posts to")

print("ALL NO-SCALE-DUMP TESTS PASSED")
