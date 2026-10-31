"""One job site is one billing group.

2026-10-31. The Ready-to-bill screen grouped on the raw address string:

    def _group_key(customer, site):
        return (c.casefold() or "unassigned", s.casefold() or "no address")

Casefold and nothing else. So one site typed three ways became three billing
groups, and "Bill all" would have sent a customer three invoices for the same
address. Observed live on Napo: 1013 Paragon Way at $4,725 / $1,100 / $400,
and on Marlyn: 697 Independence Pkwy at $6,250 / $3,700.

This is a MONEY bug, so the test file splits sharply in two:

  COLLAPSE -- pure formatting differences. Case, punctuation, a city/state
  suffix present or absent, an abbreviated street type. Same place, typed
  by a person in a hurry. Safe to merge automatically.

  STAY APART -- anything where the characters themselves differ: a different
  house number, a different street name, a different street TYPE. The boss
  says 1413/1431 Laskin and Independence Pkwy/Blvd are typos, and he is
  right about his own data -- but no rule can tell his typo from two real
  addresses on one street, and merging two real sites bills the wrong job.
  Those surface as suggestions instead.

Run:  python3 tests/test_billing_site_key.py
"""
import os
import sys
import tempfile
import importlib

TMP = tempfile.mkdtemp(prefix="haultra-sitekey-")
os.environ["DATABASE_PATH"] = os.path.join(TMP, "sk.db")
os.environ["SECRET_KEY"] = "sk"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")

FAILURES = []


def ok(cond, label):
    print(("PASS" if cond else "FAIL") + " - " + label, flush=True)
    if not cond:
        FAILURES.append(label)


# ── 1. The street key itself ───────────────────────────────────────
print("\n-- _street_key: the city/state tail comes off --")
SAME = [
    ("1013 Paragon Way, Suffolk, VA", "1013 Paragon Way, Suffolk", "1013 Paragon Way"),
    ("3533 sleepy hole rd, Suffolk", "3533 Sleepy Hole Rd, Suffolk, VA", "3533 Sleepy Hole Road"),
    ("5366 Virginia Beach Blvd, Virginia Beach", "5366 Virginia Beach blvd", None),
    ("697 Independence Pkwy, Chesapeake, VA", "697 Independence Parkway, Ches", None),
    ("11496 Shiloh Dr", "11496 Shiloh Drive, Norfolk, VA", "11496 shiloh dr, norf"),
]
for group in SAME:
    members = [g for g in group if g]
    keys = {app._street_key(m) for m in members}
    ok(len(keys) == 1,
       "one key for %r (got %r)" % (members, keys))
    ok(all(keys) and "" not in keys, "and it is not empty for %r" % (members[0],))

print("\n-- _street_key: what must stay different --")
DIFFERENT = [
    ("1413 Laskin Rd", "1431 Laskin Rd, Virginia Beach",
     "transposed house number -- a typo here, but two real houses elsewhere"),
    ("697 Independence Pkwy, Chesapeake", "697 Independence Blvd, Chesapeake",
     "different street TYPE -- Pkwy and Blvd can both exist"),
    ("1013 Paragon Way, Suffolk", "1015 Paragon Way, Suffolk",
     "neighbouring house numbers"),
    ("100 Main St", "100 Main Ave", "Street and Avenue are different streets"),
    ("40 Legacy Way", "40 Legacy Way N", "a direction is part of the street name"),
]
for a, b, why in DIFFERENT:
    ok(app._street_key(a) != app._street_key(b),
       "%r and %r stay apart (%s)" % (a, b, why))

print("\n-- _street_key: degenerate input --")
ok(app._street_key("") == "", "empty in, empty out")
ok(app._street_key(None) == "", "None in, empty out")
ok(app._street_key("Suffolk, VA") != "",
   "an address that is ONLY a city keeps something, never collapses to blank")
ok(app._street_key("  1013   Paragon   Way  ") == app._street_key("1013 Paragon Way"),
   "runs of whitespace do not matter")

# ── 2. _group_key uses it ──────────────────────────────────────────
print("\n-- _group_key --")
k1 = app._group_key("Napo", "1013 Paragon Way, Suffolk, VA")
k2 = app._group_key("Napo", "1013 Paragon Way, Suffolk")
k3 = app._group_key("Napo", "1013 Paragon Way")
ok(k1 == k2 == k3, "Napo's three spellings are ONE billing group (got %r/%r/%r)" % (k1, k2, k3))
ok(app._group_key("NAPO", "1013 Paragon Way") == k3, "customer name case does not split the group")
ok(app._group_key("Napo", "1413 Laskin Rd") != app._group_key("Napo", "1431 Laskin Rd"),
   "but a different house number is still its own group")
ok(app._group_key("Napo", "1013 Paragon Way") != app._group_key("Marlyn", "1013 Paragon Way"),
   "two customers at one address are never one group")
ok(app._group_key("", "") == ("unassigned", "no address"),
   "blank customer and site keep their placeholders")
ok(app._group_key("Napo", "") == ("napo", "no address"), "blank site alone keeps its placeholder")

# ── 3. The group shows the most complete spelling ──────────────────
print("\n-- _group_display picks the fullest address --")
d1 = app._group_display("Napo", "1013 Paragon Way")
d2 = app._group_display("Napo", "1013 Paragon Way, Suffolk, VA")
ok(d2[1] == "1013 Paragon Way, Suffolk, VA", "the full spelling renders as given")
ok(d1[1] == "1013 Paragon Way", "and a bare one renders as given")
ok(app._group_display("", "")[0] == "Unassigned", "blank customer still reads Unassigned")

# ── 4. End to end: the real Napo and Marlyn numbers ────────────────
print("\n-- the live case, end to end --")
app.init_db()
conn = app.get_db()
cur = conn.cursor()
ts = app.now_ts()
cur.execute("INSERT INTO companies (name, slug, subscription_plan, subscription_status,"
            " max_drivers, created_at) VALUES (?,?,?,?,?,?)",
            ("Bill Co", "billco", "pro", "active", 10, ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username, password_hash, role, full_name, company_id,"
            " is_active, created_at) VALUES (?,?,?,?,?,1,?)",
            ("bill_drv", "x", "driver", "Bill Driver", co, ts))
drv = cur.lastrowid
cur.execute("INSERT INTO routes (company_id, route_date, route_name, created_by,"
            " assigned_to, status, created_at) VALUES (?,?,?,?,?,'completed',?)",
            (co, "2026-10-20", "Bill Route", drv, drv, ts))
rid = cur.lastrowid
# Napo: one site, three spellings. Plus a genuinely different house number.
LIVE = [
    ("Napo", "1013 Paragon Way, Suffolk, VA"),
    ("Napo", "1013 Paragon Way, Suffolk"),
    ("Napo", "1013 Paragon Way"),
    ("Napo", "3533 sleepy hole rd, Suffolk"),
    ("Napo", "3533 Sleepy Hole Rd, Suffolk, VA"),
    ("Marlyn", "1413 Laskin Rd"),
    ("Marlyn", "1431 Laskin Rd, Virginia Beach"),
]
for i, (cn, ad) in enumerate(LIVE, start=1):
    cur.execute("""INSERT INTO stops (route_id, stop_order, customer_name, address, city,
                   state, action, container_size, status, completed_at, created_at)
                   VALUES (?,?,?,?,'Suffolk','VA','Pull','20yd','completed',?,?)""",
                (rid, i, cn, ad, ts, ts))
conn.commit()

groups = app._unbilled_stop_groups(conn, co)
napo = [g for g in groups if g["customer"].casefold() == "napo"]
marlyn = [g for g in groups if g["customer"].casefold() == "marlyn"]
conn.close()

ok(len(napo) == 2,
   "Napo's 5 stops make 2 billing groups (Paragon + Sleepy Hole), not 5 (got %d: %r)"
   % (len(napo), [g["site"] for g in napo]))
_paragon = [g for g in napo if "paragon" in g["site"].casefold()]
ok(len(_paragon) == 1 and _paragon[0]["n_stops"] == 3,
   "all three Paragon Way jobs land in ONE group (got %r)"
   % ([(g["site"], g["n_stops"]) for g in _paragon],))
_sleepy = [g for g in napo if "sleepy" in g["site"].casefold()]
ok(len(_sleepy) == 1 and _sleepy[0]["n_stops"] == 2,
   "both Sleepy Hole jobs land in ONE group (got %r)"
   % ([(g["site"], g["n_stops"]) for g in _sleepy],))
# The merged group should read as the fullest spelling on the invoice, not
# whichever stop happened to come first.
ok(_sleepy and _sleepy[0]["site"] == "3533 Sleepy Hole Rd, Suffolk, VA",
   "the group shows the most complete spelling, not the first one (got %r)"
   % (_sleepy[0]["site"] if _sleepy else None,))
ok(_paragon and _paragon[0]["site"] == "1013 Paragon Way, Suffolk, VA",
   "same for Paragon Way (got %r)" % (_paragon[0]["site"] if _paragon else None,))
ok(len(marlyn) == 2,
   "but Marlyn's two Laskin house numbers stay as 2 groups -- a human decides "
   "whether that is a typo (got %d)" % len(marlyn))

print("\n%d failure(s)" % len(FAILURES))
for f in FAILURES:
    print("  FAILED: " + f)
sys.exit(1 if FAILURES else 0)
