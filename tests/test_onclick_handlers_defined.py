"""Every onclick= on a rendered page calls a function the page actually defines.

Reported 2026-11-17: "The rearrange is not working on the driver side."

The cab's rearrange arrows render `onclick="roMove(this,-1)"`. roMove was
defined inside a <script> that lived in _reorder_html — a variable that stopped
being rendered on 2026-10-10 when the toggle moved to the top bar. The LIST
kept being emitted (from _reorder_list_html), the script did not, so every
arrow called a function that did not exist and nothing happened, silently.

The reorder API was healthy the whole time. test_driver_autonomy proved it,
and proving it is exactly why nobody noticed: the endpoint test passes whether
or not any button on earth can reach it.

So this file checks the wiring instead of the endpoint. It walks the real
rendered HTML of the pages a driver and a boss actually use, pulls every
function name out of every onclick/onchange/onsubmit attribute, and asserts
the page defines it. A dead handler is invisible in production — nothing
throws where anyone looks, the button just does nothing — which makes it worth
a guard rather than a one-off assertion about roMove.
"""
import os, re, sys, tempfile, importlib
TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "onclick.db")
os.environ["SECRET_KEY"] = "onclick"
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
            ("WireCo", "wireco", "pro", "active", 10, "2545 Squadron Ct", "Virginia Beach", ts))
co = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("w_boss", "x", "boss", "Boss", co, ts)); boss = cur.lastrowid
cur.execute("INSERT INTO users (username,password_hash,role,full_name,company_id,created_at) VALUES (?,?,?,?,?,?)",
            ("w_drv", "x", "driver", "Tim", co, ts)); drv = cur.lastrowid
conn.commit(); conn.close()

app.app.config["TESTING"] = True
cl = app.app.test_client()
HJ = {"X-CSRF-Token": "tok"}
_today = app.now_ts()[:10]

with cl.session_transaction() as s:
    s.update(user_id=boss, company_id=co, role="boss", roles=["owner", "dispatcher"], _csrf_token="tok")
# Enough stops that the cab has upcoming ones to offer for rearranging — with
# fewer than two the reorder list is not rendered and this test would pass by
# finding nothing.
r = cl.post("/api/dispatch", json={"driver_id": drv, "route_date": _today, "stops": [
    {"action": "PR", "address": "529 Whispering Oaks Cir, Chesapeake", "customer": "Jaswal",
     "container_size": "30yd", "dump_leg": "Dominion"},
    {"action": "P",  "address": "114 Sawyers Creek, Camden, NC", "customer": "Heartland",
     "container_size": "30yd"},
    {"action": "D",  "address": "1609 Laskin Rd, Virginia Beach", "customer": "Taylors Do-It",
     "container_size": "30yd"},
    {"action": "PR", "address": "401 Clearfield Ave, Chesapeake", "customer": "Balicore",
     "container_size": "30yd", "dump_leg": "Dominion"},
]}, headers=HJ)
ok(r.status_code == 200, "a four-stop route dispatches — status %s" % r.status_code)
c = app.get_db()
rid = c.execute("SELECT id FROM routes WHERE company_id=? AND route_date=?",
                (co, _today)).fetchone()["id"]
c.close()

board_html = cl.get("/routes").get_data(as_text=True)
ok("lane-track" in board_html and "Sortable" in board_html,
   "the route board with its drag-to-reorder lanes renders — the gesture "
   "assertions below mean nothing against the wrong page")

with cl.session_transaction() as s:
    s.update(user_id=drv, company_id=co, role="driver", roles=["driver"], _csrf_token="tok")
cl.post("/driver/clock/in", data={"_csrf_token": "tok", "next": "/driver/route/%d" % rid})
cl.post("/route/%d/start" % rid, data={"_csrf_token": "tok"})
cab_html = cl.get("/driver/route/%d" % rid).get_data(as_text=True)
ok('class="cab-card' in cab_html and "PRE-FLIGHT" not in cab_html,
   "the cab card renders — otherwise there are no handlers to check and this "
   "whole file would pass for the wrong reason")


# Browser and DOM things a page never defines itself.
_BUILTIN = {
    "alert", "confirm", "prompt", "fetch", "open", "print", "close", "focus",
    "blur", "reload", "submit", "reset", "scrollTo", "setTimeout", "history",
    "parseInt", "parseFloat", "encodeURIComponent", "decodeURIComponent",
    "String", "Number", "Boolean", "Array", "Object", "JSON", "Date", "Math",
    "event", "this", "return", "if", "else", "function", "var", "let", "const",
    "true", "false", "null", "undefined", "typeof", "new", "delete", "void",
}
# fn( at the start of a handler or after ; & { or a logical operator.
_CALL_RE = re.compile(r"(?:^|[;{}&|!(,=\s])([A-Za-z_$][\w$]*)\s*\(")
_ATTR_RE = re.compile(r'\son(?:click|change|submit|input|focus|blur)\s*=\s*"([^"]*)"', re.I)


def undefined_handlers(html, label):
    """Function names called from an inline handler that the page never defines."""
    called = set()
    for body in _ATTR_RE.findall(html):
        # Strip string literals first: text inside quotes is data, and a word
        # followed by "(" inside one is not a call.
        _b = re.sub(r"&#39;[^&]*&#39;|'[^']*'", "''", body)
        for name in _CALL_RE.findall(_b):
            if name not in _BUILTIN:
                called.add(name)
    missing = []
    for name in sorted(called):
        # Anything that would put the name in scope on the page.
        defined = (
            re.search(r"\bfunction\s+%s\s*\(" % re.escape(name), html)
            or re.search(r"\bwindow\.%s\s*=" % re.escape(name), html)
            or re.search(r"\b(?:var|let|const)\s+%s\s*=" % re.escape(name), html)
            or re.search(r"\b%s\s*[:=]\s*function" % re.escape(name), html)
            or re.search(r"\b%s\s*=\s*(?:async\s*)?\(" % re.escape(name), html)
        )
        # A method call like foo.bar() — the object is what matters, not bar.
        if not defined and ("." + name) in html:
            continue
        if not defined:
            missing.append(name)
    return missing


# ── the reported bug ───────────────────────────────────────────────────────
ok('onclick="roMove(' in cab_html,
   "the cab really does render the rearrange arrows — the fixture has "
   "upcoming stops to reorder")
ok("window.roMove" in cab_html,
   "and the page DEFINES roMove — it was rendering the arrows while the "
   "script that made them work was left in an unrendered variable "
   "(the reported 'rearrange is not working')")
ok("window.roSave" in cab_html,
   "roSave too, which is the half that actually posts the new order")
ok("/api/driver/route/" in cab_html and "/reorder" in cab_html,
   "and it posts to the reorder endpoint that test_driver_autonomy covers")


# ── the guard ──────────────────────────────────────────────────────────────
_cab_missing = undefined_handlers(cab_html, "cab")
ok(not _cab_missing,
   "every inline handler on the DRIVER cab page is defined (missing: %s)"
   % _cab_missing)

_board_missing = undefined_handlers(board_html, "board")
ok(not _board_missing,
   "every inline handler on the BOSS route board is defined (missing: %s)"
   % _board_missing)


# ── long-press drag vs the cancel menu ─────────────────────────────────────
# Two long-presses were armed on the same card: Sortable lifts to drag at
# 450ms, the cancel menu fired on its own 600ms timer. Holding a card to drag
# it popped "Cancel This Stop" over the lifted card 150ms later, before the
# finger had moved at all — which is exactly what waiting for the lift feels
# like. A timer cannot tell them apart; at 600ms a drag and a cancel look
# identical. Releasing can: hold-then-move is a drag, hold-then-let-go is the
# menu.
ok("onChoose" in board_html and "__stopDragActive" in board_html,
   "the drag claims the gesture when Sortable lifts a card")
ok("__stopDragActive" in board_html and "pressMoved" in board_html,
   "and the cancel menu checks both before opening — the lift, and whether "
   "the finger travelled")
ok(not re.search(r"showStopMenu\([^)]*\)[^;]*;\s*\}\s*,\s*LONG_PRESS_MS", board_html),
   "the menu is no longer armed on a bare timer that fires mid-drag")
ok("touchcancel" in board_html,
   "and a cancelled touch drops the press instead of leaving it armed")

print("ALL ONCLICK-WIRING TESTS PASSED")
