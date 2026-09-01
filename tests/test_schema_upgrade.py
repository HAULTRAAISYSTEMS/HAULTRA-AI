"""Schema-upgrade guards.

Every other suite here starts from an EMPTY database, where CREATE TABLE
includes every column and ordering inside init_db() never matters. Production
does the opposite: the table already exists on the persistent disk, CREATE TABLE
IF NOT EXISTS is a no-op, and a column only appears if safe_add_column() put it
there. An index created before its column is added therefore raises
"no such column" and kills the boot -- a green test suite and a failed deploy.

That shipped once (idx_alerts_unemailed vs alerts.emailed_at). These tests make
the whole class visible.
"""
import os, re, sys, io, sqlite3, tempfile, importlib

TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "upgrade.db")
os.environ["SECRET_KEY"] = "upgrade"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)


def ok(c, m):
    print(("PASS" if c else "FAIL") + " - " + m)
    if not c:
        raise SystemExit("FAILED: " + m)


# ── 1. Static ordering check over init_db() ───────────────────────────────
# Cheap, general, and catches this before a deploy rather than after.
src = io.open(os.path.join(ROOT, "app.py"), encoding="utf-8").read()
start = src.index("def init_db(")
end = src.index("\ndef ", start + 10)
body = src[start:end]

# every safe_add_column(conn, "table", "column TYPE ...") and where it appears
added = {}          # (table, column) -> position
for m in re.finditer(r'safe_add_column\(\s*conn\s*,\s*"([a-z_]+)"\s*,\s*"([a-zA-Z_]+)', body):
    added.setdefault((m.group(1), m.group(2)), m.start())
# also the loop form: for _t in ("a","b"): safe_add_column(conn, _t, "col ...")
loop_tables = re.findall(r'for\s+\w+\s+in\s+\(([^)]*)\):', body)

problems = []
for m in re.finditer(r'CREATE (?:UNIQUE )?INDEX IF NOT EXISTS\s+(\w+)\s*"?\s*"?\s*ON\s+(\w+)\(([^)]*)\)',
                     body, re.S):
    idx_name, table, cols_raw = m.group(1), m.group(2), m.group(3)
    idx_pos = m.start()
    cols = [c.strip().split()[0] for c in cols_raw.split(",") if c.strip()]
    for col in cols:
        pos = added.get((table, col))
        if pos is not None and pos > idx_pos:
            problems.append(
                "%s indexes %s.%s, but that column is only added by "
                "safe_add_column LATER in init_db()" % (idx_name, table, col))

ok(not problems,
   "no index is created before the column it references is added (%s)" % ("; ".join(problems) or "none"))

# ── 2. A real boot against the PREVIOUS alerts schema ─────────────────────
old_db = os.path.join(TMP, "old.db")
c = sqlite3.connect(old_db)
c.execute("""CREATE TABLE alerts (
    id INTEGER PRIMARY KEY AUTOINCREMENT, company_id INTEGER NOT NULL, kind TEXT NOT NULL,
    severity TEXT NOT NULL DEFAULT 'info' CHECK(severity IN ('critical','warning','info')),
    title TEXT NOT NULL, body TEXT, link TEXT, actor_user_id INTEGER, entity_type TEXT,
    entity_id INTEGER, dedupe_key TEXT, created_at TEXT NOT NULL, read_at TEXT,
    resolved_at TEXT, resolved_by INTEGER, pushed_at TEXT)""")
c.execute("""INSERT INTO alerts (company_id,kind,severity,title,created_at)
             VALUES (1,'DRIVER_LATE','warning','a row from before the upgrade','2026-08-31 10:00:00')""")
c.commit(); c.close()

os.environ["DATABASE_PATH"] = old_db
app = importlib.import_module("app")      # importing runs init_db() — the boot
app.app.config["TESTING"] = True
cl = app.app.test_client()

ok(cl.get("/health").status_code == 200, "app boots healthy against the previous schema")
ok(cl.get("/login").status_code == 200, "login renders after the upgrade")

conn = app.get_db()
cols = {r[1] for r in conn.execute("PRAGMA table_info(alerts)").fetchall()}
ok("emailed_at" in cols, "the missing column is added on boot, not assumed")
n = conn.execute("SELECT COUNT(*) n FROM alerts").fetchone()["n"]
ok(n == 1, "rows written before the upgrade survive it")
idx = [r[1] for r in conn.execute("PRAGMA index_list(alerts)").fetchall()]
ok("idx_alerts_unemailed" in idx, "the index gets created once its column exists")
conn.close()

print("\nALL SCHEMA UPGRADE TESTS PASSED")
