"""Regression test for the boot crash that took production down:

    sqlite3.IntegrityError: UNIQUE constraint failed: index 'idx_parse_vocab_pair'

raised from init_db() at import time, so every worker exited 1 and every deploy
failed. The trigger was a loop, not a one-off:

  * the seed guard was "no rows with company_id IS NULL", and the multi-tenant
    migration stamps every NULL row onto the bootstrap company -- so the 12
    global defaults were re-seeded as NULL rows on EVERY boot, and
  * once idx_parse_vocab_pair existed (created by the first deploy that ran the
    dedupe), the next boot's stamp collided those re-seeded rows with their
    already-stamped twins.

This test drives init_db() against the exact production states and asserts it
boots clean and stays clean across repeated boots.
"""
import os, sys, tempfile, importlib

TMP = tempfile.mkdtemp()
os.environ["DATABASE_PATH"] = os.path.join(TMP, "pv.db")
os.environ["SECRET_KEY"] = "a"
os.environ["UPLOAD_FOLDER"] = os.path.join(TMP, "up")
os.makedirs(os.environ["UPLOAD_FOLDER"], exist_ok=True)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
app = importlib.import_module("app")   # importing runs init_db() once


def ok(c, m):
    print(("PASS" if c else "FAIL") + " - " + m)
    if not c: raise SystemExit("FAILED: " + m)


conn = app.get_db()


def index_exists():
    return conn.execute(
        "SELECT 1 FROM sqlite_master WHERE type='index' AND name='idx_parse_vocab_pair'"
    ).fetchone() is not None


def dupe_groups():
    return conn.execute("""
        SELECT COUNT(*) FROM (
            SELECT 1 FROM parse_vocab
             GROUP BY company_id, LOWER(TRIM(term)), LOWER(TRIM(expansion))
            HAVING COUNT(*) > 1)
    """).fetchone()[0]


def null_rows():
    return conn.execute("SELECT COUNT(*) FROM parse_vocab WHERE company_id IS NULL").fetchone()[0]


def rows_for(term):
    return conn.execute(
        "SELECT id, company_id, COALESCE(times_used,1) AS tu FROM parse_vocab "
        "WHERE LOWER(TRIM(term))=? ORDER BY id", (term,)).fetchall()


def add(company_id, term, expansion, times_used):
    conn.execute(
        "INSERT INTO parse_vocab (company_id, term, expansion, kind, times_used, created_at) "
        "VALUES (?,?,?,'shorthand',?,?)", (company_id, term, expansion, times_used, app.now_ts()))


co = conn.execute("SELECT id FROM companies LIMIT 1").fetchone()["id"]

# ---- fresh boot ------------------------------------------------------------
ok(index_exists(), "fresh boot creates idx_parse_vocab_pair")
ok(null_rows() == 0, "fresh boot leaves no NULL-company rows")
ok(dupe_groups() == 0, "fresh boot leaves no duplicate pairs")

# ---- scenario A: the exact production crash --------------------------------
# Index EXISTS. Re-seeded NULL rows twin the already-stamped defaults, plus a
# legacy pile of NULL duplicates. NULLs are distinct under a SQLite unique
# index, so these inserts are allowed -- it is the STAMP that used to collide.
for _ in range(14):
    add(None, "hamp", "Hampton", 1)            # legacy pile, twins a stamped row
add(None, "HAMP ", " hampton ", 2)             # case/whitespace variant of the same pair
add(None, "chvl", "Charlottesville", 7)        # NULL row with no stamped twin
conn.commit()

ok(null_rows() == 16, "scenario A staged: 16 NULL-company rows present")
before_hamp = sum(r["tu"] for r in rows_for("hamp"))

app.init_db()   # must NOT raise IntegrityError

ok(True, "scenario A: init_db() survives re-seeded NULL twins + existing index")
ok(null_rows() == 0, "scenario A: every NULL row stamped onto the bootstrap company")
ok(dupe_groups() == 0, "scenario A: no duplicate pairs remain")
ok(index_exists(), "scenario A: unique index still present")

hamp = rows_for("hamp")
ok(len(hamp) == 1, "scenario A: the ~14x 'hamp' pile collapsed to a single row")
ok(hamp[0]["tu"] == before_hamp,
   "scenario A: usage counts summed, not lost (%d)" % hamp[0]["tu"])
ok(hamp[0]["company_id"] == co, "scenario A: survivor owned by the bootstrap company")

chvl = rows_for("chvl")
ok(len(chvl) == 1 and chvl[0]["tu"] == 7, "scenario A: untwinned NULL row stamped, count intact")

# ---- scenario B: half-applied run (index absent, rows already stamped) ------
conn.execute("DROP INDEX IF EXISTS idx_parse_vocab_pair")
conn.commit()
ok(not index_exists(), "scenario B staged: index dropped")

add(co, "dom", "Dominion", 3)                  # duplicate ALREADY stamped
add(co, " DOM ", "dominion", 4)                # stamped, case/whitespace variant
add(None, "dom", "Dominion", 5)                # unstamped twin of the same pair
add(None, "wat", "Waterway", 1)                # unstamped twin of a clean row
conn.commit()
ok(dupe_groups() > 0, "scenario B staged: stamped duplicates exist with no index")
before_dom = sum(r["tu"] for r in rows_for("dom"))

app.init_db()   # must NOT raise

ok(True, "scenario B: init_db() survives stamped duplicates + missing index")
ok(index_exists(), "scenario B: unique index recreated")
ok(null_rows() == 0, "scenario B: no NULL-company rows remain")
ok(dupe_groups() == 0, "scenario B: stamped duplicates collapsed")
dom = rows_for("dom")
ok(len(dom) == 1, "scenario B: 'dom' duplicates collapsed to one row")
ok(dom[0]["tu"] == before_dom, "scenario B: usage counts summed across stamped+NULL (%d)" % dom[0]["tu"])

# ---- repeated boots: the actual regression ---------------------------------
# The old code failed on the SECOND boot, so one clean pass proves nothing.
snapshot = conn.execute("SELECT COUNT(*) FROM parse_vocab").fetchone()[0]
for i in range(4):
    app.init_db()
    ok(null_rows() == 0, "boot %d: no NULL rows" % (i + 2))
    ok(dupe_groups() == 0, "boot %d: no duplicate pairs" % (i + 2))
ok(conn.execute("SELECT COUNT(*) FROM parse_vocab").fetchone()[0] == snapshot,
   "repeated boots are idempotent - row count stable, no re-seed churn")

print("\nAll parse_vocab migration tests passed.")
