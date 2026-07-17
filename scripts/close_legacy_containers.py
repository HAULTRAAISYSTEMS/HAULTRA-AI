#!/usr/bin/env python3
"""
Bulk close-out of legacy "containers out".

Why this exists
---------------
The containers showing in the Bin Tracker are real historical drops, but the
pulls happened off-app, so the "still out" list is stale and unverifiable.
This script closes those legacy containers by recording a *return*, so the
Bin Tracker only reflects real, app-tracked drops going forward.

How it closes them (and why history is preserved)
--------------------------------------------------
The Bin Tracker never stores an "out" flag. compute_containers_out() derives
what's on-site by replaying completed stops chronologically: a Delivery /
Pickup-and-Return / swap leaves a container behind, and a Pull closes it out.

So the correct, non-destructive way to mark a container returned is to append
a completed **Pull** stop at that same address, dated now, carrying the note
"closed as unverified legacy data". Nothing is deleted:

  * the original delivery rows stay exactly as they were (full history),
  * the replay now sees a Pull after each delivery, so the address drops off
    the on-site list,
  * a *new* delivery completed later still re-appears (it's replayed after
    this close-out), so real app-tracked drops going forward are unaffected.

Each company's close-out pulls are grouped under one clearly-labelled route
("Legacy container close-out (unverified)") so the audit trail is obvious.

Only closing OLD drops (--before)
---------------------------------
Live drops from a route dispatched today must stay open and on the map. Pass
--before YYYY-MM-DD to close only containers whose drop date is strictly
before that date; anything dropped on or after the cutoff is left open and
listed as "keep open" in the preview.

    --before 2026-07-17   # closes drops up to 2026-07-16; today's stay out

Undoing a close-out (--undo)
----------------------------
If a close-out was too broad (e.g. it swept up a live can), --undo deletes the
"Legacy container close-out" route(s) and their Pull stops, which reopens
every container they closed — a clean, self-contained reversal that touches
nothing else. Re-run with the right --before afterward. Typical repair:

    python3 scripts/close_legacy_containers.py --undo --yes
    python3 scripts/close_legacy_containers.py --before 2026-07-17 --dry-run
    python3 scripts/close_legacy_containers.py --before 2026-07-17 --yes

Safety
------
  * Snapshots the database first (sqlite online-backup API, same as
    scripts/backup_db.py) before touching anything. Skip with --no-snapshot
    only if you've already taken your own snapshot.
  * --dry-run shows exactly what would change and writes nothing.
  * Requires confirmation before writing (interactive "yes", or --yes for
    non-interactive shells).
  * Idempotent: re-running a close finds nothing eligible and does nothing;
    re-running an undo finds no close-out route and does nothing.

Usage (Render Shell)
--------------------
    python3 scripts/close_legacy_containers.py --dry-run              # preview all
    python3 scripts/close_legacy_containers.py --before 2026-07-17 --dry-run
    python3 scripts/close_legacy_containers.py --before 2026-07-17 --yes
    python3 scripts/close_legacy_containers.py --undo --yes           # reopen close-out
    python3 scripts/close_legacy_containers.py <company_id> --before 2026-07-17 --yes

DATABASE_PATH (and SECRET_KEY) must be set in the environment, same as the
web service — importing app relies on them.
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from app import DATABASE, get_db, now_ts, today_str, compute_containers_out
from backup_db import backup

CLOSE_NOTE = "closed as unverified legacy data"
CLOSEOUT_ROUTE_NAME = "Legacy container close-out (unverified)"


def parse_args(argv):
    """Manual arg parse so a --before value isn't mistaken for a company id."""
    opts = {
        "dry_run": False, "no_snapshot": False, "yes": False,
        "undo": False, "before": None, "company_id": None,
    }
    i = 0
    while i < len(argv):
        a = argv[i]
        if a in ("--dry-run", "-n"):
            opts["dry_run"] = True
        elif a == "--no-snapshot":
            opts["no_snapshot"] = True
        elif a in ("--yes", "-y"):
            opts["yes"] = True
        elif a == "--undo":
            opts["undo"] = True
        elif a == "--before":
            i += 1
            opts["before"] = argv[i] if i < len(argv) else None
        elif a.startswith("--before="):
            opts["before"] = a.split("=", 1)[1]
        elif not a.startswith("-"):
            opts["company_id"] = int(a)
        i += 1
    return opts


def drop_date(container):
    """Date portion (YYYY-MM-DD) of a container's drop timestamp, or ''."""
    return (container["since"] or "")[:10]


def snapshot_db():
    """Take a consistent online-backup snapshot before mutating anything."""
    backup_dir = os.path.join(os.path.dirname(os.path.abspath(DATABASE)) or ".", "backups")
    return backup(DATABASE, backup_dir)


def pick_created_by(conn, company_id):
    """A valid users.id to own the close-out route (created_by is NOT NULL).

    Prefer the company's owner, then any user belonging to the company, then
    any user at all — so the route is always attributable to a real account.
    """
    row = conn.execute(
        "SELECT owner_id FROM companies WHERE id=?", (company_id,)
    ).fetchone()
    if row and row["owner_id"]:
        return row["owner_id"]
    row = conn.execute(
        "SELECT id FROM users WHERE company_id=? ORDER BY id LIMIT 1", (company_id,)
    ).fetchone()
    if row:
        return row["id"]
    row = conn.execute("SELECT id FROM users ORDER BY id LIMIT 1").fetchone()
    return row["id"] if row else None


def close_company(conn, company_id, dry_run, before=None):
    """Close currently-out containers for one company (drop < `before` if set).

    Returns the number of containers closed (or that would be closed on a dry
    run).
    """
    out = compute_containers_out(conn, company_id)
    if not out:
        print(f"Company {company_id}: 0 containers out — nothing to close.")
        return 0

    if before:
        eligible = [c for c in out if drop_date(c) < before]
        keep_open = [c for c in out if drop_date(c) >= before]
    else:
        eligible, keep_open = out, []

    print(f"Company {company_id}: {len(out)} out — "
          f"{len(eligible)} to close, {len(keep_open)} kept open.")
    for c in eligible:
        print(f"    close: {_desc(c)}  (dropped {drop_date(c) or '?'})")
    for c in keep_open:
        print(f"    keep open (on/after {before}): {_desc(c)}  (dropped {drop_date(c) or '?'})")

    if dry_run or not eligible:
        return len(eligible)

    created_by = pick_created_by(conn, company_id)
    if created_by is None:
        print(f"    SKIP company {company_id}: no user found to own the close-out route.")
        return 0

    ts = now_ts()
    cur = conn.cursor()
    cur.execute(
        """INSERT INTO routes (route_date, route_name, raw_text, assigned_to,
                               created_by, status, notes, company_id, created_at)
           VALUES (?, ?, NULL, NULL, ?, 'completed', ?, ?, ?)""",
        (today_str(), CLOSEOUT_ROUTE_NAME, created_by, CLOSE_NOTE, company_id, ts),
    )
    route_id = cur.lastrowid

    for i, c in enumerate(eligible, start=1):
        cur.execute(
            """INSERT INTO stops (route_id, stop_order, customer_name, address, city,
                                  state, action, container_size, notes, status,
                                  completed_at, created_at)
               VALUES (?, ?, ?, ?, ?, ?, 'Pull', ?, ?, 'completed', ?, ?)""",
            (
                route_id, i, c["customer_name"], c["address"], c["city"],
                c["state"], c["size"], CLOSE_NOTE, ts, ts,
            ),
        )
    conn.commit()
    print(f"    closed {len(eligible)} container(s) under route #{route_id}.")
    return len(eligible)


def undo_company(conn, company_id, dry_run):
    """Delete this company's legacy close-out route(s), reopening their cans.

    Returns the number of close-out Pull stops removed (= containers reopened).
    """
    routes = conn.execute(
        "SELECT id FROM routes WHERE company_id=? AND route_name=?",
        (company_id, CLOSEOUT_ROUTE_NAME),
    ).fetchall()
    route_ids = [r["id"] for r in routes]
    if not route_ids:
        print(f"Company {company_id}: no close-out route found — nothing to undo.")
        return 0

    placeholders = ",".join("?" for _ in route_ids)
    n = conn.execute(
        f"SELECT COUNT(*) c FROM stops WHERE route_id IN ({placeholders})",
        route_ids,
    ).fetchone()["c"]
    print(f"Company {company_id}: reopening {n} container(s) from route(s) "
          f"{', '.join('#' + str(r) for r in route_ids)}.")

    if dry_run:
        return n

    conn.execute(f"DELETE FROM stops WHERE route_id IN ({placeholders})", route_ids)
    conn.execute(f"DELETE FROM routes WHERE id IN ({placeholders})", route_ids)
    conn.commit()
    print(f"    reopened {n} container(s).")
    return n


def _desc(c):
    addr = c["address"] or ""
    city = f', {c["city"]}' if c["city"] else ""
    size = f' [{c["size"]}]' if c["size"] else ""
    cust = f' — {c["customer_name"]}' if c["customer_name"] else ""
    return f"{addr}{city}{size}{cust}"


def confirm(opts, prompt):
    if opts["yes"]:
        return True
    if not sys.stdin.isatty():
        print("Refusing to write without confirmation. Re-run with --yes.")
        return False
    return input(prompt).strip().lower() in ("y", "yes")


def main():
    opts = parse_args(sys.argv[1:])

    if opts["before"] is not None and not re.fullmatch(r"\d{4}-\d{2}-\d{2}", opts["before"]):
        print(f"--before must be a date like 2026-07-17 (got {opts['before']!r}).")
        return

    conn = get_db()
    if opts["company_id"] is not None:
        company_ids = [opts["company_id"]]
    else:
        company_ids = [r["id"] for r in conn.execute("SELECT id FROM companies ORDER BY id").fetchall()]

    if not company_ids:
        print("No companies found.")
        conn.close()
        return

    def run(company_id, dry_run):
        if opts["undo"]:
            return undo_company(conn, company_id, dry_run)
        return close_company(conn, company_id, dry_run, before=opts["before"])

    verb = "reopen" if opts["undo"] else "close"
    past = "reopened" if opts["undo"] else "closed"
    if opts["before"] and not opts["undo"]:
        print(f"=== Preview: containers to close (dropped before {opts['before']}) ===")
    elif opts["undo"]:
        print("=== Preview: close-out to undo (reopen) ===")
    else:
        print("=== Preview: containers currently out ===")

    total = 0
    for company_id in company_ids:
        total += run(company_id, dry_run=True)

    if total == 0:
        print(f"\nNothing to {verb}. No changes needed.")
        conn.close()
        return

    if opts["dry_run"]:
        print(f"\nDry run: {total} container(s) would be {past}. No changes written.")
        conn.close()
        return

    noun = "reopen" if opts["undo"] else f"close as '{CLOSE_NOTE}'"
    if not confirm(opts, f"\n{verb.capitalize()} {total} container(s) ({noun})? [y/N] "):
        print("Aborted. No changes written.")
        conn.close()
        return

    conn.close()  # release the read connection before snapshot/writes

    if not opts["no_snapshot"]:
        print("\n=== Snapshotting database ===")
        snapshot_db()
    else:
        print("\nSkipping snapshot (--no-snapshot).")

    print(f"\n=== {'Reopening' if opts['undo'] else 'Closing'} containers ===")
    conn = get_db()
    changed = 0
    for company_id in company_ids:
        changed += run(company_id, dry_run=False)

    # Report the resulting Bin Tracker state for the affected companies.
    print("\n=== Verifying ===")
    for company_id in company_ids:
        n = len(compute_containers_out(conn, company_id))
        print(f"    Company {company_id}: {n} container(s) now out.")
    conn.close()

    print(f"\nDone. {'Reopened' if opts['undo'] else 'Closed'} {changed} container(s).")


if __name__ == "__main__":
    main()
