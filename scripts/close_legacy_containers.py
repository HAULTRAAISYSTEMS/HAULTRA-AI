#!/usr/bin/env python3
"""
One-time bulk close-out of legacy "containers out".

Why this exists
---------------
The containers showing in the Bin Tracker are real historical drops, but the
pulls happened off-app, so the "still out" list is stale and unverifiable.
This script closes every currently-out container by recording a *return*,
so the Bin Tracker resets to zero and only new, app-tracked drops show up
going forward.

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
    the on-site list -> Bin Tracker shows zero out,
  * a *new* delivery completed later still re-appears (it's replayed after
    this close-out), so real app-tracked drops going forward are unaffected.

Each company's close-out pulls are grouped under one clearly-labelled route
("Legacy container close-out (unverified)") so the audit trail is obvious.

Safety
------
  * Snapshots the database first (sqlite online-backup API, same as
    scripts/backup_db.py) before touching anything. Skip with --no-snapshot
    only if you've already taken your own snapshot.
  * --dry-run shows exactly what would be closed and writes nothing.
  * Requires confirmation before writing (interactive "yes", or --yes for
    non-interactive shells).
  * Idempotent: re-running finds zero containers out and does nothing.

Usage (Render Shell)
--------------------
    python3 scripts/close_legacy_containers.py --dry-run          # preview all
    python3 scripts/close_legacy_containers.py --yes              # close all
    python3 scripts/close_legacy_containers.py <company_id> --yes # one company
    python3 scripts/close_legacy_containers.py --no-snapshot --yes

DATABASE_PATH (and SECRET_KEY) must be set in the environment, same as the
web service — importing app relies on them.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from app import DATABASE, get_db, now_ts, today_str, compute_containers_out
from backup_db import backup

CLOSE_NOTE = "closed as unverified legacy data"
CLOSEOUT_ROUTE_NAME = "Legacy container close-out (unverified)"


def snapshot_db():
    """Take a consistent online-backup snapshot before mutating anything."""
    backup_dir = os.path.join(os.path.dirname(os.path.abspath(DATABASE)) or ".", "backups")
    dest = backup(DATABASE, backup_dir)
    return dest


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


def close_company(conn, company_id, dry_run):
    """Close every currently-out container for one company.

    Returns the number of containers closed (or that would be closed on a
    dry run).
    """
    out = compute_containers_out(conn, company_id)
    if not out:
        print(f"Company {company_id}: 0 containers out — nothing to close.")
        return 0

    print(f"Company {company_id}: {len(out)} container(s) out.")
    for c in out:
        addr = c["address"] or ""
        city = f', {c["city"]}' if c["city"] else ""
        size = f' [{c["size"]}]' if c["size"] else ""
        cust = f' — {c["customer_name"]}' if c["customer_name"] else ""
        print(f"    close: {addr}{city}{size}{cust}")

    if dry_run:
        return len(out)

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

    for i, c in enumerate(out, start=1):
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
    print(f"    closed {len(out)} container(s) under route #{route_id}.")
    return len(out)


def confirm(prompt):
    if "--yes" in sys.argv or "-y" in sys.argv:
        return True
    if not sys.stdin.isatty():
        print("Refusing to write without confirmation. Re-run with --yes.")
        return False
    return input(prompt).strip().lower() in ("y", "yes")


def main():
    dry_run = "--dry-run" in sys.argv or "-n" in sys.argv
    no_snapshot = "--no-snapshot" in sys.argv

    positional = [a for a in sys.argv[1:] if not a.startswith("-")]

    conn = get_db()
    if positional:
        company_ids = [int(positional[0])]
    else:
        company_ids = [r["id"] for r in conn.execute("SELECT id FROM companies ORDER BY id").fetchall()]

    if not company_ids:
        print("No companies found.")
        conn.close()
        return

    # Preview first (this also tells us whether there's anything to do).
    print("=== Preview: containers currently out ===")
    total = 0
    for company_id in company_ids:
        total += close_company(conn, company_id, dry_run=True)

    if total == 0:
        print("\nNothing to close. Bin Tracker already shows zero containers out.")
        conn.close()
        return

    if dry_run:
        print(f"\nDry run: {total} container(s) would be closed. No changes written.")
        conn.close()
        return

    if not confirm(f"\nClose {total} container(s) as '{CLOSE_NOTE}'? [y/N] "):
        print("Aborted. No changes written.")
        conn.close()
        return

    conn.close()  # release the read connection before snapshot/writes

    if not no_snapshot:
        print("\n=== Snapshotting database ===")
        snapshot_db()
    else:
        print("\nSkipping snapshot (--no-snapshot).")

    print("\n=== Closing containers ===")
    conn = get_db()
    closed = 0
    for company_id in company_ids:
        closed += close_company(conn, company_id, dry_run=False)

    # Verify the Bin Tracker view is now empty for the affected companies.
    print("\n=== Verifying ===")
    remaining = 0
    for company_id in company_ids:
        n = len(compute_containers_out(conn, company_id))
        remaining += n
        if n:
            print(f"    Company {company_id}: {n} still out (unexpected).")
    conn.close()

    print(f"\nDone. Closed {closed} container(s).")
    if remaining == 0:
        print("Bin Tracker now shows zero containers out for the processed companies.")
    else:
        print(f"WARNING: {remaining} container(s) still show as out — investigate before re-running.")


if __name__ == "__main__":
    main()
