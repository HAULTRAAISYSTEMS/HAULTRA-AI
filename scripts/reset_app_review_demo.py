#!/usr/bin/env python3
"""Reset the App Review demo tenant to a true pre-flight state.

Run this immediately before submitting a build. `verify_app_review_demo` in
app.py is NOT a substitute: for a route that already exists it only writes
`status='open'`, never touches stops, and the `open -> in_progress` promotion
in app.py then re-derives `in_progress` from the still-completed stops. The
net effect is churned badges over permanently-completed work, so a reviewer
sees "All Stops Done" and can never tap START ROUTE.

This resets the driver-progress columns on every stop of every route in the
reserved demo company, so each route renders its pre-flight card again.

Deliberately a manual, human-gated step rather than something on the 6-hourly
maintenance timer: it is destructive, and a timer could wipe a reviewer's route
out from under them mid-session.

Scoped strictly to the reserved demo company; it will refuse to touch anything
else. Idempotent, and safe to re-run.

    DATABASE_PATH=/path/to/haultra.db python3 scripts/reset_app_review_demo.py
    DATABASE_PATH=... python3 scripts/reset_app_review_demo.py --dry-run
"""

import os
import sqlite3
import sys

# Must match APP_REVIEW_DEMO_SLUG in app.py.
APP_REVIEW_DEMO_SLUG = "haultra-app-review"

# Driver-progress columns cleared on every demo stop. Each is listed with the
# value that means "untouched". Columns absent on an older schema are skipped,
# so this runs against any deployed version.
STOP_RESET = {
    "status": "open",
    "driver_status": "pending",
    "completed_at": None,
    "arrived_at": None,
    "held_at": None,
    "box_in_at": None,
    "box_out_at": None,
    "go_to_dump_at": None,
    "driver_signature": None,
    "photo_path": None,
    "active_leg": "primary",
}

ROUTE_RESET = {
    "status": "open",
    "started_at": None,
    "completed_at": None,
}


def existing_columns(conn, table):
    return {r["name"] for r in conn.execute(f"PRAGMA table_info({table})")}


def apply_reset(conn, table, ids, spec, dry_run):
    """UPDATE `table` rows in `ids`, restricted to columns that exist."""
    if not ids:
        return {}
    have = existing_columns(conn, table)
    cols = {c: v for c, v in spec.items() if c in have}
    skipped = sorted(set(spec) - set(cols))
    if skipped:
        print(f"  note: {table} has no column(s) {', '.join(skipped)} — skipped")
    if not cols or dry_run:
        return cols
    assignments = ", ".join(f"{c}=?" for c in cols)
    placeholders = ",".join("?" for _ in ids)
    conn.execute(
        f"UPDATE {table} SET {assignments} WHERE id IN ({placeholders})",
        list(cols.values()) + list(ids),
    )
    return cols


def main():
    dry_run = "--dry-run" in sys.argv

    db = os.environ.get("DATABASE_PATH", "").strip()
    if not db:
        sys.exit("DATABASE_PATH is not set. Point it at the live database.")
    if not os.path.exists(db):
        sys.exit(f"DATABASE_PATH does not exist: {db}")

    conn = sqlite3.connect(db)
    conn.row_factory = sqlite3.Row
    try:
        company = conn.execute(
            "SELECT id, name FROM companies WHERE slug=?", (APP_REVIEW_DEMO_SLUG,)
        ).fetchone()
        if not company:
            sys.exit(
                f"No company with slug {APP_REVIEW_DEMO_SLUG!r}. Nothing reset. "
                "Seed the demo tenant first (verify_app_review_demo)."
            )
        company_id = company["id"]
        print(f"Demo tenant: {company['name']} (company_id={company_id})")

        routes = conn.execute(
            "SELECT id, route_name, status FROM routes WHERE company_id=? ORDER BY id",
            (company_id,),
        ).fetchall()
        if not routes:
            sys.exit("Demo tenant has no routes. Nothing to reset.")

        route_ids = [r["id"] for r in routes]
        placeholders = ",".join("?" for _ in route_ids)
        stops = conn.execute(
            f"SELECT id, route_id, status FROM stops WHERE route_id IN ({placeholders})",
            route_ids,
        ).fetchall()
        stop_ids = [s["id"] for s in stops]

        print("\nBefore:")
        for r in routes:
            done = sum(
                1 for s in stops if s["route_id"] == r["id"] and s["status"] == "completed"
            )
            total = sum(1 for s in stops if s["route_id"] == r["id"])
            print(f"  {r['route_name']:<24} {r['status']:<12} {done}/{total} stops completed")

        if dry_run:
            print(f"\n--dry-run: would reset {len(stop_ids)} stop(s), "
                  f"{len(route_ids)} route(s), and delete their route_photos rows.")
            apply_reset(conn, "stops", stop_ids, STOP_RESET, dry_run=True)
            apply_reset(conn, "routes", route_ids, ROUTE_RESET, dry_run=True)
            return

        conn.execute("BEGIN IMMEDIATE")
        photos = 0
        if stop_ids and "route_photos" in {
            r["name"] for r in conn.execute(
                "SELECT name FROM sqlite_master WHERE type='table'"
            )
        }:
            sp = ",".join("?" for _ in stop_ids)
            photos = conn.execute(
                f"SELECT COUNT(*) c FROM route_photos WHERE stop_id IN ({sp})", stop_ids
            ).fetchone()["c"]
            conn.execute(
                f"DELETE FROM route_photos WHERE stop_id IN ({sp})", stop_ids
            )

        apply_reset(conn, "stops", stop_ids, STOP_RESET, dry_run=False)
        apply_reset(conn, "routes", route_ids, ROUTE_RESET, dry_run=False)
        conn.commit()

        after_routes = conn.execute(
            "SELECT id, route_name, status FROM routes WHERE company_id=? ORDER BY id",
            (company_id,),
        ).fetchall()
        after_stops = conn.execute(
            f"SELECT route_id, status FROM stops WHERE route_id IN ({placeholders})",
            route_ids,
        ).fetchall()

        print("\nAfter:")
        for r in after_routes:
            done = sum(
                1 for s in after_stops
                if s["route_id"] == r["id"] and s["status"] == "completed"
            )
            total = sum(1 for s in after_stops if s["route_id"] == r["id"])
            print(f"  {r['route_name']:<24} {r['status']:<12} {done}/{total} stops completed")

        print(f"\nReset {len(stop_ids)} stop(s) across {len(route_ids)} route(s); "
              f"deleted {photos} route_photos row(s).")
        print("Photo files on disk are not removed — only their database rows.")
        print("Every route should now render its pre-flight card with START ROUTE.")
    finally:
        conn.close()


if __name__ == "__main__":
    main()
