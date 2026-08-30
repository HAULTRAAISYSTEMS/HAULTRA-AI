#!/usr/bin/env python3
"""Clear leftover Play Store review fixtures out of the App Review demo tenant.

The Google Play review round left accounts (google-review*) and at least one
route ("App Review Route") in the reserved demo company. They are not recreated
by verify_app_review_demo -- it only knows the three APP_REVIEW_* accounts and
the three "Review <name> Route" routes -- so once cleared they stay cleared.

Reports by default and changes nothing. Pass --apply to act.

    DATABASE_PATH=... python3 scripts/cleanup_play_store_fixtures.py
    DATABASE_PATH=... python3 scripts/cleanup_play_store_fixtures.py --apply

Accounts are retired through the app's own _anonymize_user_account(), not a
DELETE: several historical foreign keys onto users are NOT NULL, so the row has
to survive as a non-identifying tombstone. The account ends up inactive, with a
"deleted-<role>-..." username, so nothing reads as a Play Store fixture.

Routes are removed with the same stops-then-route delete the boss-facing route
delete uses.

Refuses to touch the three live APP_REVIEW_* accounts, and is scoped to the
reserved demo company throughout. Idempotent.

Importing app.py runs its normal startup (schema migrations plus one
verify_app_review_demo repair pass) against DATABASE_PATH -- the same work any
boot does, and it will not resurrect anything this removes.
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import app as haultra  # noqa: E402  (import after sys.path fix)

# Routes verify_app_review_demo() owns. Anything else in the demo company is a
# leftover fixture.
SEEDED_ROUTES = (
    "Review North Route",
    "Review Central Route",
    "Review Harbor Route",
)

FIXTURE_USERNAME_PREFIX = "google-review"


def live_usernames():
    return {
        os.environ.get(name, "").strip().casefold()
        for name in (
            "APP_REVIEW_BOSS_USERNAME",
            "APP_REVIEW_DRIVER_USERNAME",
            "APP_REVIEW_DELETE_USERNAME",
        )
        if os.environ.get(name, "").strip()
    }


def main():
    apply_changes = "--apply" in sys.argv

    conn = haultra.get_db()
    try:
        company = conn.execute(
            "SELECT * FROM companies WHERE slug=?", (haultra.APP_REVIEW_DEMO_SLUG,)
        ).fetchone()
        if not company:
            sys.exit(
                f"No company with slug {haultra.APP_REVIEW_DEMO_SLUG!r}. Nothing to clean."
            )
        company_id = company["id"]
        print(f"Demo tenant: {company['name']} (company_id={company_id})\n")

        protected = live_usernames()
        if not protected:
            sys.exit(
                "APP_REVIEW_*_USERNAME env vars are not set. Refusing to run without "
                "knowing which accounts are live."
            )

        users = [
            u for u in conn.execute(
                "SELECT * FROM users WHERE company_id=? AND lower(username) LIKE ?",
                (company_id, FIXTURE_USERNAME_PREFIX + "%"),
            ).fetchall()
            if u["username"].strip().casefold() not in protected
        ]

        routes = conn.execute(
            "SELECT * FROM routes WHERE company_id=? AND route_name NOT IN (?,?,?) "
            "ORDER BY id",
            (company_id, *SEEDED_ROUTES),
        ).fetchall()

        print(f"Fixture accounts ({FIXTURE_USERNAME_PREFIX}*): {len(users)}")
        for u in users:
            print(f"  id={u['id']:<5} {u['username']:<28} role={u['role']:<9} "
                  f"active={u['is_active']}")

        print(f"\nNon-seeded routes: {len(routes)}")
        for r in routes:
            n = conn.execute(
                "SELECT COUNT(*) c FROM stops WHERE route_id=?", (r["id"],)
            ).fetchone()["c"]
            print(f"  id={r['id']:<5} {r['route_name']:<28} status={r['status']:<12} "
                  f"{n} stop(s)")

        print(f"\nProtected, never touched: {', '.join(sorted(protected))}")
        print(f"Seeded routes kept: {', '.join(SEEDED_ROUTES)}")

        if not users and not routes:
            print("\nNothing to clean.")
            return

        if not apply_changes:
            print("\nReport only. Re-run with --apply to make these changes.")
            return

        conn.execute("BEGIN IMMEDIATE")
        for u in users:
            haultra._anonymize_user_account(conn, u, company)
            conn.execute("UPDATE users SET is_active=0 WHERE id=?", (u["id"],))
        stops_removed = 0
        for r in routes:
            stops_removed += conn.execute(
                "SELECT COUNT(*) c FROM stops WHERE route_id=?", (r["id"],)
            ).fetchone()["c"]
            conn.execute("DELETE FROM stops WHERE route_id=?", (r["id"],))
            conn.execute(
                "DELETE FROM routes WHERE id=? AND company_id=?", (r["id"], company_id)
            )
        conn.commit()

        print(f"\nRetired {len(users)} account(s); deleted {len(routes)} route(s) "
              f"and {stops_removed} stop(s).")

        left = conn.execute(
            "SELECT COUNT(*) c FROM users WHERE company_id=? AND lower(username) LIKE ?",
            (company_id, FIXTURE_USERNAME_PREFIX + "%"),
        ).fetchone()["c"]
        remaining = conn.execute(
            "SELECT route_name FROM routes WHERE company_id=? ORDER BY id", (company_id,)
        ).fetchall()
        print(f"Remaining {FIXTURE_USERNAME_PREFIX}* accounts: {left}")
        print("Remaining routes: " + ", ".join(r["route_name"] for r in remaining))
    finally:
        conn.close()


if __name__ == "__main__":
    main()
