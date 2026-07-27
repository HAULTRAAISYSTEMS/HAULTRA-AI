#!/usr/bin/env python3
"""
Break-glass password reset.

Run this directly on the server (e.g. the Render Shell) when email delivery
is down, RESEND_API_KEY isn't configured, or you need to reset your own boss
account and can't get a reset email. It writes straight to the database using
the same password hashing the app uses everywhere else — no HTTP request,
no token, no email involved.

Usage:
    python3 scripts/reset_password.py <username> <new_password>

Username matching is case-insensitive and whitespace-trimmed, same as login.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from werkzeug.security import generate_password_hash

from app import get_db, now_ts, password_policy_error


def main():
    if len(sys.argv) != 3:
        print("Usage: python3 scripts/reset_password.py <username> <new_password>")
        sys.exit(1)

    username = sys.argv[1].strip()
    new_password = sys.argv[2]

    policy_error = password_policy_error(new_password)
    if policy_error:
        print(policy_error)
        sys.exit(1)

    conn = get_db()
    user = conn.execute(
        "SELECT id, username, role FROM users WHERE username = ? COLLATE NOCASE",
        (username,)
    ).fetchone()

    if not user:
        print(f"No user found matching '{username}'.")
        conn.close()
        sys.exit(1)

    conn.execute(
        "UPDATE users SET password_hash = ? WHERE id = ?",
        (generate_password_hash(new_password), user["id"])
    )
    # Invalidate any outstanding reset-email tokens for this user, since the
    # password is changing out from under them right now.
    conn.execute(
        "UPDATE password_reset_tokens SET used_at = ? WHERE user_id = ? AND used_at IS NULL",
        (now_ts(), user["id"])
    )
    conn.commit()
    conn.close()

    print(f"Password reset for '{user['username']}' (id={user['id']}, role={user['role']}).")


if __name__ == "__main__":
    main()
