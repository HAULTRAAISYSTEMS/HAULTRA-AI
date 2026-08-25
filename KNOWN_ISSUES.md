# Known Issues

## Date-dependent time-off regression test

`tests/test_time_off.py` can fail at “override flips that one date to working,
rest unchanged” when its generated recurring occurrence overlaps the separate
one-time absence created earlier in the same test. The behavior predates this
branch and reproduces unchanged on commit `31912f5`. It is intentionally not
fixed as part of the account-deletion and App Review demo work.
