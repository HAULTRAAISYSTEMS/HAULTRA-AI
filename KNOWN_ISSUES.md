# Known Issues

None currently open.

## Resolved

### Date-dependent time-off regression test

`tests/test_time_off.py` failed at "override flips that one date to working,
rest unchanged" on certain weekdays. Two independent fixture collisions, not a
product defect -- the override behaviour is correct in isolation:

- the one-time absences sat at `today+20/+21`, which lands exactly on the second
  projected recurring Monday whenever today is a Monday, so a separate absence
  still covered the date the override had cleared;
- the weekly-hours assertion read `days[0]`, which is today when the workweek
  starts on a Monday, and an earlier section of the same file clocks the driver
  in — so the OFF row was correctly suppressed for a day that had been worked.

Both now pick dates that cannot collide. A permanently red suite is worse than
no suite: it trains everyone to merge without looking, which is how a bad
dependency pin reached production during this work.
