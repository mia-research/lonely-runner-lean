# Non-Unit z0 Event Partition Summary v3
Date: 2026-03-05

## Definitions
- Event key: `(n, tuple_id, component_id, run_id, b_star)` for interior run exits.
- Candidate set: non-unit z0 runners at `b_star` from v2 rows.
- Existential pass: `exists candidate e with leave_pass(e)=1`.

## Counts
- all events with non-unit candidates: 257
- pure_nonunit events: 231
- mixed_unit_nonunit events: 26

## Results
| Class | Events | Existential Pass | Rate | All-Fail | All-Leave-Empty | Any-Snatch-Fail |
|---|---:|---:|---:|---:|---:|---:|
| all | 257 | 231 | 89.9% | 26 | 26 | 9 |
| pure_nonunit | 231 | 231 | 100.0% | 0 | 0 | 9 |
| mixed_unit_nonunit | 26 | 0 | 0.0% | 26 | 26 | 0 |

## Interpretation
- Pure non-unit exits isolate the non-unit mechanism.
- Mixed exits should be routed to the unit-z0 already-proved branch when non-unit candidate is non-causal (`leave_empty`).

## Mixed all-fail samples
- n=6 E=(1 2 5 6 10) b*=24 run=[22,23] unit_z0=1 nonunit_ct=1 first_fail=e=10,g=2,leave=0
- n=6 E=(1 4 5 6 10) b*=36 run=[25,35] unit_z0=1 nonunit_ct=1 first_fail=e=10,g=2,leave=0
- n=6 E=(1 4 5 6 10) b*=48 run=[46,47] unit_z0=1 nonunit_ct=1 first_fail=e=10,g=2,leave=0
- n=6 E=(1 5 6 7 10) b*=84 run=[61,83] unit_z0=1 nonunit_ct=1 first_fail=e=10,g=2,leave=0
- n=6 E=(1 5 6 8 10) b*=72 run=[49,71] unit_z0=1 nonunit_ct=1 first_fail=e=10,g=2,leave=0
- n=6 E=(2 5 6 7 10) b*=84 run=[64,83] unit_z0=1 nonunit_ct=1 first_fail=e=10,g=2,leave=0
- n=6 E=(2 5 6 7 10) b*=168 run=[151,167] unit_z0=1 nonunit_ct=1 first_fail=e=10,g=2,leave=0
- n=6 E=(4 5 6 7 10) b*=336 run=[316,335] unit_z0=1 nonunit_ct=1 first_fail=e=10,g=2,leave=0
- n=8 E=(1 2 3 4 5 6 8) b*=80 run=[73,79] unit_z0=1 nonunit_ct=1 first_fail=e=6,g=2,leave=0
- n=8 E=(1 2 3 5 6 8 9) b*=240 run=[217,239] unit_z0=2 nonunit_ct=1 first_fail=e=6,g=2,leave=0
- n=8 E=(1 2 3 5 6 8 10) b*=48 run=[37,47] unit_z0=1 nonunit_ct=1 first_fail=e=10,g=2,leave=0
- n=8 E=(1 2 3 5 7 8 10) b*=504 run=[337,503] unit_z0=1 nonunit_ct=1 first_fail=e=10,g=2,leave=0
