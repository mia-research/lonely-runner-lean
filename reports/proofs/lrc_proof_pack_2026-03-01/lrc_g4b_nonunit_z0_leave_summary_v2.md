# Non-Unit z=0 Leave-Witness Certifier v2
Date: 2026-03-05

## Scope
- Run-scoped interior obstruction-run exits on `B_div`.
- Event fiber `b*` = first safe fiber after run; `b_prev` = last obstructed fiber.
- Witness: `Leave_e(b*) = B_e(b_prev)\B_e(b*)`; require `Leave\U_-e(b*) != emptyset`.
- Configs: [(6, 'exhaustive', 10, None, 840), (8, 'exhaustive', 11, None, 840), (10, 'sample', 14, 600, 840)]

## Counts
- tuples_seen: 1182
- tuples_in_scope: 197
- components: 197
- runs_total: 357
- runs_interior: 327

## Profile A: all interior non-unit z=0 events
- events: 351
- leave-pass: 254 (72.4%)
- leave-empty: 88 (25.1%)
- implication fails (pass but D*=0): 0

## Profile B: pure non-unit z=0 events (no simultaneous unit z=0 at b*)
- events: 325
- leave-pass: 254 (78.2%)
- leave-empty: 62 (19.1%)
- implication fails (pass but D*=0): 0

## Failure samples (Profile A)
- n=6 E=(1 2 3 6 9) comp=0 run=0 b_prev=5 b*=6 e=9 g=3 |Leave|=0 w=0 D*= 2 unit_z0=0
- n=6 E=(1 2 4 6 8) comp=0 run=1 b_prev=17 b*=18 e=8 g=2 |Leave|=0 w=0 D*= 2 unit_z0=0
- n=6 E=(1 2 4 6 10) comp=0 run=0 b_prev=29 b*=30 e=4 g=2 |Leave|=0 w=0 D*= 2 unit_z0=0
- n=6 E=(1 2 5 6 10) comp=0 run=1 b_prev=23 b*=24 e=10 g=2 |Leave|=0 w=0 D*= 1 unit_z0=1
- n=6 E=(1 2 6 8 10) comp=0 run=1 b_prev=59 b*=60 e=8 g=2 |Leave|=0 w=0 D*= 2 unit_z0=0
- n=6 E=(1 3 4 6 9) comp=0 run=0 b_prev=11 b*=12 e=9 g=3 |Leave|=0 w=0 D*= 1 unit_z0=0
- n=6 E=(1 3 5 6 9) comp=0 run=0 b_prev=29 b*=30 e=9 g=3 |Leave|=0 w=0 D*= 1 unit_z0=0
- n=6 E=(1 3 6 7 9) comp=0 run=0 b_prev=41 b*=42 e=9 g=3 |Leave|=0 w=0 D*= 1 unit_z0=0
- n=6 E=(1 3 6 8 9) comp=0 run=0 b_prev=23 b*=24 e=9 g=3 |Leave|=0 w=0 D*= 1 unit_z0=0
- n=6 E=(1 3 6 9 10) comp=0 run=0 b_prev=29 b*=30 e=9 g=3 |Leave|=0 w=0 D*= 1 unit_z0=0

## Failure samples (Profile B)
- n=6 E=(1 2 3 6 9) comp=0 run=0 b_prev=5 b*=6 e=9 g=3 |Leave|=0 w=0 D*= 2
- n=6 E=(1 2 4 6 8) comp=0 run=1 b_prev=17 b*=18 e=8 g=2 |Leave|=0 w=0 D*= 2
- n=6 E=(1 2 4 6 10) comp=0 run=0 b_prev=29 b*=30 e=4 g=2 |Leave|=0 w=0 D*= 2
- n=6 E=(1 2 6 8 10) comp=0 run=1 b_prev=59 b*=60 e=8 g=2 |Leave|=0 w=0 D*= 2
- n=6 E=(1 3 4 6 9) comp=0 run=0 b_prev=11 b*=12 e=9 g=3 |Leave|=0 w=0 D*= 1
- n=6 E=(1 3 5 6 9) comp=0 run=0 b_prev=29 b*=30 e=9 g=3 |Leave|=0 w=0 D*= 1
- n=6 E=(1 3 6 7 9) comp=0 run=0 b_prev=41 b*=42 e=9 g=3 |Leave|=0 w=0 D*= 1
- n=6 E=(1 3 6 8 9) comp=0 run=0 b_prev=23 b*=24 e=9 g=3 |Leave|=0 w=0 D*= 1
- n=6 E=(1 3 6 9 10) comp=0 run=0 b_prev=29 b*=30 e=9 g=3 |Leave|=0 w=0 D*= 1
- n=6 E=(1 4 6 8 9) comp=0 run=1 b_prev=53 b*=54 e=8 g=2 |Leave|=0 w=0 D*= 1
