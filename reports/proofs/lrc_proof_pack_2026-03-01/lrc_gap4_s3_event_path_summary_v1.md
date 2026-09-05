# Gap 4 / S3 — Event-Cell Path Diagnostic (v1)

## Conjecture Tested
**Complementarity Bound (CB):** max_obstr_run ≤ B_div − n for all L>n tuples.

## Hypotheses
- H1: n_safe_cells ≥ n (L>n tuples)
- H2: max_obstr_run ≤ min(L/e − 1 : e ∈ E_non)
- H4: period_bound_slack = (B_div − n + 1) − max(L/e) ≥ 0

## Exhaustive Results

### exhaustive_composite_n4 (n=4, phi=2)
- Tuples processed (L>n): 318
- CB violations (max_obstr_run > B_div−n):  0
- H1 failures (n_safe_cells < n):           102
- H2 failures (max_obstr > min_period−1):   0
- H4 failures (period_bound_slack < 0):     132
- Tight CB cases (max_obstr_run = B_div−n): 6
- min B_safe:              4  at E=1 3 4
- min n_safe_cells:        1  at E=1 1 8
- min period_bound_slack:  -37  at E=1 8 9
- max max_obstr_fiber_run: 42  at E=7 8 9
- max max_obstr_cell_run:  1  at E=1 4 7

### exhaustive_composite_n6 (n=6, phi=2)
- Tuples processed (L>n): 14430
- CB violations (max_obstr_run > B_div−n):  0
- H1 failures (n_safe_cells < n):           990
- H2 failures (max_obstr > min_period−1):   1920
- H4 failures (period_bound_slack < 0):     6600
- Tight CB cases (max_obstr_run = B_div−n): 0
- min B_safe:              9  at E=1 1 1 4 6
- min n_safe_cells:        4  at E=1 1 1 4 6
- min period_bound_slack:  -284  at E=1 5 6 7 8
- max max_obstr_fiber_run: 359  at E=1 5 6 7 8
- max max_obstr_cell_run:  7  at E=1 5 6 7 8

### exhaustive_prime_n5 (n=5, phi=4)
- Tuples processed (L>n): 1090
- CB violations (max_obstr_run > B_div−n):  0
- H1 failures (n_safe_cells < n):           536
- H2 failures (max_obstr > min_period−1):   96
- H4 failures (period_bound_slack < 0):     470
- Tight CB cases (max_obstr_run = B_div−n): 0
- min B_safe:              7  at E=1 1 2 5
- min n_safe_cells:        2  at E=1 1 2 5
- min period_bound_slack:  -87  at E=1 5 6 7
- max max_obstr_fiber_run: 69  at E=1 5 6 7
- max max_obstr_cell_run:  3  at E=1 3 4 5

### exhaustive_prime_n7 (n=7, phi=6)
- Tuples processed (L>n): 70930
- CB violations (max_obstr_run > B_div−n):  0
- H1 failures (n_safe_cells < n):           25570
- H2 failures (max_obstr > min_period−1):   6480
- H4 failures (period_bound_slack < 0):     39962
- Tight CB cases (max_obstr_run = B_div−n): 0
- min B_safe:              11  at E=1 1 1 1 2 7
- min n_safe_cells:        2  at E=1 1 1 1 2 7
- min period_bound_slack:  -125  at E=1 1 3 4 5 7
- max max_obstr_fiber_run: 251  at E=1 2 3 4 5 7
- max max_obstr_cell_run:  7  at E=1 2 3 4 5 7

## Random Stress Results

### random_n8 (n=8, phi=4)
- Tuples processed (L>n): 300
- CB violations (max_obstr_run > B_div−n):  0
- H1 failures (n_safe_cells < n):           3
- H2 failures (max_obstr > min_period−1):   52
- H4 failures (period_bound_slack < 0):     133
- Tight CB cases (max_obstr_run = B_div−n): 0
- min B_safe:              19  at E=1 12 3 12 1 3 8
- min n_safe_cells:        6  at E=8 4 3 2 1 5 7
- min period_bound_slack:  -636  at E=9 8 8 2 10 1 7
- max max_obstr_fiber_run: 503  at E=8 2 3 5 1 7 6
- max max_obstr_cell_run:  9  at E=8 2 3 5 1 7 6

### random_n9 (n=9, phi=6)
- Tuples processed (L>n): 300
- CB violations (max_obstr_run > B_div−n):  0
- H1 failures (n_safe_cells < n):           3
- H2 failures (max_obstr > min_period−1):   32
- H4 failures (period_bound_slack < 0):     147
- Tight CB cases (max_obstr_run = B_div−n): 0
- min B_safe:              29  at E=4 2 2 2 6 1 9 4
- min n_safe_cells:        8  at E=2 7 9 1 1 7 2 1
- min period_bound_slack:  -623  at E=14 11 2 7 12 6 9 1
- max max_obstr_fiber_run: 1079  at E=4 1 5 7 9 8 6 1
- max max_obstr_cell_run:  9  at E=4 1 5 7 9 8 6 1

### random_n10 (n=10, phi=4)
- Tuples processed (L>n): 250
- CB violations (max_obstr_run > B_div−n):  0
- H1 failures (n_safe_cells < n):           1
- H2 failures (max_obstr > min_period−1):   22
- H4 failures (period_bound_slack < 0):     133
- Tight CB cases (max_obstr_run = B_div−n): 0
- min B_safe:              25  at E=10 6 6 2 6 2 3 3 10
- min n_safe_cells:        6  at E=10 6 6 2 6 2 3 3 10
- min period_bound_slack:  -554  at E=5 1 13 10 10 6 14 2 3
- max max_obstr_fiber_run: 524  at E=4 8 10 8 1 6 9 2 7
- max max_obstr_cell_run:  5  at E=5 14 2 9 12 10 8 3 2

### random_n12 (n=12, phi=4)
- Tuples processed (L>n): 200
- CB violations (max_obstr_run > B_div−n):  0
- H1 failures (n_safe_cells < n):           1
- H2 failures (max_obstr > min_period−1):   0
- H4 failures (period_bound_slack < 0):     130
- Tight CB cases (max_obstr_run = B_div−n): 0
- min B_safe:              31  at E=3 12 1 1 1 6 4 12 3 9 6
- min n_safe_cells:        10  at E=2 5 12 3 12 4 12 4 1 12 3
- min period_bound_slack:  -472  at E=1 6 1 3 12 9 11 2 11 11 7
- max max_obstr_fiber_run: 174  at E=4 3 1 12 4 2 10 8 9 14 10
- max max_obstr_cell_run:  3  at E=1 6 1 4 12 4 8 5 7 10 9

## Global Summary
- Total L>n tuples: 87818
- CB violations:    0
- H1 failures:      27206
- H2 failures:      8602
- H4 failures:      47707
- Tight CB cases:   6

### Obstructed-run termination types
  - z0_event: 21625 (95.2%)
  - at_B_div_end: 1090 (4.8%)

### n_safe_cells distribution
  n=4: min=1, max=9, mean=4.7, #(< n)=102
  n=5: min=2, max=9, mean=5.0, #(< n)=536
  n=6: min=4, max=16, mean=8.3, #(< n)=990
  n=7: min=2, max=12, mean=7.7, #(< n)=25570
  n=8: min=6, max=30, mean=18.5, #(< n)=3
  n=9: min=8, max=30, mean=20.1, #(< n)=3
  n=10: min=6, max=34, mean=22.3, #(< n)=1
  n=12: min=10, max=34, mean=25.6, #(< n)=1

### period_bound_slack distribution
  min=-636, max=1604, mean=2.6
  negative count: 47707

### Tight CB cases (max_obstr_run = B_div−n)
  n=4, E=1 3 4, L=12, B_div=7, B_safe=4, max_obstr_run=3, n_safe_cells=3, min_period=4
  n=4, E=1 4 3, L=12, B_div=7, B_safe=4, max_obstr_run=3, n_safe_cells=3, min_period=4
  n=4, E=3 1 4, L=12, B_div=7, B_safe=4, max_obstr_run=3, n_safe_cells=3, min_period=4
  n=4, E=3 4 1, L=12, B_div=7, B_safe=4, max_obstr_run=3, n_safe_cells=3, min_period=4
  n=4, E=4 1 3, L=12, B_div=7, B_safe=4, max_obstr_run=3, n_safe_cells=3, min_period=4
  n=4, E=4 3 1, L=12, B_div=7, B_safe=4, max_obstr_run=3, n_safe_cells=3, min_period=4
