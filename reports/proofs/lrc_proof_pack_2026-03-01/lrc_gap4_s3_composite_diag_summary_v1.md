# Gap 4 / S3 Composite-n Diagnostic (v1)

## Purpose
Probe the structure of non-obstructed fibers for composite n in Case-2,
looking for patterns that could support an analytic proof.

## Key Metrics
- `good_anchors`: #{j in {0,...,n-1}: b_j in B_div AND z_e=1 for all e in E_non}
- `good_nontrivial_safe`: #{j>=1 good anchors with delta(b_j)>0}
- `max_obstr_run`: longest consecutive obstructed block in B_div walk
- `n_safe_runs`: number of connected safe regions in B_div
- `tight`: B_safe = n-1 exactly

## Exhaustive Results

### exhaustive_composite_n4 (n=4)
- Tuples processed: 330
- viol(x0 >= n-1): 0
- viol(B_safe >= n-1): 0
- Tight (B_safe = n-1): 12
- good_anchors = 0 (no good anchor): 0
- min x0: 4  at E=1 2 4
- min B_safe: 3  at E=1 1 4
- min good_anchors: 2  at E=1 1 8
- min good_nontrivial_safe (j>=1 anchors that are good AND safe): 0  at E=1 7 8
- min max_obstr_run: 0  at E=1 1 4

### exhaustive_composite_n6 (n=6)
- Tuples processed: 15150
- viol(x0 >= n-1): 0
- viol(B_safe >= n-1): 0
- Tight (B_safe = n-1): 720
- good_anchors = 0 (no good anchor): 0
- min x0: 10  at E=1 2 3 4 6
- min B_safe: 5  at E=1 1 1 1 6
- min good_anchors: 2  at E=1 1 2 3 6
- min good_nontrivial_safe (j>=1 anchors that are good AND safe): 0  at E=1 2 3 5 6
- min max_obstr_run: 0  at E=1 1 1 1 6

### exhaustive_prime_n5 (n=5)
- Tuples processed: 1104
- viol(x0 >= n-1): 0
- viol(B_safe >= n-1): 0
- Tight (B_safe = n-1): 14
- good_anchors = 0 (no good anchor): 0
- min x0: 8  at E=1 3 4 5
- min B_safe: 4  at E=1 1 1 5
- min good_anchors: 4  at E=1 1 1 5
- min good_nontrivial_safe (j>=1 anchors that are good AND safe): 2  at E=1 2 3 5
- min max_obstr_run: 0  at E=1 1 1 5

### exhaustive_prime_n7 (n=7)
- Tuples processed: 70992
- viol(x0 >= n-1): 0
- viol(B_safe >= n-1): 0
- Tight (B_safe = n-1): 62
- good_anchors = 0 (no good anchor): 0
- min x0: 30  at E=1 1 1 1 1 7
- min B_safe: 6  at E=1 1 1 1 1 7
- min good_anchors: 6  at E=1 1 1 1 1 7
- min good_nontrivial_safe (j>=1 anchors that are good AND safe): 2  at E=1 1 3 4 5 7
- min max_obstr_run: 0  at E=1 1 1 1 1 7

## Random Stress Results

### random_n8 (n=8)
- Tuples processed: 300
- viol(x0 >= n-1): 0
- viol(B_safe >= n-1): 0
- Tight (B_safe = n-1): 0
- good_anchors = 0 (no good anchor): 0
- min x0: 46  at E=3 12 8 12 1 4 2
- min B_safe: 19  at E=1 12 3 12 1 3 8
- min good_anchors: 4  at E=12 9 7 4 8 10 5
- min good_nontrivial_safe (j>=1 anchors that are good AND safe): 2  at E=1 4 10 2 2 12 8
- min max_obstr_run: 0  at E=3 9 12 4 3 8 7

### random_n9 (n=9)
- Tuples processed: 300
- viol(x0 >= n-1): 0
- viol(B_safe >= n-1): 0
- Tight (B_safe = n-1): 0
- good_anchors = 0 (no good anchor): 0
- min x0: 116  at E=4 2 2 2 6 1 9 4
- min B_safe: 29  at E=4 2 2 2 6 1 9 4
- min good_anchors: 6  at E=2 12 14 5 6 9 7 9
- min good_nontrivial_safe (j>=1 anchors that are good AND safe): 2  at E=12 9 7 3 5 2 6 1
- min max_obstr_run: 0  at E=2 12 14 5 6 9 7 9

### random_n10 (n=10)
- Tuples processed: 250
- viol(x0 >= n-1): 0
- viol(B_safe >= n-1): 0
- Tight (B_safe = n-1): 0
- good_anchors = 0 (no good anchor): 0
- min x0: 100  at E=10 2 1 3 5 6 2 1 10
- min B_safe: 25  at E=10 6 6 2 6 2 3 3 10
- min good_anchors: 4  at E=12 9 11 5 4 12 10 10 2
- min good_nontrivial_safe (j>=1 anchors that are good AND safe): 2  at E=5 14 2 9 12 10 8 3 2
- min max_obstr_run: 0  at E=12 9 11 5 4 12 10 10 2

### random_n12 (n=12)
- Tuples processed: 200
- viol(x0 >= n-1): 0
- viol(B_safe >= n-1): 0
- Tight (B_safe = n-1): 0
- good_anchors = 0 (no good anchor): 0
- min x0: 184  at E=3 12 1 1 1 6 4 12 3 9 6
- min B_safe: 31  at E=3 12 1 1 1 6 4 12 3 9 6
- min good_anchors: 4  at E=12 9 3 3 4 1 10 6 9 7 3
- min good_nontrivial_safe (j>=1 anchors that are good AND safe): 2  at E=7 9 4 7 8 6 10 12 1 2 8
- min max_obstr_run: 0  at E=8 3 1 12 3 2 14 8 13 1 8

## Analytic Hypotheses Check

Based on above data:

### Route A (good non-trivial anchors cover n-1 by themselves)
- Tuples where good_nontrivial_safe >= n-1: 62390 / 88626
- Composite n tuples: 16530

### Cases with good_nontrivial_safe = 0
- Count: 858
  - n=4, E=1 7 8, L=56, B_safe=16, x0=16
  - n=4, E=1 8 7, L=56, B_safe=16, x0=16
  - n=4, E=1 8 9, L=72, B_safe=24, x0=24
  - n=4, E=1 9 8, L=72, B_safe=24, x0=24
  - n=4, E=3 5 8, L=120, B_safe=32, x0=32
  - n=4, E=3 8 5, L=120, B_safe=32, x0=32
  - n=4, E=5 3 8, L=120, B_safe=32, x0=32
  - n=4, E=5 8 3, L=120, B_safe=32, x0=32
  - n=4, E=7 1 8, L=56, B_safe=16, x0=16
  - n=4, E=7 8 1, L=56, B_safe=16, x0=16

### Obstruction block structure (composite n)
- max(max_obstr_run): 1079
- mean(max_obstr_run): 13.0
- Tuples with max_obstr_run > B_div - (n-1):
  Count: 0

### Tight tuples (B_safe = n-1)
- Total tight tuples: 808
  - n=4_L=n: 12
  - n=5_L=n: 14
  - n=6_L=n: 720
  - n=7_L=n: 62

