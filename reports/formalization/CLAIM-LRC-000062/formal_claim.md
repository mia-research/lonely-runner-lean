# Formalized Claim: CLAIM-LRC-000062

## Claim Type
Empirical comparative claim (boundary set detection vs. coarse midpoint detection:
correctness, miss rate, and witness time comparison across 1,200 trials at n=10).

## Domain
Dataset: `/Users/trentpalelei/Downloads/boundary_set_vs_coarse_midpoint_n10.csv`
SHA-256: `98b5f1bef13cb0097234a2936f299491966ac123b2afebadbf9e82c346c17897`
Rows: 1,200. Structure: 120 config IDs × 10 runners. Fixed: n=10, T=100.0, threshold=0.1.
Columns: `config_id, runner, n, T, threshold, boundary_detect, boundary_witness_time,
coarse_detect, coarse_witness_time, miss_due_to_coarse, speeds`

## Observed Statistics (computed from full dataset)

| Metric                          | Value                        |
|---------------------------------|------------------------------|
| Total rows                      | 1,200                        |
| boundary_detect=True            | 1200 / 1200 (1.0000)         |
| coarse_detect=True              | 1200 / 1200 (1.0000)         |
| miss_due_to_coarse=True         | 0 / 1200 (0.0000)            |
| boundary_only (bd=T, cd=F)      | 0                            |
| boundary_witness_time: min      | 2.5313                       |
| boundary_witness_time: max      | 13.7412                      |
| boundary_witness_time: mean     | 7.7033                       |
| coarse_witness_time: min        | 1.4167                       |
| coarse_witness_time: max        | 12.4167                      |
| coarse_witness_time: mean       | 6.8667                       |

## Formal Proposition
Define over all 1,200 rows (120 config IDs × 10 runners, n=10, T=100.0, threshold=0.1):
- `detect_rate(method)`: proportion of rows where the method detects the target.
- `miss_rate`: proportion of rows where coarse misses but boundary detects
  (miss_due_to_coarse=True).
- `mean_witness_time(method)`: mean witness time across all rows.

Adjudicable statements:
1. detect_rate(boundary) = 1.0000 — boundary method detects in all 1,200 trials.
2. detect_rate(coarse) = 1.0000 — coarse midpoint method detects in all 1,200 trials.
3. miss_rate = 0.0000 — the coarse method produces zero misses relative to the
   boundary method in this corpus (miss_due_to_coarse=False for all 1,200 rows).
4. mean_witness_time(coarse) = 6.8667 < mean_witness_time(boundary) = 7.7033;
   coarse method is on average ~10.9% faster than the boundary method in this corpus.
5. The coarse midpoint method matches the boundary set method on both detection
   outcome and miss rate at n=10, T=100.0, threshold=0.1, while achieving
   faster mean witness time.

## Float Precision Note
max_rel_float64_vs_mpmath = 2.045e-10 — the highest float64 error in this
cycle's claim set. Still within the stable threshold (1e-09) but closer than
all other claims. Decimal128 error (2.433e-32) remains excellent.

## Falsification Rule
Falsified if recomputation from the same source file (SHA-256 above) yields
boundary_detect or coarse_detect rate < 1.0, miss_due_to_coarse count > 0,
mean_witness_time values outside ±1e-03 of stated means (timing variance
allowance), or float64 error exceeding the stable threshold of 1e-09.
