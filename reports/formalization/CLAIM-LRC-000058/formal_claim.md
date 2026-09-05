# Formalized Claim: CLAIM-LRC-000058

## Claim Type
Empirical comparative claim (LRC detector success rate and performance characteristics
across five mathematical speed families, 30 configurations each).

## Domain
Dataset: `/Users/trentpalelei/Downloads/Detector___per-family_summary.csv`
SHA-256: `e7553c19ce9061048af54fc64ecbabc704e0658a281cfe522cd4d78f1ea84e42`
Rows: 5 family summaries. Each family: 30 configurations tested.
Total configurations: 150.
Columns: `family, configs, success_rate, median_first_time, q25_first_time,
q75_first_time, median_boundary_count`

## Observed Data (complete dataset)

| family           | configs | success_rate | median_first_time | IQR (q25→q75)        | median_boundary_count |
|------------------|---------|--------------|-------------------|----------------------|-----------------------|
| exact_arithmetic | 30      | 1.0          | 1.4087            | 1.1800 → 1.6667      | 314.5                 |
| fibonacci_ratios | 30      | 1.0          | 0.2917            | 0.2425 → 0.3475      | 1287.0                |
| harmonic_series  | 30      | 1.0          | 1.1000            | 0.4250 → 2.0000      | 359.5                 |
| sqrt_primes      | 30      | 1.0          | 0.6293            | 0.5244 → 0.7866      | 1887.0                |
| transcendental   | 30      | 1.0          | 5.3152            | 2.0670 → 8.5339      | 576.0                 |

## Formal Proposition
Define for each family F:
- `success_rate(F)`: proportion of 30 configurations where the detector succeeds.
- `median_first_time(F)`: median first-detection time across 30 configurations.
- `IQR_first_time(F)`: interquartile range [q25, q75] of first-detection time.
- `median_boundary_count(F)`: median boundary event count across 30 configurations.

Adjudicable statements:
1. success_rate = 1.0 for all five families in this corpus (150/150 configurations).
2. median_first_time ordering in this corpus:
   fibonacci_ratios (0.292) < sqrt_primes (0.629) < harmonic_series (1.100)
   < exact_arithmetic (1.409) < transcendental (5.315).
   Range: ~18.2x between fastest and slowest family.
3. First-time IQR varies substantially by family, indicating family-dependent
   timing variance: fibonacci_ratios (IQR=0.105, tight) vs transcendental
   (IQR=6.467, wide).
4. median_boundary_count ordering in this corpus:
   exact_arithmetic (314.5) < harmonic_series (359.5) < transcendental (576.0)
   < fibonacci_ratios (1287.0) < sqrt_primes (1887.0).
   Range: ~6.0x between lowest and highest family.
5. Boundary count ordering does not correspond to first-time ordering: families
   with low boundary counts (exact_arithmetic, harmonic_series) do not necessarily
   achieve the fastest detection times, indicating boundary count is not the sole
   determinant of detection speed.

## Falsification Rule
Falsified if recomputation from the same source file (SHA-256 above) yields
success_rate < 1.0 for any family, or median_first_time / median_boundary_count
values outside ±1e-06 of those stated in the table above.
