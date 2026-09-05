# Formalized Claim: CLAIM-LRC-000064

## Claim Type
Empirical comparative claim (LRC detector success rate, detection speed, and boundary
count as a function of n, across 50 configurations per n value).

## Domain
Dataset: `/Users/trentpalelei/Downloads/detector_summary_by_n.csv`
SHA-256: `2ff4420e11f156bcb2ec1feb8994e239589d43e43a85ca5a1cb52577aaaab024`
Rows: 3 (n = 4, 5, 6). Each n: 50 configurations tested. Total: 150 configurations.
Columns: `n, configs, success_rate, median_first_time, median_boundary_count`

## Observed Data (complete dataset)

| n | configs | success_rate | median_first_time | median_boundary_count |
|---|---------|--------------|-------------------|-----------------------|
| 4 | 50      | 1.0          | 1.3523391812865497| 432.0                 |
| 5 | 50      | 1.0          | 1.0818713450292399| 664.0                 |
| 6 | 50      | 1.0          | 0.7874434423697448| 1004.0                |

## Formal Proposition
Define for each n in {4, 5, 6}:
- `success_rate(n)`: proportion of 50 configurations where the detector succeeds.
- `median_first_time(n)`: median first-detection time across 50 configurations.
- `median_boundary_count(n)`: median boundary event count across 50 configurations.

Adjudicable statements:
1. success_rate(n) = 1.0 for all n in {4, 5, 6} (150/150 configurations).
2. median_first_time is strictly decreasing with n in this corpus:
   median_first_time(4) = 1.3523 > median_first_time(5) = 1.0819
   > median_first_time(6) = 0.7874.
   Total decrease: ~41.8% from n=4 to n=6.
3. median_boundary_count is strictly increasing with n in this corpus:
   median_boundary_count(4) = 432 < median_boundary_count(5) = 664
   < median_boundary_count(6) = 1004.
   Total increase: ~132.4% from n=4 to n=6.
4. The relationship between median_first_time and median_boundary_count is inverse
   across n: as n increases, detection time decreases while boundary count increases,
   suggesting that higher boundary counts in this corpus correlate with faster
   first detection rather than slower.

## Falsification Rule
Falsified if recomputation from the same source file (SHA-256 above) yields
success_rate < 1.0 for any n, or if the strict ordering of median_first_time
(decreasing) or median_boundary_count (increasing) with n does not hold, or if
any value differs from the table above by more than 1e-06.
