# Formalized Claim: CLAIM-LRC-000057

## Claim Type
Empirical comparative claim (boundary-method vs. brute-force LRC isolation: correctness and speedup).

## Domain
Dataset: `/Users/trentpalelei/Downloads/lrc_validation_results.csv`
SHA-256: `230183bfcc95b2ae90ecbfc70a6e0e645b7fb01f1599f2819c3d164292916aa7`
Rows: 100 (excluding header).
Columns: `Case ID, Boundary Isolated, Brute Isolated, Boundary Time, Brute Time, Speedup, Agreement`

## Formal Proposition
Let R be the set of 100 test cases in the dataset.
Define:
- `agreement_rate = #(rows with Agreement=true) / #(rows)`
- `isolation_match_rate = #(rows with Boundary Isolated == Brute Isolated) / #(rows)`
- `speedup_range = [min(Speedup), max(Speedup)]` over all rows
- `mean_speedup = mean(Speedup)` over all rows
- `mean_boundary_time = mean(Boundary Time)` over all rows
- `mean_brute_time = mean(Brute Time)` over all rows

Observed values in this dataset:

| Metric                  | Value                      |
|-------------------------|----------------------------|
| agreement_rate          | 1.0000 (100/100 rows)      |
| isolation_match_rate    | 1.0000 (100/100 rows)      |
| speedup_range           | [3.6894, 11.3043]          |
| mean_speedup            | 6.0566                     |
| mean_boundary_time (ms) | 4.905                      |
| mean_brute_time (ms)    | 28.425                     |
| avg_boundary_isolated   | 7.98                       |
| avg_brute_isolated      | 7.98                       |

Adjudicable statements:
1. The boundary-based isolation method agrees with the brute-force method in every
   test case in this corpus (agreement_rate = 1.0).
2. The boundary method and brute-force method produce identical isolation counts
   in every test case (isolation_match_rate = 1.0).
3. The boundary method is strictly faster than brute-force in every test case, with
   speedup ranging from 3.69x to 11.30x and a mean of 6.06x across 100 cases.
4. Mean runtime for the boundary method (~4.9 ms) is approximately 5.8x lower than
   brute-force (~28.4 ms) on average in this corpus.

## Falsification Rule
This claim is falsified if recomputation from the same source file (verified by SHA-256)
yields agreement_rate < 1.0, isolation_match_rate < 1.0, or mean_speedup outside
[3.0, 15.0] (a generous outer bound allowing for timing variance).
