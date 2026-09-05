# Formalized Claim: CLAIM-LRC-000056

## Claim Type
Empirical comparative claim (phase-match exclusivity and isolation behavior by speed family).

## Domain
Dataset: `/Users/trentpalelei/Downloads/lrc_validation_large_1759239075705.csv`
SHA-256: `99b30d585e6378f834d3357efef71ec14852fee04e01ecbb52e86a5d52c00139`
Rows: 220,110 (excluding header). Columns used: `family, n, phi_n, unique_phases, phi_match, isolation_count, boundary_count`.

## Formal Proposition
Let `R` be the set of rows in the dataset grouped by family `F in {arithmetic, geometric, perturbed, random}`.
Define:
- `phi_match_rate(F) = #(rows in F with phi_match=YES) / #(rows in F)`
- `phase_eq_rate(F) = #(rows in F with unique_phases == phi_n) / #(rows in F)`
- `isolation_rate(F) = #(rows in F with isolation_count > 0) / #(rows in F)`
- `avg_isolation(F) = mean(isolation_count) over rows in F`

Observed values in this dataset:

NOTE: `unique_phases` is derived from isolated boundary points (requires isolation_count > 0).
Across all 220,110 rows, the bijection holds perfectly:
  isolation_count > 0  ↔  unique_phases non-empty  ↔  first_isolation non-empty
Arithmetic: isolation_count > 0 for all rows → unique_phases and phi_match computable.
Geometric/random/perturbed: isolation_count = 0 for ALL rows → unique_phases = '' → phi_match
not derivable from phase count. Perturbed receives phi_match='NO' explicitly (tested as
near-arithmetic candidate, fails due to zero isolation); geometric/random have phi_match=''
(outside scope of the isolation-based phase measurement).

| family     | rows   | phi_match status        | phase_eq_rate | avg_boundary | avg_isolation |
|------------|--------|-------------------------|---------------|--------------|---------------|
| arithmetic | 55,000 | YES (all rows)          | 1.0000        | 158.8        | 19.3          |
| geometric  | 55,000 | N/A (not computed)      | N/A           | 478.8        | 0.0           |
| perturbed  | 55,110 | NO (all rows, measured) | N/A           | 429.8        | 0.0           |
| random     | 55,000 | N/A (not computed)      | N/A           | 1015.2       | 0.0           |

n range: {5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}
phi_n range: {2, 4, 6, 8, 10, 12}

Adjudicable statements:
1. In this corpus, `phi_match=YES` and `unique_phases == phi_n` occur exclusively and
   universally within the arithmetic family (rate = 1.0 over all 55,000 arithmetic rows).
2a. The perturbed family has phi_match explicitly computed and returns `NO` for all
    55,110 rows; `unique_phases` is empty (phase count not extracted), confirming
    perturbation disrupts the phi(n)-phase structure.
2b. The geometric and random families have phi_match and unique_phases columns empty
    (not computed by the pipeline) — the phi(n)-phase test is not applied to these
    families. These families cannot be scored as phi_match=0.0; they are outside the
    scope of the phi_match measurement.
3. Non-zero `isolation_count` is exclusive to the arithmetic family in this corpus;
   all other families (geometric, perturbed, random) report `isolation_count = 0` for
   every row. This is the mechanistic reason unique_phases is unmeasurable for non-arithmetic
   families: no isolated boundary points exist to define phase boundaries.
4. Arithmetic sequences exhibit the lowest average `boundary_count` (158.8), while
   random speed sequences exhibit the highest (1015.2). Geometric sequences produce
   more boundary crossings than arithmetic at every n tested (e.g. mean 47.2 vs 27.1
   at n=5; 1229.9 vs 358.3 at n=15) but none generate isolation events, indicating
   their boundary structure is topologically connected rather than phase-isolated.

## Falsification Rule
This claim is falsified if recomputation from the same source file (verified by SHA-256)
yields any arithmetic row with phi_match ≠ YES or unique_phases ≠ phi_n, any perturbed
row with phi_match ≠ NO, any geometric or random row with phi_match ≠ '' (i.e., the
pipeline begins computing phi_match for these families), avg_isolation for arithmetic
outside ±0.1 of 19.3, or avg_boundary values outside ±1.0 of stated means.

## Correction Note (2026-02-28)
Previous version incorrectly stated phi_match_rate=0.0 for geometric and random
families. Actual values: geometric and random have phi_match='' (column not populated,
test not applied). Perturbed has phi_match='NO' (test applied, explicit negative).
The binary split (arithmetic=1.0, non-arithmetic=0.0) overstated the finding.
The correct finding is a three-way structure: arithmetic=YES, perturbed=NO,
geometric/random=not measured.
