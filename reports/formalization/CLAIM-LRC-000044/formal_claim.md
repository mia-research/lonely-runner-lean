# Formalized Claim: CLAIM-LRC-000044

## Claim Type
Empirical comparative claim (detector efficiency and phase-match behavior by speed family).

## Domain
Dataset: `/Users/trentpalelei/Downloads/lrc_efficiency_runtime_validation.csv`
Columns used: `family, n, seed, phi, boundary_count, isolation_count, detected_phases, efficiency, runtime_ms, phi_match`.

## Formal Proposition
Let `R` be the set of rows in the dataset grouped by family `F in {arithmetic, geometric, harmonic, quadratic}`.
Define:
- `phi_match_rate(F) = #(rows in F with phi_match=true) / #(rows in F)`
- `eff_range(F) = [min(efficiency), max(efficiency)]` over rows in `F`.

Observed values in this dataset:
- arithmetic: `phi_match_rate = 2/96 = 0.0208`, `eff_range = [0.108341, 0.444233]`
- geometric: `phi_match_rate = 96/96 = 1.0000`, `eff_range = [0.910448, 0.999900]`
- harmonic: `phi_match_rate = 96/96 = 1.0000`, `eff_range = [0.933415, 0.999900]`
- quadratic: `phi_match_rate = 96/96 = 1.0000`, `eff_range = [0.943556, 0.999905]`

Adjudicable statement:
1. Non-arithmetic families (`geometric`, `harmonic`, `quadratic`) exhibit near-universal phase-match in this corpus (`phi_match_rate = 1.0` in each listed family block).
2. Arithmetic family has substantially lower phase-match rate in this corpus.

## Falsification Rule
This claim is falsified if recomputation of the above rates/ranges from the same source file does not match the values stated here.
