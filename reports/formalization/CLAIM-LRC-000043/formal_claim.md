# Formalized Claim: CLAIM-LRC-000043

## Claim Type
Empirical characterization claim (arithmetic efficiency per-n distribution, seed-invariance,
and phi_over_n column precision; auxiliary context for CLAIM-LRC-000044).

## Domain
Dataset: `/Users/trentpalelei/Downloads/lrc_efficiency_runtime_validation (1).csv`
SHA-256: `23ffbf7966ffd15a56878b162206af8bb457e490b6fe26b2b7574a8cb33efe55`
Note: Identical byte-for-byte to `lrc_efficiency_runtime_validation.csv`; the "(1)"
suffix is a browser download duplicate, not a distinct experiment.
Rows: 384 (1 header + 384 data). Families: arithmetic, geometric, harmonic, quadratic.
n ∈ {5,7,8,10,11,12,13,15,16,17,19,20,23,25,29,30} (16 values); 6 seeds per (family, n).
Columns used: `family, n, phi, phi_over_n, efficiency`.
Role: P3_context_or_auxiliary — provides per-n detail that contextualizes CLAIM-LRC-000044.

## Formal Proposition

### Statement 1 — Arithmetic Efficiency Per-n Characterization

Define `eff(r)` = `efficiency` = `isolation_count / boundary_count` for row `r`.
Restrict to arithmetic rows (96 rows, 6 seeds × 16 n values).

Observed per-n efficiency ranges (min and max across 6 seeds):

| n  | min eff  | max eff  | range    |
|----|----------|----------|----------|
| 5  | 0.180091 | 0.180328 | 0.000237 |
| 7  | 0.152557 | 0.152755 | 0.000198 |
| 8  | 0.121768 | 0.122087 | 0.000319 |
| 10 | 0.108341 | 0.108485 | 0.000144 |
| 11 | 0.150633 | 0.150764 | 0.000131 |
| 12 | 0.207475 | 0.207673 | 0.000198 |
| 13 | 0.242350 | 0.242513 | 0.000163 |
| 15 | 0.280723 | 0.280831 | 0.000108 |
| 16 | 0.235367 | 0.235663 | 0.000296 |
| 17 | 0.245637 | 0.245954 | 0.000317 |
| 19 | 0.241490 | 0.241736 | 0.000246 |
| 20 | 0.241428 | 0.241756 | 0.000328 |
| 23 | 0.284572 | 0.284906 | 0.000334 |
| 25 | 0.289547 | 0.289902 | 0.000355 |
| 29 | 0.417786 | 0.418042 | 0.000256 |
| 30 | 0.444042 | 0.444233 | 0.000191 |

Global min efficiency: **0.108341** at n=10.
Global max efficiency: **0.444233** at n=30.
Overall arithmetic efficiency range (pooled): **[0.108341, 0.444233]**, mean **0.240346**.
Non-monotone: efficiency does not increase or decrease with n; notable dip at n=16 (0.2354)
below both n=15 (0.2808) and n=17 (0.2458).

Cross-family comparison (all n pooled):
- arithmetic: [0.108341, 0.444233], mean 0.240346
- geometric:  [0.910448, 0.999900], mean 0.992358
- harmonic:   [0.933415, 0.999900], mean 0.992380
- quadratic:  [0.943556, 0.999905], mean 0.995271

Arithmetic efficiency is strictly separated from all non-arithmetic families: the arithmetic
maximum (0.444233) is below the non-arithmetic minimum (0.910448) by a gap of 0.466.

### Statement 2 — Arithmetic Efficiency Seed-Invariance

For each n, arithmetic efficiency varies by at most **0.000355** across the 6 tested seeds
(max at n=25). Mean within-n range across all 16 n values: **0.000239**.
Interpretation: arithmetic efficiency is nearly seed-invariant for fixed n; seed variation
accounts for ≤0.08% of the global arithmetic efficiency range (0.000355 / 0.335892).

### Statement 3 — phi_over_n Column Precision

`phi_over_n` is stored as a 6-decimal-place float (e.g., 0.857143 for 6/7).

Precision characterization (across all 384 rows, all families):
- **Exact** (relative error = 0): **144/384** rows.
  These are n values where φ(n)/n is a terminating decimal:
  n ∈ {5, 8, 10, 16, 20, 25} — each φ(n)/n has denominator of form 2^a·5^b.
- **Below sensitive threshold** (0 < rel_err < 1e-6): **216/384** rows.
  n ∈ {7, 11, 13, 17, 19, 23, 29} — stored value truncated at 6 decimal places.
- **Above sensitive threshold** (rel_err ≥ 1e-6): **24/384** rows.
  n=30 only: stored 0.266667 vs exact 8/30 = 0.2666666...; rel_err = **1.25e-6**.
- Max relative error: **1.25e-6** at n=30 (n=12 next at 1.00e-6).

Note: The dossier's `float_risk = medium` is explained by n=30 phi_over_n marginally
exceeding the sensitive threshold (1.25e-6 > 1e-6). The `efficiency` and other computed
columns are not affected by this truncation.

## Falsification Rule

This claim is falsified if recomputation from the stated source file (verified by SHA-256) yields:
1. Any per-n efficiency min/max values differing from Statement 1 table by more than 1e-6.
2. The global arithmetic min efficiency < 0.108341 or max > 0.444233.
3. Any n with within-seed efficiency range > 0.001 (relaxed bound; measured max is 0.000355).
4. The arithmetic-vs-non-arithmetic gap < 0.45 (current: 0.466).
5. phi_over_n max relative error from phi/n deviating from 1.25e-6 by more than 1e-9.
