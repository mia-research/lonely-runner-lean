# Phase 6 — Cardinality discriminator + correlation analysis

**Session:** 2026-05-27 (ctd ctd)
**Scripts:** `LonelyRunner/scripts/phase6_residual_arithmetic.py`,
`LonelyRunner/scripts/phase6b_density_separator.py`,
`LonelyRunner/scripts/phase6c_correlation.py`
**Output CSVs:** `reports/phase6_residual_arithmetic.csv` (3,839 rows),
`reports/phase6b_density_separator.csv`, `reports/phase6c_correlation.csv`

## Headline finding — the cardinality discriminator

**Within the pigeonhole-failure stratum, the cardinality balance
$k_G + k_A - (n - 1)$ is a PERFECT separator** between LRC-shape positives and
counterexamples:

| Stratum (pigeonhole fails) | balance = 0 | balance > 0 |
|---|---|---|
| L_residual (LRC-shape positive, 53) | **53** | 0 |
| CE_set (counterexamples, 681)       | **0**  | 681 |

All 681 counterexamples have $k_G + k_A \in \{n, n+1, n+2\}$ — they are
"over-specified" relative to the LRC dimension. Conversely, no LRC-shape input
(53 verified) is a counterexample.

This refines Phase 4's Theorem 5.2-S (which handled $k_G + k_A \le n - 2$) with
the boundary case $k_G + k_A = n - 1$: empirically positive for all 5,517
LRC-shape inputs in the search range.

## Stratification refinement

Within the 38,664 inputs scanned (n ∈ {3..7}, speeds ∈ {1..8}, primes ∈ {2..19}):

| Stratum | Count | All have $N_{\text{joint}} \geq 1$? |
|---|---|---|
| Pigeonhole holds (Phase 5)   | 34,825 | Yes (proved) |
| L_residual (LRC-shape, pigeonhole fails) | 53 | Yes (verified) |
| NL_residual (non-LRC, pigeonhole fails)  | 3,105 | Yes (verified) |
| CE_set                       | 681   | No (counterexamples) |

Note: the 5,517 total LRC-shape inputs = 5,464 (pigeonhole holds) + 53 (residual,
verified positive). Coverage: 100%.

## Density invariants — soft separators

`expected_overlap = n_band_betas * cIA / (n L_A)` (mean intersection under
uniform distribution):

| Stratum | min | median | max |
|---|---|---|---|
| L_residual  | 2.40  | 11.67 | 60.71 |
| CE_set      | 0.17  |  1.00 | 10.07 |
| NL_residual | 0.33  |  4.00 | 56.43 |

Best single-threshold separator: `expected_overlap > 5.6` misclassifies 18/734.
Not perfect alone, but combined with the cardinality separator it is.

`target_density = cIA / (n L_A)`:

| Stratum | min | median | max |
|---|---|---|---|
| L_residual  | 0.30 | 0.44 | 0.60 |
| CE_set      | 0.07 | 0.13 | 0.50 |

L_residual has uniformly high target density (≥ 0.30), CE has many low-density cases.

## Correlation invariants

`correlation_ratio = N_joint / expected_overlap` (1 = random; 0 = CE):

| Stratum | min | median | max |
|---|---|---|---|
| L_residual  | 0.36 | 1.00 | 1.43 |
| NL_residual | 0.12 | 1.14 | 6.00 |
| CE_set      | 0.00 | 0.00 | 0.00 |

For L_residual, the correlation_ratio is consistently near 1 (random-uniform):
bands and targets behave statistically independent. For CE, ratio is 0:
adversarial anti-correlation. **This confirms: LRC-shape ELIMINATES adversarial
alignment**, but does not impose strong positive correlation either.

## Structural reading

The empirical separator $k_G + k_A = n - 1$ is the **cardinality boundary** at
which the conjecture transitions from "over-specified, can fail" to "naturally
positive". Geometrically:
- $k_G + k_A \leq n - 2$ (Phase 4): under-specified relative to $n$; the
  conjecture reduces to LRC at $n - 1$ (handled by $\mathbf{H}(n-1)$).
- $k_G + k_A = n - 1$ (Phase 6 verified): exactly LRC-shape; conjecture holds.
  Either by pigeonhole (99.04%) or by direct verification (0.96%, 53 cases).
- $k_G + k_A \geq n$ (CE region): over-specified; abstract counterexamples exist
  but DO NOT arise in LRC.

Phase 5's pigeonhole and Phase 6's cardinality discriminator are complementary:
- Pigeonhole is a SUFFICIENT condition that's checkable but ignores cardinality.
- Cardinality is a SEPARATOR within the pigeonhole-failure stratum.

Combined: ALL LRC-shape inputs (in search range) are positive.

## What this means for Conjecture 5.2-H

The conjecture's status in v11.7 was: open in the 0.96% LRC-shape residual.
Phase 6 says: within the search range, ALL 5,517 LRC-shape inputs are positive
(5,464 via pigeonhole + 53 via direct verification).

For all-n unconditional closure of Conjecture 5.2-H, we need to argue that
LRC-shape pigeonhole-failure remains finite or directly verifiable at larger
n. This is the next open problem.

## Verification

- **Qwen prescreening:** FLAG, but with internally inconsistent reasoning (Qwen
  stated "CE require kG+kA ≥ n" which actually MATCHES the claim — Qwen
  appears confused).
- **DeepSeek deep verify (with --thinking):** ACCEPT, CONFIDENCE HIGH.
  Reasoning: "Phase 4 handles kG +kA ≤ n-2, and the remaining case (n-1) is
  perfectly captured by LRC-shape inputs as positive, structurally avoiding
  adversarial alignment seen in counterexamples."

## Artefacts

- `LonelyRunner/scripts/phase6_residual_arithmetic.py` — main mining harness
- `LonelyRunner/scripts/phase6b_density_separator.py` — density-product analysis
- `LonelyRunner/scripts/phase6c_correlation.py` — correlation analysis (final)
- `reports/phase6_residual_arithmetic.csv` — 3,839 enriched rows
- `reports/phase6b_density_separator.csv` — augmented with density invariants
- `reports/phase6c_correlation.csv` — augmented with correlation invariants
- `LonelyRunner/PHASE6_FINDINGS_2026_05_27.md` — this file

## Status going forward

Phase 6 confirms what Phase 3b reported empirically: within the search range,
LRC-shape never produces a counterexample. The new content is structural:
$k_G + k_A = n - 1$ is the cardinality boundary, and within this boundary, the
combination of pigeonhole (Phase 5) + direct verification (Phase 6) gives full
coverage.

For v11.7, the Phase 6 finding should be added as **Theorem 5.2-D
(Cardinality Discriminator)** or equivalent, alongside Theorems 5.2-S and 5.2-P.
Conjecture 5.2-H's status sharpens: the abstract joint-fine-cell statement
holds for all $k_G + k_A \leq n - 1$ in the searched range; the conjecture is
the all-$n$ extension.
