# Pre-registration — Per-N d-term / key feature sweep (v1)

**Date:** 2026-07-06. **Frozen before viewing any per-feature result.**

## Question
Do the puzzle creator's actual keys deviate from uniform-in-band at **matched bit
size N**, viewed through a fixed panel of features? Only such a deviation yields a
non-uniform per-N prior that could reorder candidate keys for an unsolved puzzle.

## Data
- **Real:** 82 solved keys (`puzzles_verified.csv`), private key d known. Use the 72
  with N≥11 (below that D-terms=0 and the band has <660 states).
- **Baseline (null):** `constructed_keys_1to160_100k.csv`, 660 independent uniform
  keys per bit-length — the "creator = uniform in band" null, matched by N.

## Test
For each real key (bit size N) map each feature to its position within the SAME-N
baseline:
- **Continuous features:** empirical quantile (avg-rank) within same-N baseline →
  aggregate the 72 quantiles with a one-sample **KS test vs U[0,1]**, and a
  **mean-quantile z** (mean−0.5)/(sqrt(1/12/m)).
- **Binary features:** compare real count S to Poisson-binomial null
  mu=Σ p_N, Var=Σ p_N(1−p_N) (p_N = baseline rate at that key's N) → two-sided z.

## Pre-registered feature panel (17)
Continuous (7):
1. `u` = (d−2^{N−1})/2^{N−1}  (raw position; direct uniformity)
2. `n`  (CF denominator)
3. `k`  (CF numerator)
4. `approx_err` = |u − k/n|
5. `d2_bits` = log2(d2) (first D-term denominator; subset with ≥1 term)
6. `d2_frac` = d2 / 2^round(d2_bits)  (mantissa of d2)
7. `d3_bits` = log2(d3) (subset with ≥2 terms)

Binary (10):
8. `d_odd`         (d mod 2)
9. `d_mod3_is0`    (d ≡ 0 mod 3)
10. `n_prime`      (n is prime)   ← standing watch-item
11. `n_even`       (n mod 2)
12. `d2_odd`       (d2 mod 2)
13. `d2_mod3_is0`  (d2 ≡ 0 mod 3)
14. `sign_term2_pos` (term2 > 0)
15. `sign_term3_pos` (term3 > 0; subset ≥2 terms)
16. `Y_parity`     (pubkey Y even)  ← transferable control (expected null)
17. `X_odd`        (pubkey X mod 2) ← transferable control (expected null)

## Multiple-testing / look-elsewhere correction
Report every feature's raw p. **Global significance** = min-p across the panel,
calibrated by Monte Carlo: R=3000 synthetic "real sets" drawn by sampling one
baseline key per matched N; null distribution of min-p; corrected global p =
fraction of replicates with min-p ≤ observed. **Decision rule fixed now:** a
feature is a *candidate signal* only if corrected global p < 0.05; anything else is
logged as null (bounded by the 72-key sample, not declared absent).

## Notes / traps controlled
- Features 16–17 use only (X,Y): a deviation there is directly usable on unsolved
  keys; expected null (pubkey coords ~uniform regardless of d-distribution) — they
  are calibration controls.
- No feature is computed at a "true n" from public data (not the circular
  classifier form); all are functions of the known d for solved keys.
- Panel is frozen; no post-hoc feature additions in v1.
