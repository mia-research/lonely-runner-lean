# WP2 — The public→n map-property ceiling at 100k  (ATTACK-VALID)

**Farm to:** Sonnet subagent (ML + control calibration).
**Runtime budget:** ~45–90 min.

## What this settles
Whether **any** public-only function of `(X,Y,N)` predicts `n`, `k`, or an
`n`-class above the noise floor — at the full 100k power (~5× the prior 20k run,
and extending to N=160). Prior result to beat/confirm: pure-`(X,Y)` MI ≈ 0.0005
bits, flat (`bigdata_leak_hunt.py`, 20k). This WP is the **definitive high-power
version** and replaces the ~30 redundant "does feature F predict n" ideas in the
source doc (FFT-of-X-bits, compression ratio, CF-of-X, k-mer, kmeans, UMAP,
GF(2)-rank, χ² residue cascades, neural raw-bit sieve — all the same map property).

## Features (public-only; `lib_data.assert_attack_valid` MUST pass)
Build one wide matrix from `(X,Y,bits)` only:
- all 32 byte-slices of `X` and of `Y`; high/low 64-bit words
- residues `X mod q`, `Y mod q` for primes `q` in 3..127
- Hamming weight of `X`, `Y`, and per-byte popcounts
- Shannon entropy of each 32-bit window of `X`, `Y`
- GLV image features: same set computed on `(βX mod p, Y)`  (β from lib_data)
- field ratios (public): `X·Y⁻¹ mod p`, `X²·Y⁻¹ mod p`, `(X+Y) mod p`, sliced
- `bits` (N) as a feature
Do **not** include anything derived from `d,n,k,D`.

## Targets (three classifiers, grouped-CV by `bits`)
1. `n` — 256-class.  Baseline = 1/‖classes present‖.
2. `n`-class — {n prime?, φ(n)=2^r?, n smooth?, ω(n)}. (marginal, few classes)
3. `k mod m` within fixed-`n` strata (does the coordinate pin `k` given `n`?).
Estimator: `sklearn.ensemble.HistGradientBoostingClassifier` (xgboost/lightgbm
absent) + a small `MLPClassifier`. Use `lib_control.grouped_cv_score`.

## Positive control (MANDATORY, and calibrate sensitivity)
Sweep planted-leak strength `s ∈ {0.1,0.2,…,1.0}` via `lib_control.plant_leak`,
append as ONE extra feature, and record accuracy vs `s`. Report the **minimum
detectable strength** `s*` (first `s` whose grouped-CV acc clears null+3σ). The
real null is only meaningful relative to `s*`: "no leak of strength ≥ `s*`".

## Null
Also fit on a `lib_control.matched_null` frame (same bit-multiset, random `d`) —
accuracy there and on real data must both sit at baseline for a clean negative.

## Report → `../RESULTS/WP2_map_ceiling.json`
`{baseline, real_acc[target], matched_null_acc, control_curve{s:acc},
min_detectable_strength, top_features (permutation importance), per-target MI}`.
`reading`: conditional negative bound to the K features, n=100k, floor `s*`.

**Done-check:** control curve shows `s*` (detector demonstrably has power), and a
bounded statement of the real public→{n,k,class} accuracy vs baseline.
