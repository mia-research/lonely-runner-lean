# Exact (float-free) redo — master list

Trigger: `u = (d-lo)/lo` is a float in `generate_dataset.py:40`; the entire
(n,k,D) decomposition line inherited it. Redo everything derived, exactly.
Rule: `btc_puzzle_investigation/CLAUDE.md`.

## Scope, stated precisely

- **Exact already (do NOT regenerate):** the keys — `d` (random int), `X,Y` (=d·G
  by integer Jacobian arithmetic, independently re-verified). `D` and `d_terms`
  are integer *given* (n,k).
- **Float-poisoned (redo):** the selection of `(n,k)` (float `u`, `round(u*n)`,
  `abs(u-k/n)`); any position/ratio target (`u_bin`, my CF target); ~28 files that
  consumed the float decomposition, and every memory finding derived from them.

## The list

**0 — Rule (DONE).** No float in the signal path → `CLAUDE.md` + `check_no_float.sh`
+ memory. Provisional-flag all float-era results.

**1 — Exact core module (`exact_core.py`).** One canonical, float-free source of:
- `best_nk(d, N, nmax)` — minimize integer `|(d-lo)*n - k*lo|`, tie-break by n.
- `residual(d,N,n,k)`, `d_terms(...)` — already integer; move here, add float guard.
- `cf_denoms(d, N)` — exact continued-fraction convergent denominators, uncapped.
- `position_bin(d, N, bins)` = `(bins*(d-lo))//lo` (exact).
- `nk_curve(d, N, nmax)` — exact n(nmax) for the priced-nmax sweep.
- Self-test: assert results == a `Fraction`-based reference; assert no float.

**2 — Regenerate the decomposition columns exactly.**
- 2a. `constructed_keys_1to160_100k.csv`: recompute n,k,D,d_terms,d2..d6 with
  `exact_core` (keys stay; re-verify X,Y integer). Write `..._exact.csv`.
- 2b. `btc_puzzle_master.csv`: recompute the same columns exactly for the 82 real
  keys. Write `..._exact.csv`. Diff against float columns → quantify what moved.

**3 — Float-free estimator (`leak_test_exact.py`).** Replace v1/v2 z-scores with
exact per-feature empirical p (integer rank among R permutations); family-wise
min-p with a matched permutation null; positive + negative controls; nmax priced.
Features from (X,Y,N) only, all via `//`/`%`.

**4 — Rerun the leakage tests exactly (v3), real + exact synthetic null.**
- 4a. (X,Y)→d: d mod p, exact bit-i, exact position bins, exact CF q1/q2.
- 4b. (X,Y)→n/k: exact n across the nmax grid, search priced into the null.
- 4c. **NEW — the low-bit targets float destroyed:** residual D bits, d_terms,
  deep CF partial quotients. These were untestable under float; they are the main
  reason to do this, not just a re-confirmation.

**5 — Re-verify the float-era memory findings, exactly.** Recompute and update
(mark each provisional→confirmed/withdrawn): composite/even-n selection lean,
n-prime deficit, F1 (XY mod n²~k), the deterministic D-floor, D-terms vs
Gauss-Kuzmin, the Y-parity→n-parity effect (with nmax priced).

**6 — Guard (`check_no_float.sh`).** Grep signal-path files for banned ops; must
pass before any test runs. Wire it as the pre-test check.

## Recommended order

0 (done) → 1 → 6 → 2 → 3 → 4 → 5. Core + guard first so nothing new is built on
float; then data; then estimator; then reruns; then the memory re-verification.
