# WP3 — Small-N exact structural ledger  (N ≤ 35, DETERMINISTIC)

**Farm to:** Haiku subagent (mechanical, exact — no statistics, no controls).
**Runtime budget:** ~15–30 min.

## Purpose
On the low bands the whole `(n,k,D)` construction is small enough to compute
exactly. Replace *statistics* with *fact* on N ≤ 35, and produce the ground-truth
that WP1's control and the coordination pass lean on. Answers three exact
questions the source doc only poses statistically:

1. **Identity check.** For every key with N ≤ 35, confirm
   `P = base·G + D·G` and `n·Q = k·2^{N-1}·G + r·G` with `|r| < 2^{N-1}/n`
   hold as exact point equalities (use `lib_data.ec_mul/ec_add`). Report any row
   that fails (there should be none).

2. **What does knowing (n,k) actually buy?** For each N, tabulate the distribution
   of `log2|D|` and `log2|D| / (N-1)` (the fraction of free bits the residual
   still spans). Confirms/【quantifies】 the memory claim "D ≈ lower ~60% of free
   bits, (n,k) pins ~16 top bits" (`btc_puzzle_nk_decomposition`) at exact
   precision across N.

3. **Does (X,Y) alone pin n when the band is enumerable?** For N where the full
   band `2^{N-1}` ≤ 2^20 (N ≤ 21), enumerate ALL d in the band, compute
   `(X,Y)→n`, and measure the exact conditional entropy `H(n | X,Y)` — is n a
   deterministic function of the public point on these bands, or genuinely
   many-to-one? (It is many-to-one only because different d→same n; but confirm
   there is no exact algebraic shortcut on the enumerable bands.)

## Data
`lib_data.load(bits_max=35)`; for the enumeration in (3), generate the full band
directly with `ec_mul` (do not rely on the 660-per-band sample).

## Report → `../RESULTS/WP3_smallN_exact.json`
`{identity_failures: 0, per_N: {N: {logD_median, logD_frac_median, r_bound_ok}},
enumerable_bands: {N: {H_n_given_XY_bits, band_size}} }`.

**Done-check:** exact tables emitted; identity_failures == 0. No positive control
needed — every claim here is a deterministic equality or an exact count.
