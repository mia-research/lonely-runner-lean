# WP6 — Candidate-sweep distinguisher battery  (ATTACK-VALID · the reformulated "mod n" ideas)

**Farm to:** Sonnet subagent.  **Runtime budget:** ~45–75 min.  **Priority: HIGH.**

## The correction this WP embodies
Earlier these ideas (source 2.2, 2.6, 3.3, 9.2, the F1 `XY mod n²` line, all the
"X mod n / Kronecker mod n / gcd(·,n) / ord mod n" tests) were dropped as
"circular — they need the secret n." **That was wrong.** Circularity only applies
to the *classifier* form (feed a model one feature computed with the true n; at
test time on an unknown key you don't have n). The **attack form is a candidate
sweep** and is fully attack-valid:

> For an unknown key `(X,Y,N)`, compute the statistic `S(X,Y,n')` for **every**
> candidate `n' ∈ [1,256]`, and bet on `n` from the value/rank. This never uses the
> secret. The dataset test: is the true `n`'s statistic **systematically extreme**
> among its 256 candidate values?

DO the work. Do not re-derive the circularity argument and stop.

## Statistics to sweep (each a function `S(X, Y, n')`)
Implement each; all use public `(X,Y)` and a candidate `n'` only:
- `X mod n'`, `Y mod n'`, `(X+Y) mod n'`, `(X*Y) mod n'`, `(X*Y) mod n'^2`
- Kronecker/Jacobi symbols `(X | n')`, `(Y | n')`  (implement Kronecker directly)
- `gcd(X, n')`, `gcd(Y, n')`  (and indicator gcd>1)
- multiplicative order of `X mod n'` (when gcd=1), and `ord(2 mod n')` interaction
- `X mod n'` compared against each candidate numerator `k'` coprime to `n'`
  (i.e. does `X ≡ f(k') (mod n')` for the paired `k'`) — sweep `(n',k')`

## Protocol (per statistic family)
1. Sample keys across bands (N in 8..120, ~150/band; more where cheap).
2. Per key, build the candidate vector `v = [S(X,Y,1), …, S(X,Y,256)]`.
3. Define the true-n **extremeness readout** two ways (report both):
   - **rank**: normalized rank of `S(X,Y,n_true)` within `v` ∈ [0,1]. Under the
     null of no leak, ranks are Uniform(0,1) across keys → KS-test vs uniform.
   - **z**: `(S(true) − mean(v)) / std(v)` per key → is the mean z ≠ 0?
   For categorical stats (gcd class, Kronecker ∈ {−1,0,1}) use the rate at which
   `S(true)` hits the rare class vs the candidate baseline.
4. Aggregate across keys: KS statistic + p (rank), t-test (z), with Bonferroni
   over the statistic families. Also stratify by band to catch N-localized signal.

## Positive control (MANDATORY — runs the SAME aggregation)
Take the real candidate vectors, and for a fraction `pγ` of keys overwrite
`S(true_n)` with an injected outlier (e.g. min of `v` minus 1). Sweep
`pγ ∈ {0.02,0.05,0.1,0.2}` and confirm the KS/rank test fires and scales with
`pγ`. Report the smallest `pγ` detected → the detector's power on THIS pipeline.
If it never fires, the WP is INCONCLUSIVE (underpowered), not a negative.

## Report → `../RESULTS/WP6_candidate_sweep.json`
Per statistic family: `{ks_stat, ks_p, mean_rank, mean_z, bonferroni_ok,
per_band_flags, control{min_detected_pgamma, fired}}`, plus the **ranking payoff**
(for what fraction of keys is true-n in the top-1%/top-10% by |z|? — the actual
hint-on-n). `attack_valid: true`. CONDITIONAL `reading` per family.

**Done-check:** control fired; every statistic family reported with a bounded
verdict AND its ranking payoff. No family silently merged into another.
