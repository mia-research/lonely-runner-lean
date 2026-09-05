# WP4 — Null n-distribution + selection-prior sharpening  (STRUCTURE PROBE)

**Farm to:** Haiku subagent (tabulation), with careful reading of the caveat.
**Runtime budget:** ~15–30 min.

## The key caveat (do not skip — it flips the interpretation)
The 100k set is **constructed**: `d` is (near-)uniform in each band and `(n,k)` is
the best-rational-approx *of that uniform d*. So the n-distribution in this file is
**the null** — what `n` looks like under uniform `d` — NOT the creator's selection.
That is exactly its value: it gives a **high-power matched null** for the 82
real-key watch-items that were previously only estimated at n=72
(`btc_puzzle_hunt_method`): "n is prime *less* often than baseline" (z=−2.3),
"φ(n)=2^r enrichment" (p=0.52), the `d mod 23` watch.

## Procedure
1. From `lib_data.load()`, tabulate, **stratified by bit-length band**:
   - `P(n = v)` for each v ≤ 256
   - `P(n prime)`, `P(φ(n)=2^r)`, `P(n squarefree)`, mean `ω(n)`, `P(gcd(k,n)=1)`
     (=1 by construction — sanity), distribution of `ord_n(2)` (period L)
2. Cross-check against the **analytic Farey/CF expectation**: the probability that
   the best-approx denominator of a uniform u∈[0,1) equals `n` is ∝ related to the
   Farey interval widths / Gauss–Kuzmin for CF denominators. The empirical (step 1)
   and analytic must agree — that agreement is this WP's built-in control (two
   independent nulls). Report the max discrepancy.
3. Re-score the **82 real keys** (`../puzzles_verified.csv`, columns include `n`)
   against this sharpened null: recompute the z-score for `P(n prime)`,
   `P(φ(n)=2^r)`, and `ord_n(2)` using the high-power null probabilities from
   step 1 (matched to the real keys' bit-length multiset). Report updated z / p.

## What counts / does not
- A real-key class stat that stays ≥2σ from the sharp null is a **marginal prior
  on n** (weak, does not use `(X,Y)`), i.e. a lean worth carrying — report it as
  such, bounded to n=82.
- Everything here is a **prior over n from the n-distribution**, never an `(X,Y)`
  leak. Do not phrase it as an attack on the public key.

## Report → `../RESULTS/WP4_null_ndist.json`
`{null_by_band: {...}, analytic_vs_empirical_max_disc, real_key_zscores:
{prime_rate, phi2r, ord2}, note: "constructed set = null, not selection"}`.

**Done-check:** empirical null agrees with analytic (control), and the 82-key
watch-items are re-scored at higher power with conditional phrasing.
