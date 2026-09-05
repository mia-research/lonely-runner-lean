# WP1 — The n·Q near-miss distinguisher  (ATTACK-VALID · crown jewel)

**Farm to:** Sonnet subagent (judgment on score distributions). May offload the
small-N exact-match control loop to a Haiku helper.
**Runtime budget:** ~30–60 min. Subsample (see below), do not run full 100k×256.

## Why this one first
This is the only idea in the source doc that (a) exploits the *defining* identity
of the construction and (b) is legitimately runnable as an **attack** — it tries
every candidate `n' ∈ [1,256]` and asks whether the true `n` behaves differently,
using only public `(X,Y,N)`. (Contrast: `X mod n`, `XY mod n²` are circular — they
need the secret `n`. See the F1 trap in `btc_puzzle_hunt_method`.)

## The identity
For a key `P=d·G` with `d = 2^{N-1} + ⌊2^{N-1}·k/n⌋ + D`, set
`Q = P − 2^{N-1}·G`. Then for the TRUE `n`:
```
n·Q = k·2^{N-1}·G + r·G,   |r| < 2^{N-1}/n   (r = n·(d−2^{N-1}) − k·2^{N-1}, small)
```
So `n·Q` is a **known** point `k·(2^{N-1}·G)` plus a **small-DL perturbation** `r·G`.
For a wrong `n'`, `n'·Q` is an essentially random point. Question: does a
**public-computable** smallness/uniformity score of `n'·Q` (or of the reduced
`R = n'·Q − t·2^{N-1}·G` swept over `t∈[0,n')`) separate `n'=n` from `n'≠n`?

## Procedure (use `../lib_data.py`)
1. Sample: for each band `N` in 8..120, take up to 200 keys (`df.groupby('bits')`).
2. Per band, precompute the anchor `Apt = lib_data.band_anchor(N)` ONCE.
3. Per key: `Q = ec_add(P, ec_neg(Apt))`. Then generate `j·Q` for `j=1..256`
   **incrementally** (running `ec_add(.., Q)`), NOT 256 scalar mults.
4. For each candidate `n'`: compute scores on `n'·Q` and on the best reduced
   `R` over `t`:
   - `min(x, p−x)`, `min(y, p−y)`  (bias toward "small" coordinates)
   - Hamming weight of `x` and of `y`
   - Shannon entropy of low 32 bits of `x`
   - residues `x mod q`, `q ∈ {3,5,7,11,13}`
   For the reduced score, take `min_t` of `min(x,p−x)` of `R = n'·Q − t·Apt·k'`
   over the plausible `t` grid (keep the grid small; `k∈[0,n')`).
5. Label each `(key, n')` with `is_true = (n' == key.n)` — **used only to evaluate**,
   never as a feature.

## Positive control (MANDATORY — this fires or the WP is inconclusive)
Small-N exact match. For `N ≤ 28`, `|r| < 2^{N-1}/n` is brute-forceable:
build a hash table `{x(r·G): r}` for `r` up to the bound, and for each `(n',k')`
look up `R = n'·Q − k'·Apt`. The **true** `(n,k)` yields an EXACT hit (recovers `r`,
hence `D`); wrong candidates do not. Report the hit-rate for true vs wrong `n'`.
This proves the identity is real and true-`n` IS distinguishable when `D` is small.

## Null
Wrong-`n'` scores are the built-in null. Also permute the `n`-label across keys
within a band and re-run the KS test (`lib_control.permutation_null`).

## Report → `../RESULTS/WP1_nq_nearmiss.json`
- Per score: KS statistic & p for `{n'=n}` vs `{n'≠n}`, with Bonferroni over scores.
- Small-N exact control: hit-rate true vs wrong (`control_z`).
- Ranking power: for what fraction of keys does the true `n` land in the top 1% /
  top 10% by best score? (This is the actual "hint on n" payoff — a posterior
  shift on `n`, per `btc_puzzle_nk_decomposition`, not recovery of `d`.)
- `reading`: conditional (`lib_control.conditional_negative`).

**Done-check:** control fired (small-N exact hits true≫wrong) AND a stated,
bounded verdict on whether the large-N statistical score inherits any separation.
