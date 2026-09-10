# Choosing the grid to fit the tuple — clusters as permutations at the outlier's scale

2026-09-10. Follows `GRID_AND_PASSAGE_v1.md`. Scripts
`experiments/n8/ok_cluster_grid_v1.py`, `ok_union3_v1.py`. Exact `Fraction`; float audit
`ok_float_audit_v1.py` covers these. Nothing uses `LRC(8)`, Rosenfeld, or any `n ≠ 8`.

---

## 1. The idea, stated

The passage law says a runner **on** its grid is resonant and **off** it is generic. But
the grid need not be the AP. Write a cluster as `e_i = N + d_i`; then

    e_i t = N t + d_i t,

so over an interval of length `1/N` the fast phase `Nt` sweeps the **whole circle** while
the differences `d_i t` are frozen. **A cluster is a permutation of an AP in its
differences, riding the outlier's scale.** Spread-out tuples are permutations of the AP
itself; clustered tuples want a different division, and the outlier supplies it.

## 2. The cluster window  `[PROVED — one line, no LRC input]`

> Let `C ⊆ E` satisfy `max C ≤ 7·min C`. On the **open** interval
>
>     W = ( 1/(8·min C),  7/(8·max C) ),     |W| = (7·min C − max C)/(8·min C·max C) > 0,
>
> every `e ∈ C` has `e t ∈ (1/8, 7/8)` strictly, hence `‖e t‖ > 1/8`.

*Proof.* `e ≥ min C` gives `e t > e/(8 min C) ≥ 1/8`; `e ≤ max C` gives
`e t < 7e/(8 max C) ≤ 7/8`. ∎  (`C = E` is the bounded-ratio theorem; the content is `C` a
proper subset.)

Each outlier `v ∉ C` has bad-set components of length `1/(4v)` at period `1/v`, so it meets
at most `⌊|W|v⌋+1` of them. Hence

> **Cluster criterion `[PROVED]`.** If `Σ_{v ∉ C} (⌊|W|v⌋+1)/(4v) < |W|` then `E` has the
> LR property, and the witness is exhibited by removing the outlier bad sets from `W`.

The optimal `C` is a **contiguous run** of the sorted speeds (`max/min ≤ 7` is an interval
condition), so there are 21 candidates per tuple.

**It is a strictly better window than the one I was using.** `BOX_AND_INTERVAL_DEFICIENCY_v1`
§2 built its interval from `LRC(h+1)`, giving `2(1/(h+1) − 1/8)/max(H)`. For
`C = {2,…,7}` the cluster window is `1/16` against `1/196` — **twelve times longer** — and
it needs no `LRC` input at all. Measured: the cluster window is longer in **510 of 608**
firing cases.

## 3. Reach  `[EMPIRICAL — sampled, stated box]`

Case-2 sample from `[1..20]`, 912 tuples (every 50th). Every criterion below returns an
explicit `t`, verified exactly against all seven speeds; **none estimates anything**.

| criterion | source | reach |
|---|---|---|
| block criterion (`a ≤ 3`) | `TILING_AND_BLOCKS_v1` §1 | 512 (56%) |
| odd-runner collapse (Klein/cyclic) | `ODD_RUNNER_COLLAPSE_v1` §2 | 821 (90%) |
| **cluster window** | this file | 445 (48%) |
| …reachable **only** by the cluster window | | **13** |
| **union** | | **905 (99%)** |
| residue | | **7 (0.77%)** |

Standalone run over `[1..20]`, 1 232 tuples: cluster criterion fires 608 (49%), **608 / 608
witnesses verified exactly**, zero failures.

## 4. The residue is a method artifact, not a difficulty class  `[PROVED — exact]`

The seven survivors, with exact `|G|`:

| tuple | `\|G\|` |
|---|---|
| `(1,2,3,6,8,10,12)` | `19/160 = 0.1188` |
| `(1,2,6,10,16,17,18)` | `1183/12240 = 0.0967` |
| `(1,4,7,8,15,19,20)` | `1441/15960 = 0.0903` |
| `(2,5,8,10,14,15,18)` | `821/10080 = 0.0814` |
| `(1,7,8,12,17,19,20)` | `373/4845 = 0.0770` |
| `(1,2,5,7,9,16,17)` | `403/7616 = 0.0529` |
| `(2,5,6,8,10,13,14)` | `353/14560 = 0.0242` |
| *(and the extremum `(2,6,7,8,10,13,14)`)* | `93/14560 = 0.0064` |

**The residue mixes the global extremum with tuples whose good set is nineteen times
larger.** So these criteria are **not sharp**: they miss easy tuples as readily as hard
ones. The 0.77% is a statement about the three criteria, not about which tuples are
difficult, and it must not be read as "0.77% of the problem remains".

## 5. Ledger

`[PROVED]` §2 window and criterion (one line each, no `LRC` input); the twelve-fold window
comparison for `C = {2,…,7}`.
`[VERIFIED — exact]` 608/608 witnesses standalone; 905 union witnesses, each checked
against all seven speeds.
`[EMPIRICAL — sampled]` all percentages, box `[1..20]`, every 50th tuple; one-sided.
`[PROVED — exact]` §4's `|G|` values and hence the "not sharp" conclusion.

`n = 8` is **not proved.** What this adds is the third and cheapest of the three
structural criteria, and — more usefully — the observation in §4 that the surviving set is
governed by the criteria rather than by the mathematics, so counting it is not a measure of
remaining difficulty.
