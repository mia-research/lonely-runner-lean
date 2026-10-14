# The LP chain search: one real result, three non-results

Addendum to `ANALYTIC_LAST_STEP_v1`. The LP-pruned chain search (§1 of that note) has finished.
**Three of its four rows are not conclusions**, and the one that is confirms the analytical bound
exactly.

```
  cover [1,7], chains ≤ length  6, k ≤ 6 :  infeasible   LP nodes 359,342   best reach 4.5172
  cover [1,7], chains ≤ length  8, k ≤ 6 :  infeasible   LP nodes 400,140   best reach 4.0146
  cover [1,7], chains ≤ length 10, k ≤ 6 :  infeasible   LP nodes 400,123   best reach 4.0146
  cover [1,7], chains ≤ length 12, k ≤ 6 :  infeasible   LP nodes 400,188   best reach 4.0476
```

## The one real result — and it validates the reach lemma exactly

The length-6 run finished **under** the 400,000-node cap (359,342), so it is complete:

> **No six bad intervals can cover `[1,7]`. The maximum reach from `R = 1` with six intervals is
> `4.5172`.**

And `(9/7)^6 = 4.51717396…` — **an exact match.** The LP, searching over chains with no knowledge of
the reach lemma, independently attains the ceiling that lemma predicts: six steps, each multiplying
the reach by at most `9/7`, all at level `m = 1`. That is a clean cross-validation of both the
per-step bound (`[PROVED]`, `dilation_lt_nine_sevenths`) and the level-counting refinement.

It also gives, rigorously for this search: **covering `[1,7]` needs at least seven intervals** — which
is what the analytical bound says and which is now confirmed by an independent method.

## The three non-results

Lengths 8, 10 and 12 all terminated **at** the node cap (400,140 / 400,123 / 400,188). Their
"infeasible" means *no feasible chain was found before the cap*, not that none exists. The tell is
the reported best reach: it **falls** from `4.5172` at length 6 to `4.0146` at length 8, which cannot
happen for a genuine maximum — more intervals cannot reach less. It is the truncation showing.

**Those three rows carry no information and must not be read as bounds.** Recorded because the word
"infeasible" in the output invites exactly that misreading.

## What this says about the route

The LP reduction is sound and decidable (`ANALYTIC_LAST_STEP_v1` §1), and it is **exact where it
completes**. But it hits its cap at length 8 on the *easier* of the two regions, while the reach
lemma says covering `[1,15]` needs **≥ 18** intervals. The gap between where the search completes
(6) and where the question lives (≥ 18) is the whole difficulty, and closing it by enumeration is not
plausible: the branching is ~`6 × (k_max+1)` per position.

So the position is unchanged from `ANALYTIC_LAST_STEP_v1` §5 — a proof needs an **interlocking**
obstruction rather than an enumeration — with one thing added: the analytical reach bound is now
confirmed tight at six steps by an independent method, so it is not merely an upper estimate.

## Grades

| | |
|---|---|
| six intervals cannot cover `[1,7]`; max reach `(9/7)^6` | **`[VERIFIED — complete LP search]`**, matching `[PROVED]` per-step bound |
| eight or more intervals cannot cover `[1,7]` | **not established** — search truncated at the node cap |
| band 2 unreachable | **not established** |

```bash
python3 experiments/n8/lp_cover_v2.py     # re-runs the search; note the node cap at 400,000
```
