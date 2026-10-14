# The residual, redone without adjoining a stationary runner

2026-09-12. Script `experiments/n8/ok_residual_nostationary_v1.py`. Exact integer arithmetic.
Supersedes the residual figures of `SMALL_DENOMINATOR_WITNESS_v1` §3–§4 and
`RESIDUAL_ANGLE_v1`, whose population was implicitly restricted. The lemma and the
characterisation are unchanged; the **counts** change, and the reason is structural.

---

## 1. What was wrong with the old population  `[PROVED]`

The old enumeration ran over **7 distinct positive integers** as the speed tuple. That set is
exactly the difference set of an **extreme** runner: for `V = {0} ∪ E` the minimum runner's
differences are `E`, all of one sign, hence all distinct.

An **interior** runner is different. Its differences `v_j − v_i` take both signs, and
`‖·‖` is even, so `v_j − v_i = −(v_k − v_i)` **collapses two constraints into one**. Measured
mean number of distinct constraints, by position in the sorted 8-set over `[1..20]`:

| position | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|---|
| mean distinct (of 7) | **7.000** | 6.601 | 6.224 | **5.964** | **5.964** | 6.224 | 6.601 | **7.000** |

So the old population was the hardest position only, and interior runners were never in it.

## 2. The redone analysis  `[VERIFIED — exhaustive]`

A configuration is 8 runners with 8 given speeds; no runner is adjoined. Runner `i` is
**settled** if some `d ∈ {2,…,8}` divides none of its distinct constraints `|v_j − v_i|`
(then `t = a/d` gives `‖·‖ ≥ 1/d ≥ 1/8`), or if it has `≤ 3` distinct constraints (union
bound). Otherwise **residual**.

| | `[1..16]`, 12 870 configs | `[1..20]`, 125 970 configs |
|---|---|---|
| achieve global isolation (all 8 at once) | 258 = **2.00%** | 1304 = **1.04%** |
| **residual (config, runner) pairs** | 9 702 / 102 960 = **9.42%** | 111 736 / 1 007 760 = **11.09%** |
| configurations with ≥ 1 residual runner | 7 026 = **54.59%** | 75 367 = **59.83%** |
| configurations fully settled by the lemma | **45.41%** | **40.17%** |

Residual runners per configuration, `[1..20]`: 0 → 40.17%, 1 → 36.81%, 2 → 18.05%,
3 → 4.19%, 4 → 0.69%, 5 → 0.08%, 6 → 0.01%. Worst found: `(1,2,4,8,12,16,18,19)`, with
**6** residual runners — `2, 4, 8, 12, 16, 18`.

**The position effect, measured:** extreme runners are residual **18.09%** of the time,
interior runners **8.75%** — a factor of 2.07. That is the whole discrepancy with the old
figure.

**The `≤ 3` union bound contributes nothing:** 0 runners settled by it in either box. With 8
runners the minimum distinct-constraint count is 4 (attained at the two centre positions of a
symmetric configuration), never 3.

## 3. What the corrected statement is

Old: *"the residual is 30.71% of Case-2 tuples."* That figure counts extreme runners only and
is therefore an upper bound taken at the worst position.

New, and this is the one to carry:

> A **runner** is residual iff its distinct constraint set `{|v_j − v_i|}` contains a multiple
> of every `d ∈ {2,…,8}`. Roughly **1 runner in 10** is residual; extreme runners at twice the
> rate of interior ones. About **40–45%** of whole configurations are settled outright by the
> small-denominator lemma, with no residual runner at all.

LRC(8) needs every runner lonely, so a configuration is finished only when all 8 are — which
is why the per-configuration figure (54.6–59.8% carrying at least one residual runner) is much
larger than the per-runner figure.

## 4. Ledger

`[PROVED]` §1, that the old population is exactly the extreme-runner difference sets, and the
sign-collapse mechanism for interior runners.
`[VERIFIED — exhaustive]` §2's tables over both boxes; the position rates 18.09% vs 8.75%;
the `≤ 3` union bound contributing 0.
`[SUPERSEDED]` the residual percentages in `SMALL_DENOMINATOR_WITNESS_v1` §3–§4 and
`RESIDUAL_ANGLE_v1`. The **lemma** and the **characterisation of a residual runner** are
unchanged and remain as first recorded in `TIGHT_INSTANCES_v1` §1.
`[SCOPE]` the percentages are box-dependent and drift with `N`; the characterisation is not.

`n = 8` is **not proved.**
