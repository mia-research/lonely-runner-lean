# Certificate and wrap depth, redone per-runner with no adjoined stationary runner, via BSM

2026-09-12. Script `experiments/n8/ok_cert_K_bsm_v1.py`. Exact `Fraction`.
Supersedes the coverage and `K` figures of `GRID_CERTIFICATE_v1` §4 and
`K_STATISTIC_RETRACTION_v1` §3, whose population was the extreme-runner slice
(`RESIDUAL_NO_STATIONARY_v1` §1). The certificate itself is unchanged.

---

## 1. Method  `[per phi_law_paper_v2 §2.2]`

A configuration is 8 runners with 8 given speeds; **nothing is adjoined**. For runner `i` the
constraints are the **distinct** values `S_i = {|v_j − v_i|}` — `‖·‖` is even, so a symmetric
pair contributes one constraint, not two.

Good sets are computed by the **Boundary Set Method**: the predicate `‖s t‖ ≥ 1/8` changes
only at `t = (8k±1)/(8s)`, so those times are collected and the predicate evaluated at entry
and exit of each cell. Lemma 2.2 makes this event-complete **for the predicate**, which is
exactly what a certificate needs. (It is *not* complete for the maximum of the min-gap — see
`feedback_count_the_runners_given_2026_09_12`.)

Certificate: at `t = a/8 + ε` with `r_s = s·a mod 8`, constraint `s` admits
`ε ∈ [(1−r_s)/(8s) + k/s, (7−r_s)/(8s) + k/s]`. **`K = max_s |k_s|`**; `K = 0` is the
principal certificate.

## 2. Results  `[VERIFIED — exhaustive]`

8-subsets of `[1..16]`: **102 960 runner-instances**.

**Control:** runners with no witness at all — **0**. (Any would refute LRC(8).)

| `K` | runners | share | cumulative | extreme | interior |
|---|---|---|---|---|---|
| **0** | 91 426 | **88.80%** | 88.80% | 78.80% | **92.13%** |
| 1 | 11 524 | 11.19% | **99.99%** | 21.18% | 7.86% |
| 2 | **10** | 0.01% | **100.00%** | 0.02% | 0.01% |

**Max wrap depth needed: 2.**

**Like-for-like with the old figures** — restricted to runners whose constraint set holds a
multiple of 8 (the old "Case 2"), 48 048 instances = 46.67%:

| | new (per-runner, BSM) | old (extreme-only, adjoined) |
|---|---|---|
| principal `K=0` | **75.99%** | 61.79% |
| `K ≤ 1` | 99.98% | 99.94% |
| `K ≤ 2` | 100% | 100% |

The principal certificate gains 14 points once interior runners are in the population, for the
reason `RESIDUAL_NO_STATIONARY_v1` gives: sign-collapse reduces their distinct constraint
count.

## 3. The `K = 2` cases are one constraint set  `[VERIFIED — exact]`

All **ten** instances requiring `K = 2` — ten different configurations, ten different runners
— carry the **same** constraint set:

> **`S = (1, 5, 6, 7, 8, 11, 13)`**

Witness `t = 23/48`, distances `23/48, 19/48, 1/8, 17/48, 1/6, 13/48, 11/48` — the minimum is
**exactly `1/8`**, so this is a tight case. And no `d ≤ 8` divides none of `S`, so it is a
residual runner in the sense of `RESIDUAL_NO_STATIONARY_v1` §3.

The hardest case for the certificate in this box is therefore a **single constraint set**,
not a family.

## 4. Control, and a control bug of mine  `[recorded]`

**Control as run:** 6000 sampled runner-instances from `[1..40]`, each certificate's **actual
witness** extracted and verified by direct evaluation of `‖s t‖ ≥ 1/8`. **0 non-witnesses.**

The first version of this control reported 1427 failures out of 3129. That was the control's
fault: `K = 0` means each constraint uses the interval *containing* `ε = 0`, so the witness is
`t = a/8 + ε` for some `ε ∈ [L,U]` — **not `ε = 0`**. I tested the grid point itself.
Third control-caught bug of mine in this line of work; none reached a published number.

## 5. Ledger

`[VERIFIED — exhaustive]` §2's table over all 102 960 runner-instances in `[1..16]`, with the
no-witness control at 0; §2's like-for-like restriction.
`[VERIFIED — exact]` §3, all ten `K=2` instances sharing `S = (1,5,6,7,8,11,13)`, witness and
distances exhibited.
`[VERIFIED — sampled]` §4's control, 6000 instances, 0 failures.
`[SUPERSEDED]` the coverage and `K` figures in `GRID_CERTIFICATE_v1` §4 and
`K_STATISTIC_RETRACTION_v1` §3. The certificate, the retraction's finding that `K` is
anti-correlated with difficulty, and the residual characterisation are all unchanged.
`[SCOPE]` percentages are box-dependent; `K ≤ 2` is a fact about `[1..16]`, not a bound.
`[recorded]` §4's control bug.

`n = 8` is **not proved.**
