# The moment, exactly — by iteration rather than by formula

2026-09-13. n = 8, individual isolation, threshold 1/8, arbitrary distinct speeds.

Corrects the closing statement of `GENERAL_MOMENT_RULE_v1` §5 and
`RANDOM_PREDICTION_v1` §5: *"the rule tells you that it's later and never where."*
**That was wrong.** It tells you where, in a handful of cheap steps.

Artifact: `experiments/n8/ok_moment_iteration_v1.py`.

---

## 1. Why there is no one-shot formula

Runner `i`'s constraint `d` is satisfied on a **union** of intervals:

    U_k [ (8k+1)/(8d),  (8k+7)/(8d) ]

and the moment is the first point common to **all seven** unions. That is a simultaneous
condition across seven incommensurable periods, not a function of any one difference. `d_min`
locates where the search starts; nothing in it locates where seven unions first overlap.

Worked example — `(1,2,3,4,5,6,7,9)`, runner r1, differences `1,2,3,4,5,6,8`:

| `d` | `‖d·t₀‖` at `t₀ = 1/8` | |
|---|---|---|
| 1, 2, 3, 4, 5, 6 | 1/8, 1/4, 3/8, 1/2, 3/8, 1/4 | all clear |
| **8** | **0** | **blocks** |

The `d = 8` constraint is satisfied on `[1/64, 7/64] ∪ [9/64, 15/64] ∪ …`, and `t₀ = 8/64` falls
in the hole between them. The moment is `9/64` — where that constraint reopens.

## 2. The iteration  `[VERIFIED — 9,600 of 9,600]`

    t  <-  1/(8 d_min)
    repeat:
        if every constraint holds at t:  return t
        t  <-  max over BLOCKED d of the next opening (8k+1)/(8d) > t

Each step is `O(n)`: seven comparisons and a jump. It is monotone and cannot overshoot — every
blocked constraint *must* clear before the runner can be lonely, so the jump target is a lower
bound on the answer.

| steps | solved | cumulative |
|---|---|---|
| **1** | 5,279 | **0.5499** |
| 2 | 2,027 | 0.7610 |
| 3 | 1,242 | 0.8904 |
| 4 | 611 | 0.9541 |
| 5 | 217 | 0.9767 |
| 6–8 | 210 | 0.9985 |
| 9–11 | 14 | **1.0000** |

**9,600 of 9,600** agree with the moment found by exhaustive BSM search. Maximum 11 steps.

## 3. What was actually missing

Not predictability. The distinction is between:

| | |
|---|---|
| **closed form** | a single expression in the seven differences — **does not exist**, and §1 says why |
| **decision procedure** | `O(n)` per step, ≤ 11 steps, exact — **exists**, and is §2 |

Step 1 alone answers 55% of runners. Two steps answer 76%. The earlier framing treated "no
formula" as "no answer", which conflated the two.

## 4. Status and scope

`[VERIFIED — 9,600 of 9,600]` §2's iteration against exhaustive search.
`[PROVED — arithmetic]` monotonicity and the no-overshoot property: a blocked constraint must
clear before loneliness is possible, so the jump never passes the answer.
`[CORRECTED]` `GENERAL_MOMENT_RULE_v1` §5 and `RANDOM_PREDICTION_v1` §5.

**Scope.** Random integer 8-subsets of `[1,80)`; 1,200 configurations. The step distribution is a
property of that population — the 11-step maximum is observed, not a bound. Rational and
irrational speeds use identical arithmetic but were not swept here.

**Not established.** Any bound on the number of steps. Whether the step count relates to the
difference structure (e.g. to how many constraints block at step 1).

**n = 8 is not proved here, and is not the target here.**
