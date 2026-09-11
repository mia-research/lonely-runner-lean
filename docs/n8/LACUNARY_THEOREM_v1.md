# A constructive interval induction — proved, general `n`, and disjoint from the hard region

2026-09-11. Script `experiments/n8/ok_lacunary_v1.py`. Exact `Fraction`.

---

## 1. The sharpest form of the problem  `[PROVED]`

With `t = ξ/n` and `r_j = e_j a mod n`, every constraint takes the same shape:

> Constraint `j` is **bad** on an interval of width `2/e_j`, centred at `−r_j/e_j`, repeating
> with period `n/e_j`. Duty cycle exactly `1/4` at `n = 8`.

So LRC(8) is: *seven periodic bad sets, each of duty `1/4`, do not cover the circle.* Total
density `7/4 > 1`, so **no measure argument can close it** — and the substitution `ξ = η + a`
shows the choice of `a` is absorbed, i.e. the four grid phases are not extra freedom. Every
reformulation attempted this session — the `Σα` criterion, the denominator route, the crowding
recursion — returns to exactly this statement. A proof must come from the **interval
structure**, not the measure.

## 2. The interval induction  `[PROVED + VERIFIED]`

`G_k = {t : ‖e_i t‖ ≥ 1/n, i ≤ k}` is a finite union of closed intervals; let `ℓ_k` be its
longest. The good set of a new speed `e` is periodic with period `1/e`, holding in each period
one good interval of length `g = (n−2)/(n e)`.

> **Step Lemma.** An interval of length `L ≥ 1/e + g = (2n−2)/(n e)` contains a *complete* good
> interval of `e`. Hence `ℓ_k ≥ (2n−2)/(n e_{k+1}) ⟹ ℓ_{k+1} ≥ (n−2)/(n e_{k+1})`.

Verified: 150 qualifying cases, **0 violations**.

Starting from `ℓ_1 = (n−2)/(n e_1)`, the chain closes exactly when

> **`e_{k+1} ≥ ((2n−2)/(n−2))·e_k` for every `k` ⟹ LRC(`n`) holds for that tuple,
> constructively.**

At `n = 8` the ratio is `7/3`. Verified: 1279 tuples satisfying it, good set empty in **0**;
witnesses exhibited, e.g. `(4,10,25,60,141,331,775)` with a good interval of length `3/3100`.

## 3. Why it does not reach the hard cases  `[VERIFIED — exhaustive]`

Seven speeds growing by `7/3` force `e₇ ≥ (7/3)⁶ e₁ ≈ 163 e₁`. Over the complete Case-2
enumeration of `[1..18]`: **0 of 20 349** tuples satisfy the condition.

That is not a defect of the constant — it is the shape of the problem. The hard instances have
speeds *close together*, so the periods `n/e_j` are all comparable and the bad intervals
overlap heavily. The induction needs each new speed to be fast enough that its period fits
inside the surviving gap, which is the opposite regime.

**The theorem and the frontier are disjoint.** Recorded so the route is not re-attempted as
though it were a candidate for the residual.

## 4. Honest position on the proof attempt

Three independent routes have now been measured to be **equivalent** to `|G| > 0` rather than
reductions of it: the denominator route (`N_d/d → |G|`, `RESIDUAL_ANGLE_v1` §1), the `Σα`
criterion at the extremum (exact equality, `RESIDUAL_ANGLE_v1` §3), and the crowding recursion
(§1 above). Pure positivity is impossible (`WHERE_THE_PROOF_IS_v2` §1). The interval induction
is a genuine non-measure argument but lands outside the hard region.

What the session produced is structure, not a proof: the case split derived rather than
assumed, the hard leaf (Unit-Complete) derived rather than assumed, the grid's limits made
sharp, and a cheap certificate covering the residual at `K=1` in a box. None of that carries a
quantifier over all tuples.

## 5. Ledger

`[PROVED]` §1 the uniform periodic form and the absorption of `a`; §2 the Step Lemma and the
growth condition, for general `n`.
`[VERIFIED — exact]` §2's step lemma (150 cases, 0 violations) and conclusion (1279 tuples,
0 empty good sets).
`[VERIFIED — exhaustive]` §3, 0 of 20 349 Case-2 tuples in `[1..18]` satisfy the condition.
`[SCOPE]` the growth condition is unconditional in the speeds; the 0% is a fact about the box,
and the disjointness argument in §3 is qualitative.
`[NOT NOVEL — assumed]` lacunary/geometric speed sets being easy is likely folklore; no
literature check was run, so no priority is claimed.

`n = 8` is **not proved.**
