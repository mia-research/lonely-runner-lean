# The search, converted into a rule

**Question asked:** is there a way to convert what the search is doing into a rule or mechanism so
it could be generalised?

**Answer: yes, and it splits cleanly in two.** The search does two things — it decides whether a
junction between consecutive bad intervals leaves a gap, and it sweeps left to right accumulating
how far the intervals have reached. Each half has a closed-form rule. Both rules are proved in Lean,
axiom-clean, and **neither statement mentions 8**.

Artefacts: `experiments/n8/GapRule_v1.lean` (3 theorems), `experiments/n8/ReachRule_v1.lean`
(3 theorems), `experiments/n8/gap_rule_v1.py`, `experiments/n8/reach_rule_v1.py`.

---

## 1. The gap rule — what a junction costs

A bad interval of reading `s` at level `m` ends at `(nm+1)/s`; the next, of reading `s'` at level
`m'`, begins at `(nm'−1)/s'`. The width between them is

```
    (nm'−1)/s' − (nm+1)/s  =  N / (s·s'),      N = s(nm'−1) − s'(nm+1)
```

and for **integer** readings `N` is an **integer** (`GapRule.gap_eq`). A gap means `N > 0`, hence
`N ≥ 1`, hence

> **every gap has width exactly `N/(s·s')` with `N ≥ 1`, so at least `1/(s·s')`** —
> `GapRule.gap_ge`.

And the covering condition at that junction is the **integer** inequality
`s(nm'−1) ≤ s'(nm+1)` — `GapRule.no_gap_iff`. Not an inequality over `ℝ` that happens to have
rational data; an inequality over `ℤ`.

**Measured.** 126,258 gaps across 4,000 profiles: width `= N/(s·s')` in every case, `N ≥ 1` in every
case, zero violations. The Branch-B minimiser `[3,4,5,7,11,24]` has all four of its gaps at `N = 1` —
`1/168, 1/44, 1/44, 1/168`, summing to `53/924`, exactly half the joint `53/462` (the halving is
`Guard.block_periodic`).

**Consequence, and it is a retraction.** For readings bounded by `H`, the smallest possible gap is
`1/H²`. So **Branch B has no uniform floor**: the minimum uncovered length decays like `H⁻²`, and a
gap of `1/3080` was found directly at readings `55, 56`. The figure `53/462` recorded earlier is a
statement about **readings ≤ 40**, nothing more. It was never a bound.

## 2. The reach rule — what the sweep proves

Strip the bookkeeping from the sweep and one number remains:

```
    reach r []            = r
    reach r ((a,b) :: t)  = if a < r then reach (max r b) t else r
```

> **Everything from the start up to the reach is covered** — `ReachRule.covered_below_reach`.

The proof needs **no sortedness hypothesis**: the fold is sound on any list, and sorting only makes
it sharp. `ReachRule.le_reach` says the reach never retreats; `ReachRule.covers_of_reach_gt` turns a
reach past the far end into coverage of the whole interval.

**Measured.** Against the search on 4,000 random integer profiles at `n = 8`: **0 verdict
mismatches**, and in every uncovered case the reach is *exactly the first uncovered point*. The same
code runs unchanged at `n = 7, 9, 11, 13`.

## 3. What the two together give

The sweep's only operations are the comparison `a < r` and the update `max r b`. By §1 each of those
is, after clearing denominators, a comparison of **integers**. So:

> **For integer readings, deciding whether `[1, n−1]` is covered is a single left-to-right fold in
> exact integer arithmetic, of length `Σᵢ (n−1)sᵢ/n + O(k)`.**

That is the generalisation. There is nothing to enumerate, nothing to sample, no floating point, and
no appeal to order 8. The search was never doing anything else; it just was not saying so.

**What it does not do.** It decides a *fixed* profile in one pass. It does not quantify over
profiles, so it is not Existence and does not bear on it. What it changes is the cost and the
exactness of every covering question downstream, at any order.

## 4. Open

- The converse of `covered_below_reach` — that the reach *is* the first uncovered point — is measured
  (4,000/4,000) and not proved. It needs the sortedness hypothesis the forward direction does
  without. That is the next Lean target here.
- Whether the `H⁻²` decay in §1 is attained infinitely often, or only up to some bound on `k`.
