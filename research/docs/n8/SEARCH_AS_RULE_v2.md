# The search, converted into a rule — v2

Supersedes `SEARCH_AS_RULE_v1.md`. Nothing in v1 is withdrawn; v2 closes v1's stated open item and
carries the chain three steps further. **16 theorems, all axiom-clean, zero `sorry`. No statement
below mentions 8.**

Artefacts: `experiments/n8/GapRule_v1.lean` (3), `experiments/n8/ReachRule_v1.lean` (10),
`experiments/n8/ArithForm_v1.lean` (2), plus `gap_rule_v1.py`, `reach_rule_v1.py`,
`finite_check_v1.py`.

---

## The chain

Each step was reasoned out of the one above it, not guessed.

**1. The gap rule.** For integer readings, the gap between consecutive bad intervals has width
exactly `N/(s·s')` with `N = s(nm'−1) − s'(nm+1)` an **integer**; a gap means `N ≥ 1`. So no gap is
exactly the integer inequality `s(nm'−1) ≤ s'(nm+1)`.
`GapRule.gap_eq`, `gap_ge`, `no_gap_iff`. *(126,258 gaps, 4,000 profiles, 0 violations.)*

**2. The reach rule.** The sweep's single accumulator certifies coverage below itself, with **no
sortedness hypothesis**. `ReachRule.le_reach`, `covered_below_reach`, `covers_of_reach_gt`.

**3. The converse — v1's open item, now closed.** On a sorted list the reach is **uncovered**, so
the fold is an `↔`: `[r,N]` is covered **iff** the reach passes `N`, and when it does not, the fold
*returns the leftmost lonely point*. `ReachRule.reach_uncovered`, `reach_decides`,
`uncovered_witness`.

> Where sortedness enters is not incidental and the forward proof predicted it: **only** in the
> branch where the scan stops. If the scan halts at `r` because the next interval starts at `a ≥ r`,
> every later interval also starts at `a' ≥ a ≥ r`. That one step is the entire use of the order.

**4. What the witness is.** The recursion only ever assigns `r` its start value or the right endpoint
of an interval it crossed. So the witness is `r`, or some `(n·m+1)/s` — a rational whose
**denominator divides a reading**. `ReachRule.reach_mem`, `reach_in_endpoints`, `reach_denom`.

**5. The continuum is removable.** Combining 3 and 4: covering `[r,N]` is equivalent to covering a
**finite list of explicitly named points**. No quantifier over the reals remains on either side.
`ReachRule.finite_check`. *(Measured candidate-set size at n = 8, readings < 60: min 27, median 123,
max 242.)*

**6. And no division remains either.** At a point `A/s`, "within 1 of a multiple of `n`" is the
integer inequality `|A − nks| < s` — equivalently the residue condition
`s'·A mod n·s ∈ (−s, s)`. `ArithForm.near_iff_int`, `covers_iff_int`.
*(374,522 candidate points across 3,000 profiles: integer form vs real form, 0 mismatches. The
resulting finite congruence check vs the full interval sweep: 0 mismatches on 3,000 profiles.)*

## Where that leaves it

> **For integer readings, at any order `n`, deciding whether `[1, n−1]` is covered is a finite
> conjunction of integer inequalities over an explicitly enumerable candidate set — proved
> equivalent to the real statement, not approximating it.**

No enumeration of the continuum, no sampling, no floating point, no appeal to order 8. The search
was never doing anything else; it just was not saying so.

**Boundaries, stated plainly.** This decides a *fixed* profile. It does not quantify over profiles,
so it is not Existence and does not bear on it. Its scope is integer readings. What it changes is
the cost, the exactness, and the *form* of every covering question downstream — the question is now
posed in `ℤ`, where congruence and counting tools apply and interval arithmetic does not.

## Carried forward from v1

**Retraction (stands).** The gap rule gives a smallest possible gap of `1/H²` for readings `≤ H`, so
Branch B has **no uniform floor** — a gap of `1/3080` exists at readings `55, 56`. The `53/462`
figure is a statement about readings `≤ 40`. It was never a bound. The readings-to-200 search was
stopped: the rule answers what it was going to measure, and more sharply.

## Open

- Whether the `H⁻²` decay in step 1 is attained infinitely often, or only up to some bound on `k`.
- The candidate set has size `≈ Σᵢ (n−1)sᵢ/n`. Whether it can be thinned — most candidates are
  covered by an obvious reading — is untested.
- Whether the congruence form of step 6 supports a counting argument over profiles. Untried. This is
  the first point in the chain where a statement about *all* profiles could even be phrased in the
  right category.
