# The divisibility test: what it proves, what it cannot, and the one critical set

2026-09-16. Tests the arithmetic-side idea proposed after Routes A and B were refuted — that shadowing a
flank demands a divisibility relation between that flank and the other differences, and that requiring it
at all seven flanks over-determines seven integers. Scripts: `experiments/n8/flank_divisibility_v1.py`,
`flank_overdetermination_v1.py`, `flank_critical_sets_v1.py`, `flank_saturation_bound_v1.py`.

**Existence at order 8 remains open, and the cascade gate still reports it unstated.**

---

## 1. The divisibility hook is real  `[PROVED — elementary]`

At flank `e` with integer differences, the ratio `d/e` in lowest terms is `a/c` with `c = e/gcd(d,e)`, and
the fraction of `e`'s openings it blocks depends only on `c`:

| `c` | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 12 | 16 | 20 |
|---|---|---|---|---|---|---|---|---|---|---|
| density (max over numerators) | 1/2 | 1/3 | 1/4 | 2/5 | 1/3 | 2/7 | 1/4 | 1/4 | 1/4 | 1/4 |

Small `c` — that is, **large `gcd(d, e)`** — blocks far more than the large-`c` limit of 1/4.

**`[CORRECTS the first draft]` Density is not a function of `c` alone.** It depends on the numerator as
well: at `c = 7` the numerators give 2/7 or 1/7, not 2/7 throughout. The row above is the **maximum** over
numerators, which is the safe direction for a *necessary* condition (it over-estimates blocking, so falling
short of the requirement really does forbid a shadow) — but it must not be read as the density of a given
ratio. The first draft of this section read it that way. Combined with
the forced overlap at opening `k = 0` (every ratio below 1 blocks it), shadowing `e` requires

    Σ_j density(e / gcd(d_j, e))  ≥  1 + (m − 1)/e,     m = #{ratios blocking k = 0}.

Two consequences, both exact:

- **`[CORRECTS the first draft]` The budget forbids `e = 4, 5, 7` — but not `e = 6`.** The first draft
  claimed it "forbids any shadow of the largest flank below `c = 8`", reasoning from six *generic*
  density-1/4 ratios. That reasoning imposed the large-`c` limit on small flanks, where the densities are
  higher (2/5 at `c = 5`, 1/3 at `c = 6`). Computed per ratio with actual numerators, over every subset of
  at most six of the available differences:

  | `e` | best achievable Σ density | requirement | budget forbids? | cover exists? |
  |---|---|---|---|---|
  | 4 | 1 | 3/2 | **yes** | no |
  | 5 | 1 | 8/5 | **yes** | no |
  | 6 | 3/2 | 3/2 | no (exactly met) | **no** |
  | 7 | 11/7 | 12/7 | **yes** | no |
  | 8 | 7/4 | 13/8 | no | yes |

  So counting explains three of the four empty cases. **`e = 6` is empty for a reason the counting does not
  capture** — the same lesson as §2, one flank earlier than I first saw it.
- **The eighth pattern is exactly saturated.** Its ratios `{1,3,4,5,7}/8` spend
  `1/4 + 1/4 + 1/2 + 1/4 + 1/4 = 3/2`, against a requirement of exactly `3/2`. It closes the gap only
  through `d = 4`, where `gcd(4,8) = 4` gives `c = 2` and density 1/2. The rigidity predicted for Route A
  is real and this is where it lives — in the overlap budget, not in uniqueness.

## 2. Why it does not close the problem  `[the test's own refutation]`

The condition is **necessary, not sufficient**, and the gap is not small. On the critical set
`{2,3,4,5,6,7,16}` at flank `16` — the one flank that is *free* —

    budget Σ density = 1/4 · 6 = 3/2 = 1.5000,   requirement 1 + 5/16 = 1.3125.

The budget is comfortably sufficient for a shadow, and the flank is free anyway. **Counting cannot predict
freeness once the budget is met; the arrangement of the blocked sets decides, not their sizes.** So the
over-determination argument cannot be completed in this form: there is no contradiction to derive at a
flank whose budget is satisfied.

Recorded plainly because the idea was this session's own proposal and the owner endorsed it on that
recommendation: it yields §1's theorem and does not reach Existence.

## 3. What the exhaustive search gives  `[PROVED — finite verification, scoped]`

Every 7-subset of `{1,…,30}`, tested exactly in integer arithmetic (a runner at difference `d` is in the
way at opening `k` of flank `e` iff `r = d(8k+1) mod 8e` has `min(r, 8e−r) < e`):

| `d_max ≤` | sets | no free flank | exactly one free flank |
|---|---|---|---|
| 18 | 31 824 | **0** | 1 |
| 22 | 170 544 | **0** | 1 |
| **30** | **2 035 800** | **0** | **1** |

> **Order 8, integer differences with `d_max ≤ 30`.** Every such runner has a free flank, hence a lonely
> instant (`lonely_iff_exists_flank`). Existence holds for every one of the 2,035,800 configurations.

**And the problem has exactly one tight case in that range**: `{2, 3, 4, 5, 6, 7, 16}`, free only at flank
`16`. Six consecutive integers plus one large difference; the set's overall gcd is 1. Every other set in two
million has at least two free flanks. That single configuration is what any uniform proof must survive, and
its shape — a near-AP block plus an outlier — is the extremal form this project keeps rediscovering.

**Scope.** Integer differences, seven distinct values, `d_max ≤ 30`. Sets with fewer distinct differences
carry strictly fewer blockers. Irrational and unbounded-`d_max` configurations are untouched by this.

## 4. The target in its arithmetic form

The search's own test is the cleanest native statement of what is left to prove. Opening `k` of flank `e` is
free exactly when, writing `u = 8k + 1` and `M = 8e`,

    d_j · u  mod  M  ∈  [e, M − e]   for every other difference d_j.

So **Existence at order 8 is: for every seven differences, some flank `e` admits a `u ≡ 1 (mod 8)`,
`0 < u < 8e`, with every `d_j u mod 8e` outside the central band.** A simultaneous-avoidance statement in
the framework's own vocabulary, with no measure, density or covering language in it. That is the form worth
attacking next, and the form worth formalising when one of its cases lands.
