# The largest flank: a candidate route to Existence

Following the `|J| = 3` withdrawal, the question reframed correctly. A shadowed flank is harmless —
**Theorem 6.8 says the subject is lonely iff *some* flank has a lonely opening.** So the object is not
whether flanks shadow, but whether a subject can have *all* of them shadowed.

## The measurement

Over 4,000 arrangements, 32,000 subjects, clear flanks per subject (of 7):

| clear flanks | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|
| subjects | 2 | 22 | 374 | 4,344 | 27,258 |

**Never 0, 1 or 2.** Minimum 3, and Existence needs 1. Adversarial hill-climbing to *minimise* the
count also bottoms out at 3.

Checking the cutoff on the minimiser (`[7,48,107,125,136,144,145,146]`, subject 4): the three clear
flanks clear at `k = 2, 5, 2`, and the three shadowed live flanks are genuinely shadowed to
`k = 200,000`. The count is real, not an artefact of a short scan.

## The pattern, and the claim it suggests

In that minimiser the clear flanks are the **large** differences `129, 88, 29` and the shadowed ones
the **small** `8, 9, 10`. Clear-rate by rank of `|e|` over 48,000 subjects:

| rank of `|e|` (0 = largest) | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| clear | **100%** | **100%** | **100%** | 99.97% | 99.74% | 98.06% | 89.52% |

**The three largest flanks were clear in every one of 48,000 subjects** — which is exactly why the
minimum clear count is 3.

> **Candidate: the flank at a subject's largest `|difference|` is always clear.**
> **If provable with an index bound, that is Existence at order 8.**

## Attacked, not merely sampled

Sampling misled twice in this thread, so the claim was attacked:

- **Hill-climbing** to *maximise* the first-clear index of the largest flank, 80 restarts: the index
  reached **91**, and the flank was **never** shadowed.
- **Structured families** — arithmetic progressions, geometric-ish, powers of two, near-equal, and
  half-integer-heavy arrangements: **0** shadowed.

## The gap, stated precisely

Two things are missing, and the second is the one that sank Prop 6.11.

1. **A proof.** Nothing above is proved. The mechanism is plausible — at the largest flank every ratio
   satisfies `|ρⱼ| ≤ 1`, so the movers sit on `ρⱼ·(k + 1/8)` with `|ρⱼ| < 1` — but that is a
   description, not an argument, and an attempt to estimate the first clear index from the smallest
   `|ρ|` gave `≈ 0.64` where the observed value was `91`. **The estimate is wrong and the mechanism is
   not understood.**

2. **An index bound.** The first clear opening is **not** small: adversarial search reaches `k = 91`,
   and whether it is bounded at all is unknown. Prop 6.11 was withdrawn for naming an opening without
   bounding it; this claim would fall the same way without a bound.

## Status

`[VERIFIED]`: the largest flank clear in 48,000 random subjects, plus adversarial hill-climbing (80
restarts, max index 91, none shadowed) and five structured families (0 shadowed).
`[VERIFIED]`: minimum 3 clear flanks per subject, random and adversarial, with the cutoff checked to
`k = 200,000` on the minimiser.
`[OPEN]`: the claim itself, and the index bound. Existence at order 8 unchanged.

**This is the strongest candidate route in the record**, and it is a candidate — not a result.
