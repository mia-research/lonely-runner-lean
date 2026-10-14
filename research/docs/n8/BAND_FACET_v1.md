# The failure facet, and a correction

Continues `SMALL_B_ANCHOR_v1.md`. **One claim in that document is withdrawn.** The failures turn out
to be exactly structured, and they name the facet.

## Correction — the `b ≥ 28` threshold is withdrawn

`SMALL_B_ANCHOR_v1.md` reported that the rounding route works for `bᵢ ≥ 28` and that "the derivation
predicted its own breakdown point" (0 failures at 28, 40 at 12, 121 at 8). **Both halves of that were
artefacts of the test.**

1. The test searched for the order-7 witness on a grid of denominator `8m`, which often misses it.
   When it did, the script counted "no witness found" as "the route failed". Using the normalised
   witness set (`ReachRule.witness_normalised`, denominators `7s`) instead, the route succeeds far
   below 28 — down to `bᵢ ≥ 8`.
2. The population was unrepresentative. The category splits on whether `lcm(bᵢ) = m`, and the sample
   at `b ≥ 28` was almost entirely the easy half. Restricted to `lcm(bᵢ) = m` the original test fails
   at *every* threshold, including 28.

The derivation of `28` as a *sufficient* margin is still correct arithmetic — `1/7 − 1/8 = 1/56` and
the rounding cost `1/(2bᵢ)` — but it is conservative, and the empirical "confirmation" of it was not
a confirmation of anything. The lesson is the one already on file: **split the population on the
structural variable before reading a threshold off it.**

## The facet — every failure carries `b = 2`

Combined route, exhaustive over all divisor-closed profiles with `m < 400`: 103,060 profiles, **603
not settled**. Of those 603:

| | failures | successes |
|---|---|---|
| smallest `bᵢ = 2` | **100.0%** | 31.2% |
| contains some `bᵢ ≤ 7` | **100.0%** | 85.0% |

`b = 2` means `s = m/2`, and by `Rescale.small_b_blocks_iff` its condition is exactly **`q` odd**.
The rounding route is structurally blind to it: the rounding error is `1/(2b) = 1/4` at `b = 2`,
which swamps the entire margin of `1/24`. **The route fails precisely where the exact law applies and
rounding has no purchase.** The two regimes are not alternatives to choose between; a proof must
combine them.

Combining by shifting `q` through multiples of `lcm` of the large `bᵢ` — which preserves every large
condition — moves 603 to **583**. Barely anything, and the reason is structural: that `lcm` is
usually `m` itself, so at most one shift fits in a range of length `3m/4`.

## What a worked failure shows

`m = 60`, `b = [2,3,5,10,12]`. The conditions are `q` odd, `3∤q`, `5∤q`, `q mod 10 ∈ [2,8]`,
`q mod 12 ∈ [2,10]`, `q mod 60 ∈ [8,52]`. Solving them by hand gives `q = 17`, and
`t = 17/60` satisfies `‖sᵢt‖ ≥ 0.283` for all six speeds — comfortably an order-7 witness.

**So the profile was never the problem; the route was.** It rounds *the normalised* witness rather
than searching the clear set, and `17/60` is not of the form `A/(7s)`.

## A sufficient condition from our own gap rule

That reframes the target: the order-7 clear set must contain a point of the grid `q/m`, so it needs a
clear interval at least `1/m` wide. `GapRule.gap_ge` bounds exactly that — gaps are `≥ 1/(sᵢsⱼ)`, and

> `1/(sᵢsⱼ) ≥ 1/m` ⟺ **`sᵢ·sⱼ ≤ m` for every pair.**

**Verified:** of 103,060 divisor-closed profiles, 4,229 satisfy it and **all 4,229 have a grid
witness — 0 failures**, as derived. Sound, and derived from the framework's own gap rule rather than
from rounding.

**It is also weak: 4.10% coverage**, and 100% of the complement has a grid witness anyway. Stated as
weak. It is a genuine sufficient condition, not a closure of the category.

## Where this leaves the category

Divisor-closed remains open. What is now known about it:

- the reduction to unit constraints is proved (`divisor_reduces`);
- `b ≤ 7` obeys an exact law (`small_b_blocks_iff`), and the all-`b ≤ 7` sub-category is closed;
- rounding routes work for large `b` but are blind at `b = 2`, which is where **every** failure sits;
- the gap rule gives a sound but weak grid criterion, `sᵢsⱼ ≤ m`.

The open piece is sharply stated: **make the small-`b` congruences and the large-`b` intervals hold
simultaneously.** The obstruction is parity at `b = 2`, not a shortage of witnesses.
