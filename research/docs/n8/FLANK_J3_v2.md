# `|J| = 3`: both parts of v1's reduction withdrawn

`FLANK_J3_v1.md` claimed a two-part reduction. **Both parts are wrong**, and the second is wrong
*because* of the first. What survives is a structural characterisation, which is stated below and is
not a finite list.

## Part 1 is false — refuted by construction

v1: *"every shadowed `|J| = 3` flank has all fractional parts of denominator `≤ 4`; a denominator
`≥ 5` forces a clear opening at index `≤ 8`."* Based on 2,648 sampled live flanks, 0 exceptions.

**Counterexample class, constructed directly: 256 shadowing configurations of the form
`(1/2, 1/2, denominator-5)`.**

The mechanism is elementary and should have been checked before the claim was made. A mover with
`f = 1/2` takes two values, `c` and `c + 1/2`, so it is bad on **at most one parity class of `k`** —
and on exactly one when its whole class `w ∈ {0,7}` (even `k`) or `w ∈ {3,4}` (odd `k`). **Two half-
movers on opposite parities cover every `k`, and the third mover is irrelevant whatever its
denominator.**

So the "0 exceptions" measured what random arrangements *produce*, not what configurations *permit*.
That distinction is the same sampling trap as before, and the fix is the same: construct the
adversarial case rather than sample for it.

## Part 2 is withdrawn as incomplete

v1 enumerated `5³ × 8³ = 64,000` configurations and reported **12** shadowing multisets — but that
space was restricted to denominators `≤ 4` **on the strength of Part 1**. Re-enumerated over
denominators `≤ 8` (906,752 configurations):

> **1,688 shadowing configurations in 46 fractional-part multisets**, and the count **grows with the
> denominator bound**, because `(1/2, 1/2, X)` shadows for every `X`.

`|J| = 3` is **not** reduced to a finite list. v1's table of 12 is a correct enumeration of a space
that was chosen wrongly.

## What survives, and it is structural

- **No single mover shadows a flank alone.** Over all `(w, f)` with denominator `≤ 8`, **zero** movers
  have a bad set equal to all of `ℤ/q`.
- **Exactly four whole-classes make a half-mover block a parity**: `w ∈ {0,7}` block even `k`,
  `w ∈ {3,4}` block odd `k`; `w ∈ {1,2,5,6}` block neither.
- **The dominant shadowing mode is two half-movers on opposite parities**, which covers `ℤ`
  regardless of the third mover — `(1/2,1/2,X)` at 64 configurations for each `X`, plus 144 for
  `(1/2,1/2,1/2)`.
- Shadowing without a half-mover pair is possible but restricted: the thirds shadow among themselves
  (`(1/3,1/3,1/3)`, `(1/3,1/3,2/3)`, `(1/3,2/3,2/3)`, `(2/3,2/3,2/3)`), which is three movers covering
  `ℤ/3`.

So shadowing at `|J| = 3` is exactly *the three blocked-residue sets covering the lcm-cycle*, and the
useful content is which movers can contribute a large blocked fraction — the half-movers at four
whole-classes being the extreme case.

## What is still true about arrangements, and is now a question

The measurement stands as a statement about its own object: in 2,648 live `|J| = 3` flanks drawn from
random 8-speed arrangements, **no shadowed flank had a denominator `≥ 5`**. Configurations permitting
it exist. So either such arrangements are rare in that sample, or arrangements cannot realise the
configuration.

**That is a real question and it was hidden by the false claim**: is there an arrangement-level
constraint preventing two half-movers on opposite parities from co-occurring with a high-denominator
third at the same flank? Not investigated.

## Status

`[WITHDRAWN]`: v1's Part 1 (denominator bound) and Part 2 (12-multiset finite list).
`[EXHAUSTIVE]`: 906,752 configurations at denominators `≤ 8` — 1,688 shadowing, 46 multisets, growing.
`[VERIFIED]`: the structural facts above, over the same range.
`[OPEN]`: `|J| = 3`, unreduced. Existence at order 8 unchanged.
