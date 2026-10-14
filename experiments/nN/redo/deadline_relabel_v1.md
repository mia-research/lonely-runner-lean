# Pinch dilation, forced labels, and a directed separation exception

2026-09-30. Analytical branch: replacement of a clear event at a pinch.
Objects: clear phases, integer lap labels, forward openings and backward closings.
This does not prove global transport along an arbitrary AP deformation.

## Uniform seven-reading reduction

Suppose all seven readings are clear at t, with two distinct readings on the
opposite boundaries 1/8 and 7/8 modulo integers. At least one of 2t, 3t, 5t
has at most one captured reading.

For an old clear phase f in [1/8,7/8]:

- Capture at 2t forces f in (7/16,9/16), where both 3f and 5f are clear.
- Capture at 3t forces f in (7/24,3/8) or (5/8,17/24), where 5f is clear.
- Both original boundary phases remain clear under all three multipliers.

Thus the three capture sets are pairwise disjoint subsets of the remaining
five readings. They cannot each have two members. Integer lap labels do not
change the argument, since integer dilation preserves integer shifts.

Lean: `pinch_one_blocker`, `dilated_phase`, `pinch_one_blocker_readings` in
`LonelyRunner/LRC/Spec/DeadlineRelabelN.lean`.

**Consequence:** every such pinch has a three-candidate, at-most-one-blocker
description. This is uniform in the speeds and lap labels, not inferred from
sample success. It does NOT prove that moving the lone blocker preserves the
other readings, or that a replacement extends the deformation.

## The exact forward margin

At a candidate event T let the blocker have positive disparity b and signed
phase z in (-1/8,1/8) from its capture centre. Its forward displacement is
h = (1/8-z)/b. For another positive disparity d whose clear phase is g,
its CURRENT band is retained exactly when

    d(1/8-z) <= b(7/8-g).

This is `forward_margin_iff`. Clearance in some later band is not claimed
equivalent to retention of the current band.

## An understood failure and its repair

Use subject disparities

    (1/8, 7/8, 1/2, 100+1/3, 1/5, 7/16, 5/8)

and old t=1. All readings are clear; the first two pin the old window.
The unique blockers at multipliers 2,3,5 are respectively readings 3,4,5.
Their forward exits fail:

| Multiplier | Forward exit | A newly captured reading | Its phase |
|---|---|---|---|
| 2 | 9/4 | 7/16 | 63/64 |
| 3 | 7227/2408 | 5/8 | 16871/19264 |
| 5 | 45/8 | 7/8 | 59/64 |

These failures and unique-blocker statements are Lean regressions in
`experiments/nN/deadline_relabel_axioms_v1.lean`.

The feature causing the tripled failure is exact: disparity 5/8 is already
at phase 7/8 at t=3. A forward movement crosses its closing; a backward
movement enters its clear band instead. The blocker is at its capture centre,
so retreat to its preceding closing is forced as the nearest backward repair.

This repairs an infinite family, not only the example. Replace 100 by ANY
natural K, set b=K+1/3, and take

    T = 3 - 1/(8b).

Then 21/8 <= T < 3. The seven band labels are

    (0,2,1,3K,0,1,1).

The fast reading is exactly at 3K+7/8. The other six stay in these clear
bands throughout the retreat, as follows directly from the bounds on T.
`exception_backward_bands` and `exception_backward_clear` prove this for
every natural K, with a positive witness instant. The numbers are subject
disparities, not a claim that a physical runner must be stationary.

**Consequence:** separation direction matters. The forward-only implication
from the blocker-count theorem is false; this exception is explained and
resolved by the same band-boundary mechanism in the opposite direction.
The family theorem alone is not a universal selection rule or an assertion
about every straight AP deformation.

## Forced deadline relabelling

The earlier part of the module also proves that an opening beyond a deadline
U forces its label below floor(dU-1/8). Recomputing all labels there never
increases them and strictly decreases their sum if a conflict exists.
The OLD known event supplies the lower bound: this diagnostic may return
the old labels. Its finite descent is NOT progress toward a new isolation.

## Remaining analytical obligation

Determine from all seven readings whether one of the three candidates admits
a forward or backward separation, carrying both sets of margins explicitly.
No assertion that one must do so is made here. When both directions fail,
identify the readings whose opening/closing margins are exhausted before
proposing the next replacement. Global coverage remains open.

Verification: targeted module build and declaration-wide audit for this module
plus the three exact regressions; not the full Spec gate. No commit or push.
