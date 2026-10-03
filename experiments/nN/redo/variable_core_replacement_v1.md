# Variable core: one full replacement mechanism region

3 October 2026. Module: `VariableCoreReplacementN.lean`.

## Result

The core is no longer fixed. Each of its six positive disparities d_i can
vary independently over the intervals below. For every such choice, and every
inserted disparity V >= 19/3, the subject has a positive isolation time at
threshold 1/8. In particular this includes every V at least the largest core
reading, since d_4 and d_5 are at least 19/3.

| Index | Lower bound | Upper bound |
|---|---:|---:|
| 0 | 1 | 350/337 |
| 1 | 25/9 | 125/37 |
| 2 | 170/43 | 1300/301 |
| 3 | 3300/653 | 575/111 |
| 4 | 19/3 | 2350/337 |
| 5 | 19/3 | 2350/337 |

All intervals have strictly positive width. The theorem does not need ordering
or distinctness; restricting to ordered distinct readings is allowed. The
last two intervals overlap, so an ordering restriction should not be silently
inferred from their table indices. The original core belongs to this region.

These are six independently variable readings before quotienting scale, not
six additional factors beyond the earlier normalisation. Pinning the minimum
to 1 leaves five core ratios plus the inserted reading's ratio: the usual six.

## How the region is derived

In eighth-time R=8t, choose four subwindows:

    [1,1001/1000], [43/10,111/25], [653/100,337/50], [9,903/100].

Their core lap vectors are respectively

    (0,0,0,0,0,0), (0,1,2,2,3,3),
    (0,2,3,4,5,5), (1,3,4,5,7,7).

For a window [A_w,B_w], clearance throughout it on lap q_wi is guaranteed by

    (8*q_wi+1)/A_w <= d_i <= (8*q_wi+7)/B_w.

For each reading, take the maximum of the four lower bounds and the minimum
of the four upper bounds. This produces the table, not a sampled perturbation
radius. Lean proves the whole intervals clear for every core in the region.
The chosen subwindows are a proof design choice, not a claim of optimality.

## Forced replacement, uniformly over the region

If an early window survives adding V, it supplies the full isolation. If all
three are swallowed, their endpoint inequalities force

    K_1=1, K_2=4, K_3=6,
    310/43 < V < 2450/337.

The derivation eliminates arbitrary integer labels using the same finite
capture-width argument as the fixed-core proof; no scan is used. The constants
are slightly wider than before because the early windows were shortened.

For every speed in this residual interval:

- If 65 <= 9V, use R=9.
- Otherwise use R=65/V, the added reading's lap-8 exit.

Lean verifies 9 <= R <= 903/100 and 65 <= V*R <= 71. The fourth window already
keeps all six variable core readings clear there. This proves `family_isolated`.

## Scope and boundary

This is a complete, uniformly solved region with variable core ratios and an
unbounded inserted speed. It is not a proof that arbitrary cores fall in the
region. Common rescalings preserve the mechanism with inverse-rescaled times.

Leaving a table interval means one of these fixed subwindows can lose the
specified lap clearance. It does not mean isolation is lost, or even that the
larger moving window is gone. The next classification must allow those window
endpoints or their labels to change and cover the complementary core regions.

## Verification

Targeted Lean build and full audit of this module's nine declarations, plus
three regressions: nondegenerate intervals, original-core membership, and an
inserted speed of 1000. No full Spec gate, no commits, no pushes.
