# Thin two-plus-six packet strip

Rules: 1–4, 8–18. New all-subject assembly, reusing the established native single-slow opening and complete S2 frozen-six proof. It does not count the six frozen subjects as a new unknown family.

## Exact statement

For every real `b>0`, speeds

`c, c+1, c+A, c+A+b, ..., c+A+5b`

have isolation for every subject when the **original gap** `g=A−1` satisfies the closed polynomial conditions

`4 ≤ 3g` and `40b ≤ g(6−5b)`.

These imply `g>0` and `b<6/5`. With positive original steps `u,v`, the equivalent homogeneous conditions are `4u≤3g` and `40uv≤g(6u−5v)`. `TwoSixThinClass` additionally retains positive distinct physical speeds, arbitrary signed affine scale, mirror, drift and labels.

## Source and interplay

For either low subject the six positive readings are `x+j b`, `0≤j≤5`, with `x≥g`; the other low reading has magnitude1. The selected named boundary is `OpeningClump.openingAfter x (1/8)`. Its exact established bounds are `1/8≤T≤1/8+1/x`. The first condition retains the magnitude1 reading in its AP band. The second is exactly the algebraic sufficient condition

`5b(1/8+1/x)≤3/4`.

It places every packet reading in the same opening band. Monotonicity from `g` to either actual `x` is proved symbolically; no individual candidate-time certificate is assumed as the arrangement type.

For the six upper subjects, the same exact normalized twoMover/display permutation assembly as `TwoSixNine` invokes the existing S2Complete cases. There is no extra first-AP-window fit restriction on these already proved subjects. All seven readings remain in every physical isolation statement.

## Relation to prior sufficient classes

The strip extends below the gap9max family. For instance `b=1/8,g=4/3` satisfies both thin inequalities, while `g<9max(1,b)`. It also fails the upper-role separation condition in the existing sufficient `UnequalTwoAPBlockClass` at p2: that condition forces `g≥20b=5/2`. No assertion is made that every point in the strip was absent from every earlier class; the novelty is this complete symbolic all-subject assembly with the unnecessary frozen-role gap removed.

At `b≤6/35`, the first inequality's boundary `g=4/3` already satisfies the polynomial condition. More generally this source proves `g≥max(4/3,40b/(6−5b))` for `0<b<6/5`. Neither expression is asserted to be a necessary or optimal bound. Unequal-step closer-gap arrangements outside all established classes remain a complement.

## Exact regression and check manifest

Run `python3 experiments/n8/two_six_thin_v1.py`.

- 624 actual original-cascade subject controls.
- 156 named low opening controls.
- 13 rational step ratios from1/1000 to119/100, including both sides of6/35, 3 exact gap factors, 2 physical scales and all8 subjects.
- Zero exceptions; maximum observed6 cascade moves is diagnostic only.
- Exact paths, setters, candidates and landings saved in `two_six_thin_v1.json`.

`./check.sh Fresh/TwoSixThin.lean` passed warning-free. Each endpoint prints exactly `[propext, Classical.choice, Quot.sound]`:

- `Fresh.TwoSixThin.two_six_low_thin`
- `Fresh.TwoSixThin.two_six_thin_all_subjects`
- `Fresh.TwoSixThin.twoSixThin_isolation`

The source scanner found zero sorry/native_decide/axiom/admit/unsafe declarations. No gates, pins, prior APIs or other agents' files were edited. No full n=8 claim is made.
