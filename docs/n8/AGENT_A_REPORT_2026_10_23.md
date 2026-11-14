# Agent A report, 2026-10-23: AP landing law for an end subject, relative radius 1/32 and 1/16

Rules: 5 (no runner stationary; readings are differences from a positive-speed subject), 7 (no caps or move budgets used as lemmas; chain inequalities only), 8 (checked through the cascade's own path), 15 (exact Fractions; LP floats steered the tree only), 16 (new files only), 18 (grades below).

## Result

Both radii go through. [L] means Lean compiled with `[propext, choice, Quot.sound]` only, scan clean (0 sorry, native_decide, axiom, admit, unsafe), untagged Prop defs 0.

| radius (relative) | case-tree leaves | distinct landing instants | tree splits |
|---|---|---|---|
| 1/64 (existing) | 3 | 3 | 2 |
| 1/32 [L] | 5 | 5 | 4 |
| 1/16 [L] | 6 | 6 | 5 |

Cascade-path types seen by sampling (path plus clear-window integers, [OBS]): 3 at 1/64 (20,000 points), 5 at 1/32 (300,000 points), 9 at 1/16 (100,000 points). The sampling count at 1/16 exceeds the leaf count because several cascade paths share a landing instant: a leaf is a valid zone chain, and a chain valid on a region fixes the first lonely instant there whatever path the cascade takes. The earlier probe's counts (4 paths at 1/32, 8 at 1/16) differ from these sample counts; the 5th type at 1/32 lies on a measure-zero face (below), which the earlier sampling did not hit.

## Chambers (relative readings x_i = i + e_i, |e_i| <= r; first lonely instant T)

Notation: the strict/weak shape is exactly as proved; the first tree hypothesis that fails gives its boundary to the other side.

Radius 1/32 (apLawR2_core_32):
1. `x7 <= 7 x1` (i.e. 7 e1 - e7 >= 0): no moves, T = (0+1/8)/x1.
2. `7 x1 < x7`, `3 x5 <= 5 x3`: 6 moves, T = (1+1/8)/x3.
3. `7 x1 < x7`, `5 x3 < 3 x5`, `7 x7 < 25 x2`, `31 x2 < 9 x7`: 11 moves, T = (3+1/8)/x5.
4. `7 x1 < x7`, `5 x3 < 3 x5`, `7 x7 < 25 x2`, `9 x7 <= 31 x2` (31 e2 - 9 e7 >= 1): 9 moves ending (2,1), T = (1+1/8)/x2. NEW.
5. `7 x1 < x7`, `5 x3 < 3 x5`, `25 x2 <= 7 x7`: 8 moves ending (7,3), T = (3+1/8)/x7. NEW, but see below.

Radius 1/16 (apLawR2_core_16): chambers 1 and the same four with one more split `x5 * 7/8 < x4 * 9/8` (ov4: 7 x5 < 9 x4, i.e. -9 e4 + 7 e5 < 1) on the "x7 > 7 x1" side:
- ov4 holds: chambers 2 to 5 as above (6, 11, 9, 8 moves).
- ov4 fails (`9 x4 <= 7 x5`): 3 moves ending (5,1), T = (1+1/8)/x5. NEW.

## Does anything other than "one more linear inequality per new chamber" appear?

[L]/[OBS] at 1/32 and 1/16: no. Every new chamber is cut out by one new linear inequality in the x_i with a constant term in the e-form:
- chamber 4: `31 e2 - 9 e7 >= 1` (the task's predicted boundary; the 11-move chain's overlap x2*(4-1/8) < x7*(1+1/8) is its failing inequality). It is non-empty in the box exactly when (31+9)/8 r > 1/8, i.e. r > 1/40 (arithmetic).
- chamber 5: `-25 e2 + 7 e7 >= 1`. Over the box |e|<=r the maximum of -25 e2 + 7 e7 is 32 r, so at r = 1/32 the set is the face e2 = -1/32, e7 = +1/32 (codimension 2, measure zero), and it gains positive measure only for r > 1/32. The 8-move type appeared in sampling at 1/32 only because the sampler hits exact box faces.
- ov4 fails: `-9 e4 + 7 e5 >= 1`; maximum 16 r, so at r = 1/16 the set is the face e4 = -1/16, e5 = +1/16 (measure zero); positive measure for r > 1/16. The 3-move chamber is therefore a boundary-face case at 1/16.
No chamber needed a non-linear form, and no lap integer changed inside a leaf: the window integers are fixed per chain and every window inequality (weak, linear) was discharged by `linarith` from the box and the tree hypotheses. The thresholds 1/40, 1/32, 1/16 at which chambers 4, 5 and the 3-move chamber become non-empty are where the corresponding linear form first meets the box.

## Where it stops (exploration, [OBS])

The tree builder `ap_r2_tree_v1.py 8` (radius 1/8) hit its depth cap of 14 without finishing; the splits then include window inequalities (`wlo`, `whi`) as well as overlaps, and the builder re-enters regions with slivers. Not diagnosed whether the tree is finite at 1/8; nothing was attempted in Lean beyond 1/16. No claim is made about radius 1/8 or larger.

## Verification beyond Lean (exact Fractions, [OBS])

`ap_r2_verify_v1.py`: the leaf T formula equals the cascade's first lonely instant (exact) at all 128 box corners, 60,000 random points, random points on every split hyperplane, the hyperplane/box vertices, and offsets of +-1e-6 either side: 80,144 checks at 1/32 and 92,107 at 1/16, 0 mismatches. The partition itself (no gaps, no overlaps beyond boundaries, boundary ownership) is proved by the Lean case tree: each split is `lt_or_ge` / `le_or_gt`, so each point lies on exactly one branch, and a strict chain inequality that fails passes the point to a branch carrying the weak complement.

## Files created

Lean (in `/Users/trentpalelei/Desktop/Math Ex/LonelyRunnerFresh/Fresh/`, all GENERATED, all compiled one at a time with `./check.sh`):
- `APLawR2_Chain.lean`: `apLawR2_chain_m0, m3, m6, m8, m9, m11`. Each takes positivity of x1..x7 and every chain inequality (overlaps strict, end windows weak) as hypotheses and proves "Clear7 at T and no earlier instant is Clear7". Radius-free. [L]
- `APLawR2_Core32.lean`: `apLawR2_core_32` (hypotheses |x_i - i| <= 1/32; conclusion: exists T, 0 < T, Clear7 at T, none earlier, and a 5-way disjunction of chamber conditions with T). [L]
- `APLawR2_Core16.lean`: `apLawR2_core_16`, 6-way disjunction. [L]
- `APLawR2_End32.lean`: `apLawR2_end0_32`, `apLawR2_end7_32` (FirstIso v 0 T / v 7 T from relative readings within 1/32), and `apLawR2_end0_speeds_32`, `apLawR2_end7_speeds_32` (speeds within 1/64 of c + i). [L]
- `APLawR2_End16.lean`: the same four at 1/16 (speeds within 1/32). [L]

Each of the 14 theorems named above prints `[propext, choice, Quot.sound]` under `#print axioms`. The long theorems carry `set_option maxHeartbeats 8000000 in`.

Scripts (in `/Users/trentpalelei/Desktop/Math Ex/experiments/n8/`): `ap_law_gen_r2_v1.py` (the Lean generator; `ap_law_gen_v1.py` kept), `ap_r2_tree_v1.py` (case-tree builder), `ap_r2_explore_v1.py` (type sampler), `ap_r2_verify_v1.py` (exact verification). The tree builder uses LP floats to choose splits and sample points; the soundness of each leaf is the Lean check, not the LP.

## Not proved / owed

- The statements give `FirstIso` (first lonely instant for the subject) at the listed T; the `Lands` form was not added (same as the existing `apLaw_end0/7`).
- Interior subjects at radius 1/32 or 1/16 (the ratio-condition route of `APLawAll`) were not extended; `ap_nbhd_firstIso` is unchanged.
- Radius 1/8 and larger: not done (see above).
- The chamber list is a certificate of cover, not a proof that each leaf has positive measure; the measure statements above are arithmetic on the linear forms, [OBS] unless a reader recomputes them.
