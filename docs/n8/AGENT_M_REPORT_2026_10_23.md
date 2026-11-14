# Agent M report, 2026-10-23: near-tight landing law at T1 = (1,2,3,4,5,7,12) and T2 = (1,4,5,6,7,11,13)

Rules: 5 (no runner stationary: readings are differences from a positive-speed subject; the arrangement statements use speeds c + a_i with c a free real), 7 (chain inequalities only, no caps or move budgets as lemmas), 8 (landing is the cascade's own first lonely instant), 15 (exact Fractions; no floats), 16 (new files only; nothing committed), 18 (grades below).

[L] = Lean compiled with `[propext, choice, Quot.sound]` only; scan 0 sorry/native_decide/axiom/admit/unsafe; untagged Prop defs 0 (each file one at a time with `./check.sh`; driver `tightlaw_build_v1.sh` reads the printed lines). Scripts are [OBS].

## Lean results (new files in `/Users/trentpalelei/Desktop/Math Ex/LonelyRunnerFresh/Fresh/`, 80 files, GENERATED)

Speeds within `rho/2` of `c + a_i`, `a = (0,1,2,3,4,5,7,12)` (T1) or `(0,1,4,5,6,7,11,13)` (T2); relative readings within `rho` (box a superset of the reachable deviations). Per radius: `TightLaw_<T>_<den>_Chain{A..}`, `_Leaves{A..}`, `_Core`, `_Arr`. Statement of the `_Arr` theorem `tightLaw_<T>_<den>_end_0 (c) (v : Fin 8 -> R)` with hypotheses `|v i - (c + a_i)| <= 1/(2 den)` for the eight i: `exists T > 0, FirstIso v 0 T /\ (T = (M + 1/8)/(v i - v 0) for one of the listed (M,i))`. The core theorem `tightLaw_<T>_<den>_core` is the same for seven readings in the box about `T_i`.

| radius rho | T1 [L] | T2 [L] |
|---|---|---|
| 1/64 | 3 leaves, 3 chain theorems | 14 leaves, 13 chain theorems |
| 1/32 | 5, 5 | 26, 25 |
| 1/16 | 7, 7 | 46, 44 |
| 1/12 | 11, 11 | not compiled (67 chain types; ~1 h estimated, stopped) |
| 1/10 | 15, 15 | not compiled |
| 1/8 | 20, 19 | not compiled |
| 1/6 | 24, 21 | not compiled |
| 1/5 | 52, 39 | not compiled |

Totals: 202 chain theorems, 223 leaf lemmas, 11 arrangement theorems (T1: 1/64, 1/32, 1/16, 1/12, 1/10, 1/8, 1/6, 1/5; T2: 1/64, 1/32, 1/16), every one printing the standard axioms. Soundness is the Lean case tree; the exact audit `ap_r4_verify_v1.py` (box + path implies every chain inequality; formula = cascade's first lonely instant at corners, random, on-wall, vertex, +-1e-6 points) gave 0 defects for T1 1/16, T1 1/8, T2 1/64, 1/32, 1/16, 1/8 (3000 random points each; [OBS]).

Scripts created (`/Users/trentpalelei/Desktop/Math Ex/experiments/n8/`): `tightlaw_gen_v1.py` (generator adapted from `ap_law_gen_r4_v1.py`: subject 0, arrangement positions), `tightlaw_build_v1.sh`, `tightlaw_analyse_v1.py`, `tightlaw_walls_v1.py`, `tightlaw_touch_v1.py`, `tightlaw_table_v1.py`. The enumerator `ap_r4_chambers_v1.py` was used unchanged with nominal vectors `1,2,3,4,5,7,12` and `1,4,5,6,7,11,13` (tags T1, T2; T0 = (1..7) as control). Pickles are in the session scratchpad.

## Chamber counts per radius (exact enumerator finished in every row; [OBS])

| rho | T0 (AP) leaves | T1 leaves (chain types, wall forms, landing forms, max moves) | T2 leaves (same) |
|---|---|---|---|
| 1/64 | 3 | 3 (3, 2, 3, 11) | 14 (13, 10, 8, 26) |
| 1/32 | 5 | 5 (5, 4, 5, 11) | 26 (25, 19, 14, 27) |
| 1/16 | 6 | 7 (7, 6, 7, 11) | 46 (44, 31, 18, 27) |
| 1/12 | 10 | 11 (11, 10, 9, 12) | 68 (67, 39, 22, 27) |
| 1/10 | 21 | 15 (15, 12, 9, 12) | 96 (93, 44, 24, 27) |
| 1/8 | 39 | 20 (19, 16, 11, 12) | 142 (131, 53, 24, 27) |
| 1/7 | 126 | 20 (19, 16, 11, 12) | 384 (332, 67, 24, 27) |
| 1/6 | 201 | 24 (21, 20, 12, 12) | 506 (451, 73, 24, 27) |
| 1/5 | 379 | 52 (39, 34, 20, 15) | 638 (574, 86, 26, 27) |
| 1/4 | not run | 222 (156, 69, 23, 16) | not run |
| 1/3 | not run | 1710 (1190, 172, 31, 19) | not run |

T0 rows 1/64 to 1/8 re-run here and equal the earlier counts (3, 5, 6, 10, 21, 39); T0 1/7 to 1/5 are from the Agent E report, not re-run. T2 at 1/4 and below, T1 beyond 1/3: not run. "Landing forms" counts distinct (reading, lap M) pairs `(M + 1/8)/x_i`.

## Walls

Every split of every tree (T1: 2 to 221 splits; T2: 13 to 637) compares two readings against an odd-over-odd ratio `x_i (p/8) vs x_j (q/8)`, p and q odd (checked on every split of every tree in the table, `tightlaw_table_v1.py`, last column True). So the wall family is the same pairwise ratio family `(8a +- 1)/(8b +- 1)` as at the AP. The tight wall `x_k * 1 vs x_1 * 7` (the tight reading k at 7 x_1) is common to all three, with k = 7, 6, 5 for T0, T1, T2. Sharing of (p,q) ratio pairs: at 1/64 T0 and T1 share both of their 2 walls (3x15 vs 5x9, and 1 vs 7); at 1/8, 10 of T0's 25 and 12 of T1's pairs; T0 and T2 9; T1 and T2 5; all three 5.

## The first chamber and the nominal point

For all three, at the nominal point the cascade's type has 0 moves: `T = 1/(8 x_1) = 1/8` (reading 1, lap 0), and the clear set at that instant is the single point `[1/8, 1/8]` (zero width; computed exactly from the seven windows). The tight reading k (nominal 7 = 7 x_1) sits exactly at `distInt = 1/8` on the far side: the chain row `whi_k` (`x_k <= 7 x_1`) is the one chain inequality equal to zero at the nominal point (T0 `whi7`, T1 `whi6`, T2 `whi5`). So, as at the AP, the tight point uses the isolated lonely instant at `1/(8 x_1)`: reading 1 enters its window at `1/8` while reading k leaves its window there, and nothing remains but a point.

The chambers whose closure contains the nominal point (exact, `tightlaw_touch_v1.py`; same list at every radius from 1/64 to 1/8):
- T0 and T1: 3, identical: moves 0, 6, 11, landing at `1/(8 x_1)`, `(1 + 1/8)/x_3` (nominal 3/8), `(3 + 1/8)/x_5` (nominal 5/8). The two cone walls through the nominal point are `7 x_1 vs x_k` and `5 x_3 vs 3 x_5`. T1's reading 12 is at distance 1/2 from an integer at every instant c/8 with c odd (12c/8 = 3c/2), so it is never in the way at these instants.
- T2: 8 chambers touch it, 7 cone walls through it: moves 0, 8, 17, 18, 18, 18, 26, 26, landing forms `1/(8 x_1)`, `(4 + 1/8)/x_6` (nominal 3/8), `(3 + 1/8)/x_3` (5/8), `(8 + 1/8)/x_7` (5/8), `(6 + 1/8)/x_5` (7/8). The unit-of-Z/8 pattern persists (instants 1/8, 3/8, 5/8, 7/8), with more cones at the point and moves up to 26.

## Common and different

Common:
- the wall family: pairwise odd-over-odd ratio walls only; the tight wall (reading of nominal 7 against 7 x_1) present in all three;
- the nominal point uses the zero-width instant `1/(8 x_1)` with 0 moves; the tight reading is the reading equal to 7 times the least;
- first radii: T0 and T1 have the same two-wall, 3-chamber tree at 1/64 and 5 at 1/32; chamber growth is by jumps and plateaus, not a smooth rate (T1: 20, 20, 24, 52, 222, 1710 at 1/8, 1/7, 1/6, 1/5, 1/4, 1/3);
- each wall of a smaller radius that enters keeps appearing (observed on the pickles at the radii in the table; not a theorem).

Different:
- T1 is the AP's twin at small radius (same fan at the nominal point, 7 against 6 leaves at 1/16 and then fewer than T0 at 1/10 to 1/6: 15 against 21, 20 against 39, 24 against 201). The reason T0 grows faster is not identified here; the counts are an observation, not a mechanism.
- T2 is already large at 1/64 (14 leaves, 26 moves) and its fan at the nominal point has 8 chambers against 3; readings (4,5,6,7) near the tight pair make many more nominal coincidences (7 cone walls against 2). T2's landing forms grow to 24 by 1/8 against 11 (T1) and 19 (T0).
- Max moves: T0 11 to 18, T1 11 to 12 (to 1/6), T2 26 to 27 from the smallest radius.

## Not proved / owed

- T1 above 1/5 and T2 above 1/16 have no Lean (T2 1/12 stopped after the generator and the first chain file: compile time; its files were removed). T1 at 1/7, 1/4, 1/3 and T2 at 1/8 to 1/5 are enumerated (and T1 1/8, T2 1/8 audited) only.
- The statements are `FirstIso` with a disjunction of landing forms; the attribution of a form to its chamber is the tree, not a theorem statement. The box is a superset of the reachable deviations; no claim that a leaf is reached or of leaf measures.
- Only the extreme subject 0 (readings T) is treated, as requested; the other seven subjects of the arrangements (0,1,2,3,4,5,7,12) and (0,1,4,5,6,7,11,13) are not covered here, and nothing says g*(arrangement) is 1/8 or how the arrangement's other subjects land.
- Nothing is claimed for the tightness of T1 or T2 beyond the lead's exact search (N = 22); the three-point list is not re-derived here.
- Wall-family and growth statements are observations on the enumerated trees, not theorems for all radii.
