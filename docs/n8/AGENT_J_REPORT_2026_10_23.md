# Agent J report, 2026-10-23: band cover walls against the AP deformation walls; band landing path types

Rules: 5 (no runner stationary; s0 = 1 is a positive reading), 7 (no caps/move budgets as lemmas; counts are observations), 8 (paths computed by the cascade itself), 15 (exact Fractions only), 16 (new files only, no Lean written), 18 (grades: all results below are [OBS]; no [L] claims).

No Lean was created. Task 4's Lean branch was not taken (chamber count is far above a few hundred). All scripts are exact Fractions; no edits to existing files, nothing committed.

## 1. Walls of the band cover [OBS]
Source: the `by_cases` conditions of BandCoverN.lean and BandCoverTree{2,3,4,17,18,19}N.lean (`band_walls_extract_v1.py`, `.out`).
- 7,018 split nodes, all parsed (0 unparsed), 445 distinct oriented forms `c1*s_a <= c2*s_b` (s_0 = 1, s_i = 1 + x_{i-1}), 419 distinct walls `s_b/s_a = q` (pair, reduced ratio), covering all 21 reading pairs.
- Every one of the 7,018 splits has `c1 = 1 mod 8` and `c2 = 7 mod 8` (`band_walls_stats_v1.py`): the form `(8k+1) s_a <= (8k'+7) s_b`, the clear-interval overlap of lap k of reading a with lap k' of reading b. So all 419 are walls `x_j/x_i = (8a+-1)/(8b+-1)` as stated (the constants 7 and 9 enter as 7 = 8-1, 9 = 8+1). 0 exceptions. 22 coefficient pairs have a common factor, so 50 of the 419 walls have a reduced fraction not of the form (e.g. 15/9 = 5/3); the form holds for the stated, unreduced coefficients.
- Leaf rule `cone_band`: 5,887 leaves, 105 distinct lap assignments (max lap 14); its pair conditions `(8k_i+1) s_j <= (8k_j+7) s_i` give 959 distinct pair-ratio walls, which contain all 419 split walls. Root walls: s6 = 7, 9 (also of the form). `band_walls_leaves_v1.py`.

## 2. Comparison with the AP deformation complex (end subject, nominal 1..7; readings x_1..x_7 = s_0..s_6) [OBS]
Exact trees from `ap_r4_chambers_v1.py` (39, 201, 379 leaves at 1/8, 1/6, 1/5). Every AP row is homogeneous in x, so every AP wall is also a pairwise ratio wall (`band_walls_compare_v1.py`).
- Signature of the stated coefficient pairs (`band_walls_sig_v1.py`): AP overlap rows (`ov`) and upper-window rows (`whi`) are (1,7) mod 8 (the band family); lower-window rows (`wlo`, `(8W+1) x_iL <= (8M+1) x_j`) are (1,1) mod 8, a family the band cover never uses. Split nodes: 1/8: 27 of type (1,7), 11 of type (1,1); 1/6: 166/34; 1/5: 328/50.
- AP split walls (distinct, reduced) against the band cover (`band_walls_overlap_v1.py`):

| radius | AP split walls | (1,7) walls in band split set | (1,1) walls (not band walls) | (1,7) walls not in band cone family |
|---|---|---|---|---|
| 1/8 | 25 | 19 | 6 | 0 |
| 1/6 | 30 | 24 | 6 | 0 |
| 1/5 | 62 | 45 (+2 in cone family only) | 13 | 2: (2,6,57/23), (3,6,57/31) |

 (pair indices are reading indices 0..6.) The 6 (1,1) walls at 1/8 and 1/6: (1,3,17/9), (1,5,25/9), (2,5,17/9), (2,6,41/17), (3,5,25/17), (4,5,41/33).
- Restricted to the band side x7 > 7 x1 of the box (`band_walls_apband_v1.py`, `band_walls_overlap2_v1.py`), the AP tree has 2, 4, 5, 8, 19, 37, 88, 141, 330 leaves at relative radius 1/64, 1/32, 1/16, 1/12, 1/10, 1/8, 1/7, 1/6, 1/5 (31, 73, 122, 289 distinct chain types at 1/8, 1/7, 1/6, 1/5); split walls 1, 3, 4, 7, 16, 24, 27, 28, 61, of which all are band split walls except the (1,1) walls (1, 3, 6, 6, 6, 13 from 1/12) and, at 1/5, 2 large-lap walls.
- Walls meeting the open box on the band side (exact LP): band split walls 86 of 419 (1/8), 127 (1/6), 144 (1/5); band cone walls 120, 181, 211 of 959. Against AP split walls on the band side: overlap 17/23/44, AP-only 6/6/17, band-only 69/104/100 (1/8, 1/6, 1/5; full table in `band_walls_compare_v1.out`). Band-only walls are the cover's lap walls that the first-lonely-instant cascade does not need at that radius.
- Reading: within radius 1/6 the AP complex's (1,7) walls are all walls of the band cover. The AP complex adds only the (1,1) window walls. The band cover is not the AP chamber complex: it carries many walls the AP chambers do not, and lacks the (1,1) family, so it gives no landing statement by itself.

## 3. Band landing: path types [OBS]
`band_walls_paths_v1.py`, `band_walls_paths_report_v1.py(.out)`. Cascade of ap_r2 (start 1/(8 s_0), jump to the latest end among blocked readings). Exact rational shapes 1 = s0 < ... < s6, 7 < s6 <= 9: uniform 2.5 million (400k + 3 x 700k), AP-perturbed 6 x 100,000 (radius 1/64 .. 1/3), systematic grids g = 2 (7,084 shapes) and g = 3 (116,032), 3.2 million shapes in all.
- Distinct path types: 1,683 (union); distinct chain types (path + window integers): 1,890. Pooled uniform alone: 1,552 path types (452 singletons, 174 doubletons; Chao1 estimate about 2,140), 1,757 chain types (Chao1 about 2,380). The discovery curve is not saturated (grid g = 3 alone: 532). Against 105 cover cells: more than 16 times as many.
- Max moves 23. Path types by moves: 1 at 0, 6 at 1, 15 at 2, 20 at 3, 30 at 4, 66 at 5, 107 at 6, 149 at 7, 183 at 8, 212 at 9, 229 at 10, 177 at 11, 147 at 12, 105 at 13, 80 at 14, 60 at 15, 45 at 16, 32 at 17, 11 at 18, then 3, 2, 2, 1.
- Landing `(M + 1/8)/s_i`: 28 distinct (i, M) forms, M distribution over all 3.2M shapes: M=0: 9,360; 1: 2,832,028; 2: 237,439; 3: 142,320; 4: 1,889; 5: 58; 6: 18; 8: 2; 9: 2. Index i by M tabulated in the .out. Landing index i is 2..6 for nearly all shapes; M <= 4 in all but 80 shapes.
- Linear walls: every chain inequality is linear in s with coefficients (8k+1), (8k+7) or (8k+1) (section 2). Finiteness of the path types is not established: the counts are lower bounds and growing slowly.

## 4. Exact band enumerator [OBS, incomplete]
`band_walls_chambers_v1.py` (coordinates s1..s6, s0 = 1; exact simplex of ap_r3; same split construction as ap_r4). Run as 8 slices s6 in (7 + k/4, 7 + (k+1)/4]. After about 8,000 seconds each slice had visited 1,400 to 2,200 nodes without finishing (depth up to 35); stopped. No complete tree, no exact total. The sampled lower bound is 1,890 chambers, exact (each distinct chain type is a distinct cascade region), so the count is not a few hundred; the Lean generation was not attempted.

## Not proved / not done
- No Lean theorem; band landing theorem not stated or proved.
- Exact chamber total of the band: not obtained (lower bound 1,890; Chao1 estimates about 2,400 are estimates, not counts).
- Finiteness of band path types: not shown.
- Wall comparison is for the 105-cell cone family and the full-box AP trees; the band cover's 419 split walls are those of this particular certified tree, not an invariant of the band.

## Files created
Scripts and outputs in `/Users/trentpalelei/Desktop/Math Ex/experiments/n8/`: band_walls_extract_v1.py/.out, band_walls_leaves_v1.py/.out, band_walls_stats_v1.py/.out, band_walls_compare_v1.py/.out, band_walls_sig_v1.py/.out, band_walls_overlap_v1.py/.out, band_walls_overlap2_v1.py/.out, band_walls_apband_v1.py, band_walls_paths_v1.py, band_walls_paths_report_v1.py/.out, band_walls_chambers_v1.py. Pickles are in the session scratchpad (bw/). No Lean files.
