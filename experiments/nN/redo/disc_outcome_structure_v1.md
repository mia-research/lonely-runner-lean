# Outcome structure of the tree members, by result (v1)

Object: 110,081 members (one stored witness arrangement per tree cell, J=2; `cell_members_J2.pkl`), outcome record per member in `disc_records_v1.pkl` (`disc_records_v1.py`, exact Fractions: R*, width, p_y, states, exits). The members are one witness per cell, not a spread over the cell; every "members" statement below is about those 110,081 arrangements only.

Rule applied (coordinator correction): every verdict below is an exact-Fraction computation (`disc_exact_v1.py`, `disc_partition_v1.py`, `disc_gapwitness_v1*.py`, `disc_gapclimb_edge_v1.py`) or an inequality argument. Floats were used only to steer searches; the earlier float scripts (`disc_rstar_v1`, `disc_positions_v1`, `disc_states_v1`, `disc_explore*`, `disc_floats_v1`) are guidance only. Their tolerance-based items (|p-1|<1e-6 "on-face" counts, Spearman matrix, k-means, regression of moves on ln R*, float 0.01-bin empty-interval list of states, float gap searches "not entered") are WITHDRAWN as results. Percentages are not used.

## 1. R* and width

**Verdicts that survive (exact):**
- R* has no member in (7,9) and none equal 7; 8 members have R*=9 exactly, all with opener (rank 1, lap 1). Reason (inequality, not data): reading 1 has the zone (7,9), so an R* there is blocked. Equal statements, exact: the set with a state exactly 9, the set with reading 1 as a setter, the set with R*>=9, the set with R*>7 are the same 4,939 members. Of these, 4,931 continue past 9 (R*>9) and 8 land at 9.
- Smallest member R* is 9570149208162304/8583747560173039 (1.114915...); largest 11.592485...; no member has zero moves.
- Gaps between consecutive member R* values larger than 0.03 (exact sorted list; `disc_rstar_v1.out` lists edges): (1,1.1149), (1.1149,1.2073), (1.4242,1.4678), (5.7946,5.8398), (6.3854,6.4404), (6.6273,6.6642), (6.6642,6.7800), (6.7851,9), (10.8288,10.9059), (11.0872,11.2372), (11.2372,11.2744), (11.3319,11.5251), (11.5251,11.5563), and above 11.5925. **Of these only (7,9) is a property of the cascade (forced by reading 1's zone).** Every other gap has an exact-Fraction arrangement inside a tree cell, path word equal to the cell's (checked with `path()`), whose R* lies strictly between the two bracketing member values (`disc_exact_v1.out` E1, witnesses in `disc_gapwitness_v1.out`, `disc_gapwitness_v1b.out`):
  gap (6.7851,9): R* = 55169095435288576/7881299347899751, which is below 7 by about 1.2e-12 (cell 62250; readings in `disc_gapclimb_edge_v1.out`). Also 27584547717644288/4011964952796309 = 6.8756 (cell 62251).
  Witnesses exist for gaps 0-12 listed above (1.1060, 1.2071, 1.4678, 5.7947, 6.3885, 6.6273, 6.6647, 10.8290, 11.0874, 11.2744, 11.3319, 11.5253). Earlier statements "R* just below 7 does not occur" and "(1,1.11) empty" hold for the 110,081 members only.
- Atoms: 66,440 distinct R* values; 7,913 values occur at least twice; 612 occur at least 10 times. The largest are exits of readings pinned at integers: 49/17 (3,056 members, opener rank 7 lap 6, reading 17), 49/15 (2,082), 41/15 (1,841), 11/5 (1,388), 41/17 (1,357), 25/7 (1,260), 33/7 (729), 65/17 (603), 19/5 (595). 15,969 members open at an exactly-integer reading; 21,346 have rho_7 = 17. 35,586 of the members sitting in repeated values open at a non-integer reading (repeated non-integer witnesses, e.g. 11540474045136896/4520156978941711, 192 members). Whether the cells contain arrangements off these values at the same (rank,lap) is true by the witnesses above for the gap cases; for the atoms it is not tested, so the atoms are recorded as properties of the member list.
- Tenth-of-unit counts of R* (exact floor): `disc_exact_v1.out` E6; counts are zero in [6.8,9.0) and from 11.6 up, nonzero elsewhere in [1.1, 11.6) except the gaps above.
- Width: exact zero in 11 members, all with p_7 = 7 exactly (the landing is both the exit of the opener and the entry of reading 7's zone): 10 with opener (rank 5, lap 4), 1 with opener (rank 6, lap 4). Largest width 0.559336 (exact fraction in `disc_exact_v1.out`). Smallest positive widths are 1.8e-16, 1.6e-13, 2.3e-13 (exact values in the file); 16 members have width below 1/10^6, 157 below 1/10^3. Closer rank counts (exact argmin of (7-p_y)/rho_y), ranks 1..7: 4, 5882, 11645, 12916, 19270, 25289, 35075 (two members tie for closer exactly).

## 2. Positions p_y at R*

- The opener has p = 1 exactly in every member (R* = (8j+1)/rho by construction). Removing it removes exactly the p=1 atom: the count of opener rank k is 8, 2347, 8827, 16992, 22701, 25708, 33498 for k = 1..7.
- Exact ties at p = 1: 118 members have two readings at p = 1, 13 have three (tied non-opener ranks 2..6, always lower rank than the opener, offsets -1..-5). p = 7 exactly: 11 members (the 11 zero-width members).
- Every exact 0.02-bin of [1,7) is occupied by non-opener readings of each of ranks 2..7 (members tested: 107,734; 101,254; 93,089; 87,380; 84,373; 76,583). So no per-rank forbidden band was found for ranks 2..7 over the members. Rank 1: p_1 = R* mod 8; 19 of 300 bins are empty and they are the R* gaps above (so p_1 in (6.7851,7] is a member-list fact, not a cascade fact, by the witnesses above).
- Pairs: over the 15 pairs among ranks 2..7, exactly one empty 0.5 x 0.5 cell out of 144 in all pairs: (p_2,p_3) in [6.5,7)x[6.5,7). Members only; not searched at cell level, so undecided.
- The Spearman matrix and k-means are withdrawn (float, not a verdict). Exact descriptive facts only: 930 distinct lap vectors, 2,957 distinct p-orderings of the 5,040 (floats-free counts in `disc_positions_v1.out` 2g, recomputed from exact floor of R*rho/8 is not repeated here; treat as guidance).

## 3. State sequences

- Ratio R_{k+1}/R_k (exact): in all 1,320,740 moves ratio <= 1 + 2/(8j-1) for the exit lap j, hence < 9/7; 0 violations. Argument: the blocker at lap j >= 1 sits at R*rho > 8j-1 and its exit is less than 2/rho away. Largest ratio per lap sits within 5e-6 of the bound for j=1..5. R_1 < 9/7 in every member (R_0 = 1, first exits come from readings in (7,9) or (15,17)).
- Exit lap equals round(R_k rho/8) of the setter (exact, 1,320,740 moves; 0 mismatches). Occurring (rank,lap) exits: 52 pairs; largest lap per rank 1..7: 1, 5, 6, 7, 8, 10, 18. Reading 1 sets only at lap 1 (state 9), in 4,939 members. Exits by rank 1..7: 4,939; 149,321; 202,661; 225,436; 238,917; 248,215; 251,251.
- States in (7,9): 4,939 members have one (all go to 9 next via reading 1); the largest such state is 9570149208162304/1245144706329595 = 7.685973 (member list only).
- The setter is the lowest-rank blocker in 1,264,639 of 1,320,740 moves. The 56,101 exceptions all have at least two blockers (2: 47,016; 3: 8,409; 4: 675; 5: 1). In every exception d_low > d_setter (forced: exit_low < exit_setter with rho_low < rho_setter); d_low ranges over [-0.7708, 1.0000] and exceeds 0 in 39,732. Largest exception pairs (lowest blocker rank -> setter rank): (5,7) 10,403; (6,7) 7,997; (4,6) 7,573; (4,7) 7,548; (5,6) 5,584. The exceptions share: the setter is of higher rank than the lowest blocker and the lowest blocker is at an offset that gives an earlier exit.
- Zones passed (reading y, lap j, with b = (8j+1)/rho_y in (1, R*]): 231,013 zones are jumped over rather than visited; in all of them the jump was set by a strictly lower rank than y (0 exceptions). Argument: jump < 2/rho_setter and zone width 2/rho_y. Rank 1: 4,939 visited, 0 skipped. Skipped by rank 2..7: 835; 1,866; 12,432; 29,893; 63,285; 122,702.
- Number of moves: members with R*>=9 have 17..29 moves; members with R*<7 have 1..27 (2 with 1 move). The relation of move count to R* beyond these ranges is not stated (the regression was float and is withdrawn).

## 4. Groups by outcome (`disc_partition_v1.out`; features found above: reading 1 as setter; closer vs opener rank)

closer = reading minimising (7-p_y)/rho_y; opener = last setter at p = 1.

| group | definition | members | R* range | moves |
|---|---|---|---|---|
| G1 | some state = 9 (reading 1 sets a move) | 4,939 | [9, 11.5925] | 17..29 |
| G2 | not G1, closer rank < opener rank | 57,861 | [1.4071, 6.7851] | 3..25 |
| G3 | not G1, closer rank > opener rank | 47,083 | [1.1149, 6.5282] | 1..27 |
| G4 | not G1, closer = opener | 198 | [1.3923, 5.9333] | 2..16 |

- G4 has opener rank 7 only. Proved: if opener rank k < 7, reading 7 has (7-p_7)/rho_7 <= 6/rho_7 < 6/rho_k (p_7 >= 1, rho_7 > rho_k), so the opener is never the closer; 0 contradictions among members. For rank 7 it is 198 members (opener 7 x closer 7).
- Opener x closer table (counts, rows opener 1..7, cols closer 1..7): opener 1: closers only 4 (5), 5 (3); opener 2: 0,0,343,191,668,358,787; opener 3: 0,21,0,844,1230,1947,4785; opener 4: 0,1017,1757,0,1495,3858,8865; opener 5: 0,1769,2974,3469,0,3084,11405; opener 6: 4,1190,3043,4296,8140,0,9035; opener 7: 0,1885,3528,4111,7734,16042,198. Closer rank 1 occurs in 4 members (opener 6). Zero cells off the diagonal are member-only (not searched at cell level: undecided).
- G1 composition: opener ranks 1..7: 8, 295, 253, 500, 751, 1,073, 2,059; closer ranks 2..7: 61, 82, 1,094, 2,846, 649, 207.
- Cases that do not fit a single rule: 2 members with two readings tied for closer (in G2); 131 members with a tie at p=1 (26 in G1, 56 in G2, 49 in G3); 11 zero-width members (all G3, closer rank 7, p_7=7); the 8 members with R*=9 (G1, opener rank 1); the 56,101 setter-not-lowest-rank moves (section 3).

## What did not survive from the first pass
Float "gap not entered" for (6.664,6.780) and (6.785,7) (the climb of cell 62250 enters (6.785,7) exactly); the "on-face" 1e-6 witness counts; the correlation/cluster findings; any statement that the atoms or the (1,1.11) region are properties of the cascade. Open at cell level (undecided, no exact search done): the empty (2,3) pair cell, opener x closer zero cells off the diagonal and above, the atoms' status.

Files (all in `experiments/nN/redo/`): `disc_records_v1.py/.pkl`, `disc_exact_v1.py/.out`, `disc_partition_v1.py/.out`, `disc_gapwitness_v1.py/.out`, `disc_gapwitness_v1b.py/.out`, `disc_gapclimb_edge_v1.py/.out`, `disc_gapsearch_v1.py` and `disc_gapclimb_v1.py` (float guidance, outputs `.out.a/.b/.c`), `disc_rstar_v1`, `disc_positions_v1`, `disc_states_v1` (`.py/.out`, guidance).
