# envl_bounds_v1 -- per-rank reading envelopes of multi-move cascades

Objects: readings rho_1 = 1 < rho_2 < ... < rho_7 (ranks), zones Z(y,j) = ((8j-1)/rho_y, (8j+1)/rho_y), cascade states R_0 = 1 < R_1 < ..., a move from R_k goes to the largest exit (8 l + 1)/rho_s among the blockers at R_k (setter s, lap l). Exact code: `path`, `outcome` exec'd from `cascade_path_map_v1.py`, `outcome_classes_v2.py`.
Windows: J1 = rho_7 <= 9 (tree `terminals5_J1`, 9197 members), J2 = rho_7 <= 17 (`terminals5_J2`, 110081 members).
Grades: [EXACT] = exact rational vertex, exact feasibility, nudge certificate; [PROVED] = derived below, no data used; [COUNT] = count over the stated set; [OPEN] = not derived.

## 0. What the data set is (a scope finding that changes the question)

0.1 [COUNT] The members are not all arrangements. In J1, 9197 members: 9187 have every reading of rank 2..7 as a blocker at some visited state; 5 have rank 7 never a blocker (members sitting at rho_7 = 9 + eps). In J2: 95 of 110081 have some reading of rank 2..7 never a blocker (45 + 50 from the two halves; the missing ranks are 4, 5, 6, 7 only). So the tree class is "every reading is involved in the cascade" (`envl_check_J*_v1.out`, lines `C8`).
0.2 [EXACT, counter-case] The bounds for ranks 2..5 on multi-move cascades are statements about that class, not about all arrangements. Exact arrangement `[1, 11/10, 6/5, 13/10, 7/5, 31/5, 15/2]`: `path` gives 2 moves (setters ranks 7 then 6), landing R = 45/31, with rho_5 = 7/5 < 343/81. (Run in the session with `path` of `cascade_path_map_v1.py`; with rho_6 = 28/5 the same readings give 1 move.) The explanation: a reading y with R_k rho_y <= 7 at every visited state never blocks, so nothing forces it up.
0.3 The task's tree ranges are sub-boxes of the cascade-type regions: 591 of 8839 J1 signature regions have an LP range wider than their (first) tree box (`envl_an_J1_v1.out`). All minima below are over the full signature region (the polytope in rho of one exact combinatorial type: per state, per reading, blocked-with-lap or clear-in-gap, plus the max-exit comparisons, plus ordering and rho_7 <= W). The region minima coincide with the tree-box minima in every rank (compare `envl_an_J1_v1.out` with the tree-box lines in section 1).

## 1. Per-rank bounds (infimum over cascades with >= 2 moves and with >= 10 moves)

Method: for each signature (8839 in J1, 105286 in J2; one per distinct exact path type among members), a linear program in (rho_1..rho_7) with rho_1 = 1 (HiGHS), then for each extremal signature the active set at the float optimum is solved exactly (sympy rationals), the exact vertex is checked feasible against every exact constraint, and the vertex is moved by 1e-6 toward an interior point; the exact `path` signature at the moved point equals the signature [EXACT; `envl_extreme_J1_v1.out`, `envl_extreme_J2_v1.out`]. Optimality is the float LP optimum equal to the exact vertex value to 1e-9; no dual certificate was produced. Infima: the closure value; the nudge shows that values within 1e-6 of it are realised by arrangements of that exact type.

| rank | >= 2 moves, J1 | >= 2 moves, J2 | >= 10 moves, J1 | >= 10 moves, J2 |
|---|---|---|---|---|
| 7 | 7 | 7 | 7 | 7 |
| 6 | 49/9 = 5.4444 | 49/9 | 49/9 | 49/9 |
| 5 | 343/81 = 4.2346 | 343/81 | 343/81 | 343/81 |
| 4 | 2401/729 = 3.2936 | 2401/729 | 1715/459 = 3.7364 | 1715/459 |
| 3 | 735/289 = 2.5433 | 735/289 | 735/289 | 735/289 |
| 2 | 3381/2125 = 1.5911 | 3381/2125 | 3381/2125 | 3381/2125 |

The J1 and J2 columns are identical in every entry. The task's "rank 3 about 2.2-2.5" is 735/289 = 2.54325 here; the tree-box minimum is also 2.5433 (`envl_an` and the tree-box scan: J1 and J2, >= 2 moves: 1.5911, 2.5433, 3.2936, 4.2346, 5.4444, 7.0; >= 10 moves: 1.5911, 2.5433, 3.7364, 4.2346, 5.4444, 7.0).
Attaining vertices (readings of ranks 2..7, then path as (setter rank, lap)):
- rank 7 (7): any cell with first move (7,1); the J1 >= 2 vertex is `[49/9, 7, 7, 7, 7, 7]`, path (7,1),(2,1) (`envl_extreme_J1_v1.out`).
- rank 6 (49/9): `[49/9]*5, 7`, path (7,1),(2,1). 2 moves.
- rank 5 (343/81): `[343/81]*4, 49/9, 7`, path (7,1),(6,1),(2,1). 3 moves.
- rank 4 (2401/729), >= 2 moves: `[16807/6561, 16807/6561, 2401/729, 343/81, 49/9, 7]`, 7 moves.
- rank 4 (1715/459), >= 10 moves: `[16807/6561, 2401/729, 1715/459, 343/81, 49/9, 7]`, 10 moves, path (7,1),(6,1),(5,1),(3,1),(2,1),(7,3),(5,2),(4,2),(7,4),(3,2).
- rank 3 (735/289): `[1715/867, 735/289, 276115/70227, 39445/7803, 105/17, 7]` (J1, 9 moves) path (7,1),(6,1),(5,1),(4,1),(7,2),(6,2),(3,1),(2,1),(5,3).
- rank 2 (3381/2125): `[3381/2125, 161/39, 4991/975, 483/85, 161/25, 7]` (J1, 15 moves).

## 2. Derivations (framework objects only)

Facts used. (a) y blocks at R iff R rho_y in (8l-1, 8l+1) for some lap l >= 1 (lap 0 never: R rho_y >= 1). (b) A move from R_k with setter s at lap l goes to R_{k+1} = (8l+1)/rho_s; the setter sits at position 8l+1, an open-zone edge, so it does not block R_{k+1}. (c) R_k rho_s < 8l+1 and R_k rho_s > 8l-1, hence R_{k+1}/R_k < (8l+1)/(8l-1) <= 9/7. (d) states strictly increase; a reading whose zone at lap l was left (exit <= R) re-blocks only at lap >= l+1.

D1 [PROVED]. R_k < (9/7)^k R_0 = (9/7)^k. From (c) and induction.
D2 [PROVED]. The setter y_k of move k+1 blocks at R_k at some lap l >= 1, so rho_{y_k} > (8l-1)/R_k >= 7/R_k > 7 (7/9)^k.
D3 [PROVED]. y_{k+1} != y_k (fact b). So rho_7 > 7 for >= 1 move and rho_6 > 49/9 for >= 2 moves (two distinct readings y_0 != y_1, with rho_{y_0} > 7 and rho_{y_1} > 49/9; both exceed 49/9, so the second largest reading does). These two bounds use no window and no involvement; they are the only parts of the table that are universal by proof.
D4 [PROVED, conditional] Chain: if the cascade has >= k+1 moves and y_0..y_k are k+1 distinct readings, each exceeds 7(7/9)^i for its own index i <= k, so each exceeds 7(7/9)^k, and the (k+1)-th largest reading exceeds it: rho_{7-k} > 7 (7/9)^k. Values k = 0..5: 7, 49/9, 343/81, 2401/729, 16807/6561 = 2.5617, 117649/59049 = 1.9924. The table entries for ranks 5 and 4 (>= 2 moves) are exactly k = 2, 3; the vertices above are chain-tight (every R_k rho_{y_k} = 7, every step ratio 9/7).
D5 [ARITHMETIC, attaining paths]. When y_0 recurs among the first setters, D4 does not bind and the lower rank drops: rank 3 = 735/289 = 7 * (15 * 7/17) / 17: rho_7 = 7, the second block of rank 6 is at lap 2 (rho_6 R_4 > 15 with R_4 = 17/rho_7, so rho_6 > 105/17), then rank 3 blocks at R_5 = 17/rho_6 (rho_3 > 7 rho_6 / 17). Rank 4 (>= 10 moves) = 1715/459 = 15 (343/81)/17: rank 4 first blocks at lap 2 at R = 17/rho_5. Rank 2 = 3381/2125 = 7 (483/85)/25: rank 2 blocks at R = 25/rho_5 (a lap-3 exit). These identities are checked by exact arithmetic on the vertices; they identify the tight chain of the attaining paths. That no other path type goes lower is the LP statement of section 1 (every signature of the tree), not a derivation. [OPEN as a closed-form theorem.]
D6 [PROVED]. First-block time: if y first blocks at state t_y then rho_y > 7 (7/9)^{t_y}. A reading of rank r that is involved but small must first block late, which needs many moves. This is the object-level reason the ranks 5..2 bounds are tied to the number of moves in the involved class.

### Violation counts for the derived inequalities (members)

All counts: members of the J1 tree (9197) and the J2 tree (110081). The script prints only counters that were incremented, so an absent line is a count of 0 (`envl_check_J1_v1.out`, `envl_check_J2a_v1.out`, `envl_check_J2b_v1.out`).
- R strictly increasing (D-states): 0 violations. Step ratio R_{k+1} < R_k (8l+1)/(8l-1): 0. D1 R_k < (9/7)^k: 0. D2: 0. D3 consecutive setters differ: 0. Each (reading, lap) used as setter at most once: 0. D6 first-block time inequality: 0. Pair-count m <= #{(y,l): 8l-1 < R_{m-1} rho_y}: 0. Smallest involved reading > 7/R_last: 0.
- D4 chain, members with >= k+1 moves, rho_{7-k} > 7(7/9)^k: k = 0..4 (ranks 7..3): 0 violations in J1 and in J2. k = 5 (rank 2): 42 violations (J1), 45 (J2), all with a repeated setter among the first 6 (42 of 42, 23 + 22 of 45).
- First k+1 setters distinct, members: J1 all for k <= 3 (9187 of 9187 at k=3), 6007 of 9187 at k=4, 1496 of 9173 at k=5. J2 all for k <= 2 (110067 of 110067 at k=2), 98591 of 109960 at k=3, 64994 (32470 + 32524) of 109380 at k=4, 20970 of 107603 at k=5.
- Region level (whole signatures, not members; `envl_chain_lp_v1.out`): J1 k=4 (rank 3): 5 signatures below 2.5617, all with repeated setters (minimum 2.5433); k=5: 141 below 1.9924 (min 1.5911). J2 k=4: 5 below; k=5: 190 below. With distinct first k+1 setters the minima equal the chain value exactly and there are 0 violations at k = 0..5 in both windows. The members at k=4 show 0 violations while the regions show 5: absence in members is a sampling absence, and the counter-arrangements are the nudged vertices of section 1 (exact signature check).
- Repeated setters among the first k+1: J1 none for k <= 3; J2 repeats appear at k = 3 (10865 signatures) and none of them is below 2401/729 (their minimum is 3.864).

### Universe check outside the tree (random arrangements, float path, tolerance 1e-9; `envl_universe_*_v1.out`)
400000 samples per window. D4 with distinct setters: 0 violations for k = 0..5 at W = 9, 17, 40, 100. Repeated setters among the first k+1 first occur: W = 9: k = 4; W = 17: k = 3; W = 40 and 100: k = 2. So the rank-5 chain bound (343/81, >= 3 moves) fails for W = 40: exact arrangement `[1, 310049/286490, 1294334/972837, 1556213/808651, 2185118/595217, 6450130/933033, 1842676/59293]` (rho_7 = 31.08): setters (7,6,7), laps (4,1,5), 3 moves, rho_5 = 3.671 < 4.2346 (`envl_w40_example_v1.out`, exact `path`). Thresholds between W = 17 and 40 for the first repeat at k = 2 are not located.

## 3. Upper side

Sup of each rank over cascades with >= 10 moves (LP over signatures; closure value / value over signatures with non-empty interior within the window, nudge-certified):

| rank | J1 closure | J1 interior | J2 closure | J2 interior |
|---|---|---|---|---|
| 2 | 27/5 = 5.4 | 27/5 | 289/23 = 12.5652 | 289/23 |
| 3 | 153/23 = 6.6522 | 153/23 | 425/31 = 13.7097 | 425/31 |
| 4 | 867/115 = 7.5391 | 225/31 = 7.2581 | 1445/93 = 15.5376 | 296769/19375 = 15.3171 |
| 5 | 1377/161 = 8.5528 | 255/31 = 8.2258 | 3179/195 = 16.3026 | 3179/195 |
| 6 | 9 | 9 | 17 | 17 |
| 7 | 9 | 9 | 17 | 17 |

"Closure" is the maximum over every signature region including those whose region has empty interior inside rho_7 <= W (zero thickness; 6, 6, 6, 12 candidates above the J1 interior values for ranks 2, 3, 4, 5, and 2, 2, 3, 0 in J2). Those values are tree-box values (they equal the tree box maxima 5.4, 6.6522, 7.5391, 8.5528 and 12.5652, 13.7097, 15.5376, 16.3026) but the nudge certificate fails for them; the interior column is the nudge-certified one (`envl_nudge_J1_v1.out`, `envl_nudge_J2_v1.out`). Ranks 6 and 7 reach the window edge W (sup, not attained, ties rho_6 <= rho_7 <= W).
Window dependence [COUNT]: the envelope is not window independent. J2 / J1 for ranks 2..5: 2.33, 2.06, 2.10 (interior), 1.98. Restricting J2 to cascades whose first setter is at lap 1 still gives rank 2 up to 9.0 (vs 5.4 in J1) and rank 3 up to 12.57 (`envl_firstlap_v1.out`): the extra room comes from readings above 9 (laps >= 2 at R = 1), not only from a shifted first zone. The window dependence is for two windows; no formula in W is identified. [OPEN]
Derived upper statement [PROVED, J-specific]: with rho_7 <= W and W in (7, 9], a cascade with >= 2 moves has rho_2 <= 7. If rho_2 > 7 every reading of rank 2..7 lies in (7, 9]; the blockers at R = 1 are exactly those in (7, 9), the largest exit is 9/rho_2 (setter rank 2), R_1 = 9/rho_2 < 9/7; each other reading has R_1 rho_y in [9, 81/7] which lies in the clear gap (9, 15) up to the closed end, and rank 1 has R_1 < 7; no blocker, 1 move. Same argument for rho_7 <= 17: rho_2 > 15 gives 1 move. Matching data: tree boxes, >= 2 moves, max rank 2 = 7.0 (J1), 15.0 (J2); members with m >= 2 and rho_2 > 7 (J1) or > 15 (J2): 0.
The ">= 10 moves" upper sups are not derived. [OPEN] What is derived and checked (0 violations in all members): the number of moves is at most the number of distinct (reading, lap) pairs with 8l-1 < R_{m-1} rho_y, which is the quantity that grows with the window.

## 4. Universal vs window-dependent

| item | status | evidence |
|---|---|---|
| rho_7 > 7 for >= 1 move; rho_6 > 49/9 for >= 2 moves | universal, over all arrangements (D3) | proof; 0 violations in 1.6M random arrangements, W up to 100 |
| rho_{7-k} > 7(7/9)^k with first k+1 setters distinct | universal (D4) | proof; 0 violations tree (both windows) and random (4 windows) |
| rho_5 >= 343/81 for >= 3 moves | holds for W <= 17 (tree, 800000 random); FAILS at W = 40 | exact counter-arrangement, section 2 |
| rho_4 >= 2401/729 for >= 4 moves | holds in J1; J2 tree-class holds; random arrangements at W = 17 have 78 samples below | section 2 universe |
| ranks 5, 4 on >= 2 moves in the tree | class-dependent (all readings involved) | counter-case rho_5 = 1.4, section 0 |
| ranks 3, 2 (735/289, 3381/2125) | window-independent between J1 and J2 in the tree class, not derived as theorems | LP over all signatures, exact vertices |
| rank 4 on >= 10 moves: 1715/459 | same in J1, J2 (tree class), not derived | LP |
| upper envelope on >= 10 moves | window dependent | section 3 table |
| rank 2 <= 7 (W <= 9), <= 15 (W <= 17) on >= 2 moves | derived for these windows | section 3 |

## 5. Failures and what the failing cases share
1. The first reading of the task, "bounds over all arrangements with >= 2 moves", is false for ranks 2..5 (section 0.2); the tree class forces every reading to block somewhere.
2. The first nudge certificate failed for 10 of 12 upper-side extremes (`envl_extreme_J*_v1.out`, `same_sig_after_nudge=False`: ranks 2..7 in J1, ranks 2, 3, 4, 7 in J2). Shared feature: the signature region has zero thickness inside rho_7 <= W (Chebyshev slack 0), i.e. the member sat at rho_7 = W + eps. The interior column of section 3 replaces them.
3. D4 at k = 4, 5 is violated at region level (5 / 141 and 5 / 190 signatures) while 0 members violate at k = 4. Shared feature: a repeated setter (reading 7 or 6 re-blocking at lap >= 2).
4. The float random sampler first reported repeated consecutive setters; these were rounding (setter at position exactly 1); fixed with a 1e-9 tolerance and rerun. Reported numbers are from the fixed run.
5. J2 signature extraction ran 11 minutes (limit 10); the LP and checks were chunked under 10 minutes each.
6. 7003 of 117084 J2 tree cells have no member in `cell_members_J2.pkl`; signatures are built from members, so those cells are not in the LP sets. The tree-box minima and maxima (which include them) equal the LP minima and closure maxima for every rank listed.
7. Not derived: closed forms for the global minima of ranks 3, 2, and rank 4 at >= 10 moves, the >= 10 upper sups, the dependence on W beyond two windows, and the threshold W in (17, 40] at which the rank-5 chain fails.

## Files
`envl_common_v1.py` (signature and constraint rows), `envl_lp_v1.py`, `envl_sigs_v1.py`, `envl_run_v1.py`, `envl_chunk_v1.py`, `envl_extreme_v1.py`, `envl_nudge_v1.py`, `envl_chain_lp_v1.py`, `envl_check_v1.py`, `envl_universe_v1.py`, `envl_w40_example_v1.py`, `envl_firstlap_v1.py`, `envl_an1_v1.py`; outputs `envl_*_v1.out`, `envl_chunk_J2_v1.log`. Pickles are in the session scratchpad.
