# b12 -- landing bound for gate-crossing arrangements (v1)

Scripts: `b12_cell_lib_v1.py` (exact cell rows, exact vertex and dual certificate), `b12_A_vertex_v1.py`, `b12_A_face_v1.py`, `b12_B_identities_v1.py`,
`b12_C_lines_v1.py`, `b12_C_pivot_v1.py`, `b12_C_facevert_v1.py`, `b12_DE_v1.py`; outputs `*.out`. Floats only chose an LP basis; every stated value is a Fraction
solve, an exact feasibility check of all rows, and an exact dual certificate (multipliers solved in Fractions and checked >= 0).

Cell used: the "fine cell" = path (setter, lap per move) plus the status (blocked lap j / clear) of every reading at every state plus the setter comparisons plus rank order.
Every row is homogeneous linear in the readings (R_k = (8 j+1)/rho_s, so R_k rho_y in an interval is a linear inequality). The fine cell lies inside the tree's path cell; its exact
supremum of R* = (8 j+1)/rho_s (last setter s, lap j) is the exact LP minimum of rho_s over its closure. 375 rows for the extremal cell. The extremal cell has 27 moves (the path listed has 27 pairs).

## A. Tight constraints of the extremal vertex (exact)

Vertex readings (1, 16715503/7123545, 47/15, 726761/173745, 47/9, 15463/2673, 2209/297) is feasible for all 375 closure rows and is the exact LP optimum
(`b12_A_vertex_v1.out`). Exactly 6 distinct rows are tight (7 rows before removing a duplicate). Framework reading (zone of (y,j) = (8j-1, 8j+1)/rho_y):

| # | equality | statement |
|---|---|---|
| 1 | 9 rho_6 = 7 rho_7 | entry of (6,1) = exit of (7,1): reading 6 enters its zone exactly where reading 7's first-lap zone ends (move 1, R = 9/rho_7) |
| 2 | 5 rho_3 = 3 rho_5 | exit of (3,1) (= 9/rho_3, state 6) = entry of (5,2) (= 15/rho_5) |
| 3 | 33 rho_7 = 47 rho_5 | exit of (5,4) (= 33/rho_5, state 17) = entry of (7,6) (= 47/rho_7) |
| 4 | 9 rho_5 = 47 | R = 9 (the gate state, exit of (1,1)) = entry of (5,6) |
| 5 | 41 rho_2 = 23 rho_4 | exit of (4,5) (= 41/rho_4, state 22) = entry of (2,3) (= 23/rho_2) |
| 6 | 65 rho_4 = 47 rho_6 | exit of (6,8) (= 65/rho_6, state 25) = entry of (4,6) (= 47/rho_4) |

Rank 6 in the six free readings; the exact solution of the six equalities is rho_5 = 47/9, rho_7 = 47 rho_5/33 = 2209/297, rho_3 = 3 rho_5/5 = 47/15, rho_6 = 7 rho_7/9, rho_4 = 47 rho_6/65, rho_2 = 23 rho_4/41,
which reproduces the vertex exactly (a path graph 3-5-7-6-4-2 of "exit(a) = entry(b)" equalities with the single anchor "R = 9 = entry of (5,6)" at reading 5). The pairs 9 rho_5 = 15 rho_3 = 47 in the task statement follow from rows 4 and 2 (15 rho_3 = 5*3 rho_3... i.e. rho_3 = 3 rho_5/5 = 47/15).

**The bound inside this cell uses only rows 3 and 4.** Exact Farkas certificate: multipliers 1/33 on row 3 and 47/297 on row 4 (the rest 0) give
rho_7 >= 47 rho_5/33 >= 47*47/(33*9) = 2209/297, hence R* = 89/rho_7 <= 89*297/2209 = 26433/2209 on the whole closed cell.
Consequently the vertex is not isolated as a maximiser: with rho_7 pinned at 2209/297 (and so rho_5 = 47/9) the other readings range over exact intervals inside the cell
(rho_2 in [16715503/7123545, 55225/23463], rho_3 in [47/15, 3355471/1059399], rho_4 in [726761/173745, 108241/25839], rho_6 in [15463/2673, 149695/25839]; `b12_A_face_v1.out`).
The four other rows are what fix a vertex, not what bound R*.
Nine fine cells (27, 28, 29 moves; three different phase-1 shapes, one shared phase-2 tail and the same two Farkas rows) have this supremum (`b12_DE_v1.out`). The supremum is not attained (closure).

## B. Derivation attempt (what closes, what does not)

Closed (exact algebra, checked):
1. Gate: reading 1 sets the move from a state in (7,9) to exactly 9 (given). R* >= 9 for crossings.
2. Telescoping identity for the phase after 9: R* - 9 = sum over later moves of (2/rho_{y_k} - s_k), with s_k = R_k - (8 j_k - 1)/rho_{y_k} >= 0 the depth of state k inside its setter's zone.
   Checked exactly on 159 distinct paths (all gate-crossing cells with tree Rhi > 11; `b12_B_identities_v1.out`). It is an identity; it bounds R* by 9 + sum of setter zone widths, which does not reach 12 by itself.
3. Same-reading lap-ratio inequality: if the opener o (lap j_o, R* = (8 j_o+1)/rho_o) is blocked at an earlier state R_a at lap j_a then rho_o >= (8 j_a - 1)/R_a, so
   R* <= R_a (8 j_o + 1)/(8 j_a - 1). The extremal cell's chain is this inequality at a = state 17 (o = 7, j_a = 6, j_o = 11) combined with R_17 = 33/rho_5 and 9 rho_5 >= 47 (reading 5 blocked at the gate state, lap 6):
   R* <= (89/47)(33*9/47) = 26433/2209. Verified: 0 violations over 159 paths; in each of them the opener is blocked at some earlier state (159/159) and the best such bound is <= 12 (maximum 11.5984 over those arrangements, which sit at R* up to 11.5925).

Not closed:
- (a) Why the opener is blocked at an earlier state, and why a state exists with R_a (8 j_o+1)/(8 j_a-1) <= 12. Only the 159-path observation, no derivation.
- (b) Anything bounding the tail 9 -> R* for an arbitrary phase-1: the identity in 2 has no upper bound on sum(2/rho - s_k) without a statement on how many moves and which readings occur after 9. Counting zone widths of six readings against the interval [9, 12] gives no contradiction by width alone (each reading's zones meeting [9,12] have total width up to 3/4 + 2/rho), so any closing argument must use the arithmetic of the laps. I found none.
- (c) The interaction of phase 1 with phase 2 through 8 frac(rho_y): in the extremal cell the link is exactly rows 3 and 4 (reading 5 is blocked at 9 at lap 6, and its exit at lap 4 sets the state where reading 7's lap-6 zone begins). I have no general statement that such a link exists, only that it does in each cell examined.
- (d) Mirror R -> 24 - R: p_y(24-R) = -p_y(R) + 24 rho_y (mod 8), symmetric only if 3 rho_y is an integer for all y. At the extremal cell the shifts 24 rho_y mod 8 are not 0 (for rho_5 = 47/9: 16/3 mod 8), so no mirror inequality follows. Undecided whether any bound at 12 can come from the mirror.
- (e) Readings above the tree window rho_7 <= 25: undecided here (the exhaustive tree stops there).

## C. Stress (exact; every cell's supremum is an exact LP with certificate)

Nothing exceeded 26433/2209 = 11.966047985... (count of cells with exact supremum above it: 0 in every run).

- C1 line scans (`b12_C_lines_v1.out`): from an exact near-vertex arrangement (vertex pulled 1e-4 into the cell, path verified). Six single-reading directions x 2 signs and 15 pairs x 4 sign choices (60 pair lines): 208 cells visited, exact boundary crossing of 1e-9 relative. Every walk stalls at the first crossing: the neighbouring cell has path length < 20 or no setter 1. Stall rows: state 1 entry(rho_6, lap 1) (the row 1 above), state 6 clear-before-zone (5,2) (row 2), state 16/17 entries of (5,4)/(7,6) (row 3), and others; list in the output. Cells beyond the first crossing are not visited, so nothing is claimed about them from this run.
- C2 pivot walk (`b12_C_pivot_v1.out`): starts = the 186 distinct fine cells from the 191 tree cells with Rhi > 11 and the gate (exact members, else rationalised witness), plus the extremal cell. At each cell's exact optimal vertex, every tight row and every pair of tight rows is crossed along an LP-chosen direction verified exactly (violated rows violated, other tight rows kept), the new cell found by path(), kept only if setter 1 occurs and length >= 20. 540 s budget: 1066 cells expanded, 1485 distinct fine cells with exact supremum, 419 left on the frontier unexpanded; maximum 26433/2209; 0 above. Crossings that lose the gate or length: thousands (the most frequent rows: entry of (7,6), entry of (6,1), entry of (5,4)); crossings with no pure direction: 1,502.
- C2b (`b12_C_facevert_v1.out`): the same pivots at all 5 exact extreme vertices of the optimal face. The component closed: 124 fine cells, frontier empty, maximum 26433/2209, second exact value 25839/2209 (11.6965), 0 above.
- C3: the 186 starting cells have exact suprema: 9 cells at 26433/2209, then 17981271/1539673 = 11.6786, 25839/2209; 0 of 186 above 12; 9 of 186 at >= 11.9. Farkas support sizes 1..6 (1: 33, 2: 85, 3: 27, 4: 24, 5: 16, 6: 1); in 156 of 186 a Farkas row sits at the gate state (R = 9), in 30 none does.
What the failing directions share: the rows that carry the crossing losses are entries into a zone at an exact state (the rows 1, 3, 4 types above), i.e. the exact coincidences "exit of one zone = entry of the next" that the extremal path needs.

## D. Window against 12 (exact)

At the extremal cell's supremum: R* = 26433/2209, 12 - R* = 75/2209, window width 216/2209, right end 567/47 (closer (5,8): entry 63/rho_5 with rho_5 = 47/9), right end - 12 = 3/47, centre - 12 = 33/2209. So R* + width/2 = 12 + 33/2209 exactly in the limit, and R* + right end = 24 + 66/2209 (not 24).
Over the 186 cells at near-supremum arrangements (R* within 1e-5 or less of the cell supremum): window contains 12 in 9 (the nine cells with sup 26433/2209), window entirely below 12 in 177; centre above 12 in those 9, below in 177; R* + right end = 24 in 0. So no exact mirror relation holds; the only relation verified is the one-cell numbers above.
