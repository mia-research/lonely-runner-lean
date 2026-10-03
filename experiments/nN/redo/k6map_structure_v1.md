# k6map_structure_v1 -- K6 as the six-reading cascade; the pins of the extremal gate-crossing vertices

All stated facts are exact Fractions: windows by `k6map_lib_v1.K6` (checked equal to `ceil_k6_lib_v1.clear_components`, 3,000 + all tested tuples, plus a pointwise blocked/clear test of endpoints), crossings by `path()` of `cascade_path_map_v1.py`, cell optima by exact Fraction vertex solves with every row checked in Fractions and an exact dual (Farkas) certificate. Floats only chose LP bases and sampling. Negatives are "not reached by (search)". Undecided is marked.

## 0. Reused from the record (not rebuilt)

* `ceil_gate_crosser_v1.md`: Lemma 2 (K6 and the zones of reading 7), (W) rho_7 < 2/l_max, X24, the fine-cell machinery `b12_cell_lib_v1.py` (cell_rows, min_rho_s_exact), `ceil_lib_v1.maxrho/tight/dedupe_rows`, `ceil_allowed7_v1` (here redone with H = 7), exact vertices of `ceil_pivot7b_v1.out`, `ceil_pivot6_v1.out`.
* `b12_landing_bound_v1.md` section A (the six tight rows of the 2209/297 vertex).
* RUNNING_LOG E358 (`k6_longest_v1.py`, `k6_progression_v1.out`; MANUSCRIPT_v21 17C R8, 17E "length step"), E354 (R1).
* `stress_seeds_v1.pkl` (11,176 exact gate crossers) as the source of seven-reading arrangements.

## 1. Task 1

### 1(a) K6 on [1,7], exhaustive grids (`k6map_task1a_v1.py`, outputs `k6map_task1a_{int24,mix8,half16,third12}_v1.out`)

K6 = clear set of readings 1..6 on [1,7], closed windows, point windows included. Reading 1's own zone (7,9) starts at 7 and contributes no zone inside [1,7].

| grid (six-sets {1} + five values) | six-sets | components per K6 | six-sets with a point window | most point windows | K6 empty or all point windows |
|---|---|---|---|---|---|
| integers 2..24 | 33,649 | 4..34 | 15,187 | 10 | 0 |
| halves 3/2..16 (step 1/2) | 142,506 | 2..21 | 67,003 | 8 | 0 |
| thirds 4/3..12 (step 1/3) | 237,336 | 1..18 | 82,709 | 9 | 0 |
| halves and thirds up to 8 (28 values) | 98,280 | 1..11 | 28,284 | 5 | 0 |

The full (components, point windows) -> count tables are in the `.out` files.

* Longest component: integers, 6/11 at (1,2,3,6,7,11); halves, 1 at (1,3/2,2,5/2,3,7/2); thirds, 13/8 at (1,4/3,5/3,2,7/3,8/3); mixed, 2 at (1,4/3,3/2,5/3,2,7/3).
* Least total length of K6: 29/154 at (1,4,5,6,7,11) (integers, halves, thirds); 8/35 at (1,2,3,4,5,7) (mixed grid, bounded by 8).
* Progression 1..6 (exact): windows [1,7/6], [9/4,7/3], {3}, [17/5,7/2], [9/2,23/5], {5}, [17/3,23/4], [41/6,7]; 8 windows, two of them point windows (R = 3 and R = 5, where readings 3 and 5 sit at positions 1 and 7 together), longest 1/6. 1,2,3,4,5,7: {1}, [9/7,7/5], {3}, {5}, [33/5,47/7], {7}; 6 windows, 4 point windows.
* Deformation of the progression (`k6map_prog_deform_v1.py`, `k6map_prog_deform_v1.out`; reading k moved by d/200, |d| <= 90, or joint exact perturbations |d| <= 0.1, 3,000 draws): the point windows at 3 and 5 are not stable under motion of reading 3 (moved: components 5..7 and 0 point windows in all 180 deformations) or reading 5 (0 point windows except one); the open windows persist. Joint perturbations: 4..9 components, 8 of 3,000 with a point window, longest component in [1/6, 6970/17157]. So in the progression the point windows are tie phenomena of the integer lattice the open windows persist; in these deformations the longest component never fell below 1/6.
* Component counts on the integer grid: odd counts (9, 11, ..., 27) occur in 462 of the 33,649 six-sets, even counts in the rest. No parity rule was derived (undecided).
* Not reached by these grids: a six-tuple with K6 empty or with K6 a finite set (all point windows). This is Lemma 4/5's source condition of `ceil_gate_crosser_v1.md`; the walk of 1(c) also did not reach one.

### 1(b) R2 against the direct cascade (`k6map_task1b_v1.py`, `k6map_task1b_seeds_v1.py`; outputs `.out`)

R2: for six readings, the set of rho_7 > rho_6 for which the seven-reading cascade has landing > 7 equals the intersection over components [a,b] of K6 of the union over j >= 1 of ((8j-1)/a, (8j+1)/b) (open; ties are clear points).

* 2,000 six-tuples in `k6map_task1b_seeds_v1`: 1,000 sixes of exact gate crossers (all 1,000 own rho_7 inside the R2 set) and 1,000 exact perturbations (readings 2..6 moved by up to 1e-3) of other crossers' sixes; 1,978 have a nonempty R2 set. 40,811 exact rho_7 test points (midpoints, endpoints, endpoints +- width/1000, +- 1e-9, gaps, random up to cap 80): 6,955 direct crossings, 33,856 not; **0 mismatches** between R2 and `path()`.
* `k6map_task1b_v1.py`: 1,000 generic tuples (random families) plus 1 search of 459,601 random draws within 330 s: **only X24's six had a nonempty R2 set** above rho_6 (cap 80); 10,541 test points, 0 mismatches. The R2 set of X24's six: (8.98344, 9) u (24.35999, 24.40084). The six of the 16.2108 vertex has an empty set (the vertex has a clear tie point). So random six-tuples are not a source of gate crossers; the crossers' sixes are.
* sup(R2 set) * L_max / 2 over the nonempty tuples: max 0.999988, min 0.343476 (each < 1, as (W) requires). The equality sup = 2/L_max holds exactly when a zone of reading 7 fits the longest component exactly at the closure; 0.999988 is the nearest the data came. In general the maximal rho_7 is min over components of (8j+1)/b, not 2/L_max.

### 1(c) Smallest L_max * rho_6 (ratio = L_max / (2/(7 rho_6)) = 7 rho_6 L_max / 2)

**Exact structure used (`k6map_lp_v1.py`).** With u_y = 1/rho_y every zone endpoint (8j-1)u_y, (8j+1)u_y and the bounds lo = u_1, hi = 7u_1 is linear in u. The fine cell of a six-tuple (sorted order of all endpoints in the window, including one lap beyond hi for each reading, rank order) is a polyhedral cone; each component length is a linear form in u; rho_6 L_i = L_i(u)/u_6 is linear-fractional, so by Charnes-Cooper (w = u/u_6, w_6 = 1) the exact minimum of the ratio over the closed cell is an LP in (w_1..w_5, t). Each cell value below is an exact Fraction vertex with all rows checked and an exact dual.

**Walk (`k6map_walk_v1.py`, `k6map_walk_resume_v1.py`, `k6map_walk_wide_v1.py`).** Seeds: progression, X24's six, the grid minimisers (mixed grid 14/9, (1,3,7/2,4,5,20/3), (1,2,5,6,7,8), (1,4,5,6,7,11), (1,2,3,4,5,7)), the 16.21 vertex six, 40 sixes of crossers; neighbouring cells found by exact micro-perturbations (scales 1e-7 .. 1/300) of each cell's vertex, cells expanded lowest value first. Run 1: 6,085 certified cells, 420 s, 0 LP uncertified. Resume with 60 lowest: closed (no new cell). Wide run (1,470 random-family seeds, 520 s): 4,619 cells, 9 LPs uncertified, best 84/43 = 1.9535 (the walk from generic seeds does not reach the lower region; the lower region was reached from the grid-minimiser seeds).

**Minimal ratio found, exact: 6615/7496 = 0.882471** (cell minimum; closure vertex; the vertex is a valid arrangement, strictly increasing):

rho = (1, 6559/2279, 26236/6779, 231/47, 26236/4115, 7).

Independent check (`k6map_best_check_v1.py`, `.out`): K6 by two implementations equal; windows {1}, [37035/26236, 47/33], [25/7, 94645/26236], [115243/26236, 31/7], [135795/26236, 34185/6559], [38743/6559, 155917/26236], {47/7}, {7}; four windows of length 135/3748; L_max = 135/3748 = 0.036019 < 2/(7 rho_6) = 2/49 = 0.040816; ratio = 6615/7496. Endpoints and midpoints are clear and points 1e-12 outside the components are blocked (exact). An interior arrangement of the same cell (micro-jitter, same signature) has ratio 0.882474.

* Binding in the cell (exact dual): the four windows of length 135/3748, bounded by exit(6,3)..entry(5,3), exit(3,2)..entry(6,4), exit(5,4)..entry(2,2), exit(2,2)..entry(3,3), dual weights 9537, 7935, 6647, 5865 over 29984. The remaining rows of the vertex (the position of rho_4) are not binding: rho_4 ranges over several values (231/47, 161/33, 865788/175211, ...) at the same ratio 6615/7496, listed in `k6map_minstruct_v1.out`.
* Next cell minima: 165/184 = 0.896739, (1,3703/1287,76636/19799,161/33,103684/16265,7); 2205/2306; 105/109; 39/40; 299460/303337; 1020/1033 (all below 1).

**What the minimising tuples share (`k6map_minstruct2_v1.py`, `.out`).** In run 1: the 50 lowest cells all have the cell-minimiser vertex with **rho_6 = 7 exactly**; of the 200 lowest, 166 have rho_6 = 7, 28 have rho_6 = 47/7; of the 1,000 lowest, 873 rho_6 = 7, 69 rho_6 = 47/7, 46 rho_6 = 20/3. rho_6 = 7 holds in 3,821 of 6,085 cells. In the wide run: rho_6 = 47/7 and 7 lead (306 and 298 of the lowest 1,000). So the minimisers pin rho_6 at 7 (entry (6,1) = 1 = lo) or 47/7 (entry (6,6) = 47/rho_6 = 7 = hi): the two ends of the window [1,7]. Their K6 has three point windows (at 1, 47/7 and 7 for the best): ties of the pinned reading with the window ends. The lowest cell with rho_6 not 7 in run 1 is 7/6 (rho_6 = 47/7).

**Consequences (exact).**
1. The inequality "longest component of K6 >= 2/(7 rho_6)" (E358: tested ratio >= 1.84) **is false**: ratio 0.882471 at the tuple above. The record's R8 is about a lonely cell of the seven-reading arrangement, not about the first window; the first-window version, which the route "rho_7 < 2/L <= 7 rho_6" of E354/E358 needs, does not hold. The route rho_7 <= 7 rho_6 through R8 therefore does not close by this step. (R8 itself is not tested here and is not contradicted.)
2. The best tuple has an empty R2 set (cap 400; vertex and interior point): it is not a six of a gate crosser. So the exception to the bound does not, by itself, give a gate crosser with rho_7 > 7 rho_6.
3. `k6map_allowed_walk_v1.py`: for 8,457 visited cells (10,702 examined, lowest first, interior point re-found; cap 1000), R2 sets are nonempty in 85; the largest sup(R2)/(7 rho_6) is 0.33641 (so rho_7 < 2.36 rho_6 there) at the cell with ratio 2.43478, set (16.4578, 16.4839). The lowest-ratio cell with a nonempty R2 set: ratio 168/101 = 1.66337, set (8.0907, 8.1429). Not reached by this walk: a gate crosser with rho_7 > 0.34 * 7 rho_6, other than X24 (rho_7/rho_6 = 3.48 = 0.497 * 7).
4. Upper end: the walk found no cell minimum under 0.882471. "Not reached by (the three walks above)"; the true infimum over all six-tuples is undecided.

## 2. Task 2: why extremal vertices pin rho_5 or rho_6

Scripts: `k6map_pins_v1.py` (IDX 7 and 6; `k6map_pins_idx7_v1.out`, `k6map_pins_idx6_v1.out`), `k6map_pins_vertices_v1.py` (`.out`). Cells: 7,003 distinct fine cells (the 11,176 seeds, X7, X24); for each, the exact maximum of rho_7 (resp. rho_6) over the closed cell, vertex and dual verified in Fractions.

**P1 (checked on all 7,003 cells, and by construction of `cell_rows`).** Every row has at most two nonzero entries, and a row with two entries is of the form p rho_a >= q rho_b with p, q > 0 (the entries are state heights c/rho_s against zone endpoints (8j+-1)/rho_y). The maximum number of nonzero entries in any row was 2.

**P2 (proved from P1; checked 7,003/7,003 for rho_7 and 7,003/7,003 for rho_6).** At a vertex of the closed cell (cone cut by rho_1 = 1) the tight rows form a graph on the seven readings that is connected. Proof: if a component C of the tight graph does not contain reading 1, multiply the readings of C by 1 +- eps; every tight row (both ends in C or both outside) stays tight, every non-tight row stays satisfied for small eps, so the point is not a vertex. A connected spanning graph with 6 independent rows is a spanning tree (cycles with gain 1 add no rank; gain != 1 forces a zero reading). Hence **some tight row is incident to reading 1**, and the value of its other reading is fixed as a rational (8j+-1)/h (times rho_1 = 1).

**P3 (proved form; checked).** The rows incident to reading 1 are of three kinds: (i) states set by reading 1: R = 1 (the start) and R = 9 (exit of (1,1), the gate state); (ii) the status of reading 1 at another state R = c/rho_s: tie with its entry R = 7 or its exit R = 9, or lap-0 clearance (R >= 1); i.e. the state height h of a tight row incident to reading 1 is one of 1, 7, 9. Checked: the heights at which these rows sit, over all 7,003 cells and both objectives, are exactly {1, 7, 9} (counts 190 / 2,927 / 6,492 for rho_7; 206 / 2,785 / 6,746 for rho_6). So the pinned value is (8j +- 1)/h with h in {1,7,9}. The three heights are lo = 1, hi = 7 of the window and 9 = exit of reading 1's first zone; each is = +-1 mod 8, the positions of reading 1 (rho_1 = 1) at its zone endpoints. A reading y has a tie (entry or exit of some zone) at height h iff h rho_y = +-1 mod 8.

Pins on the named vertices (all exact, from `k6map_pins_vertices_v1.out`, rows with their states):

| vertex (objective) | pinned reading and row | h | value |
|---|---|---|---|
| X24 cell (max rho_7 = 86989/3565) | R = 1 <= entry(6,1), state 0 | 1 | rho_6 = 7 = 7/1 |
| 511/31 vertex (max rho_7) | same row | 1 | rho_6 = 7 |
| 16.21 cell (max rho_7 = 34675/2139) | R = 9 = exit(5,7), state 22 | 9 | rho_5 = 57/9 = 19/3 |
| b12 vertex (min rho_7 = 2209/297, R* sup 26433/2209) | R = 9 = entry(5,6), state 20 | 9 | rho_5 = 47/9 |
| rho_6 max, 57/7 vertex | R = 7 = entry(1,1) = exit(6,7), state 24 | 7 | rho_6 = 57/7 |
| rho_6 max, 73/9 vertex | R = 9 = exit(6,9), state 25 (also rho_5 = 7 at R = 1, rho_7 = 79/9 at R = 9) | 9, 1 | rho_6 = 73/9 |

The vertex 124509/15275 (rho_5 = 7 pinned, rho_6 max of `ceil_pivot6_v1.out`): not reached by 3,000 micro-jitters in 60 s (the cell was reached by the pivot walk of `ceil_pivot_v1.py`, not by jitter); its row list is in `ceil_pivot6_v1.out`.

**P4 (LP duality on the tree; observed on the 5 vertices with duals listed, proved for a nondegenerate vertex).** The optimal dual of max rho_s over a tree of binary rows is supported on the tree path from s to reading 1, so the bound is rho_s <= rho_pin * prod of ratios (8j+1)/(8j'-1) along that path. Checked: X24 path 7-2-3-6-1 (multipliers 1/15, 43/115, 731/3565, 12427/3565); 16.21 path 7-6-5-1 (1/31, 73/713, 1825/6417); 511/31 path 7-6-1 (1/31, 73/31); b12 path 7-5-1 (1/33, 47/297); 57/7 vertex, rho_6 path 6-1 (1/7). The ceiling of a cell is the anchor value times a product of lap ratios, and the anchor value is a number (8j+-1)/h, h in {1,7,9}.

**Why 7 and 19/3 appear most.** (observed + elementary) rho = 7 is = -1 mod 8, so 7h = +-1 mod 8 for each of h = 1, 7, 9: a reading at 7 has a tie at all three heights at once (entry (y,1) at R = 1, exit (y,6) at R = 7, entry (y,8) at R = 9). A tie at h = 1 alone forces rho = 8a+-1, so 7 is the only reading in (1,9) with a tie at h = 1, and it has the other two as well. 19/3 = 57/9 has a tie at h = 9 only (exit (y,7)); 47/9 at h = 9 (entry (y,6)); 57/7 at h = 7 (exit (y,7)); 73/9 at h = 9 (exit (y,9)). The pins at the maximisers are the largest values of the form (8j+-1)/h that the cell's other rows allow; no other derivation was found. In the K6 ratio minimisers of 1(c) the same two anchors appear as the window ends: rho_6 = 7 (h = 1) or 47/7 (h = 7); there the proof of P2 does not apply (the component rows have up to four readings), so those pins are **observed**.

**Observed counts of pins over all 7,003 cells (not only maximisers).** The pinned readings by rank: every rank 2..7 occurs, and the most frequent values are 31/9, 25/7 (rank 3), 13/3 (rank 4), 55/9 (rank 6), 23/9, 17/7 (rank 2). rho_6 = 7: 195 cells; rho_5 = 7: 5; rho_5 = 19/3: 7; rho_6 = 19/3: 150. So "rho_5 or rho_6 pinned at 7 or 19/3" is a property of the maximisers of rho_7 and rho_6, not of cells in general: in general the pin sits on any rank.

## 3. What does not close

* Why the maximiser's anchor reading has rank 5 or 6 and why j (6 for h = 9, 7 for h = 9, 1 for h = 1) is what it is: no derivation; observed in the 7 vertices above.
* Any bound on the product of lap ratios along the tree path (the open ceiling): P4 only identifies it.
* The absolute ceilings of rho_7 and rho_6 stay open; the walk of 1(c) and the check 3 of 1(c) give: the largest sup(R2)/(7 rho_6) among visited low-ratio cells is 0.336, X24 has 0.497.
* The infimum of 7 rho_6 L_max / 2 over all six-tuples: 6615/7496 is the lowest cell value reached; three walks, 10,702 cells.
* Parity of the component counts; the structure of the point windows beyond the progression (ties at the heights 1, 7, 9 and between readings with h rho = +-1 mod 8 are the candidates; not derived).
* The cell of the 124509/15275 vertex was not reached by jitter; tight rows are taken from `ceil_pivot6_v1.out`.
* The 0 mismatch of R2 is on 2,000 + 1,000 tuples at cap 80; rho_7 > 80 is not covered by the direct test.

## 4. Files

Libraries: `k6map_lib_v1.py`, `k6map_lp_v1.py`. Task 1: `k6map_task1a_v1.py`, `k6map_task1b_v1.py`, `k6map_task1b_seeds_v1.py`, `k6map_prog_deform_v1.py`, `k6map_walk_v1.py`, `k6map_walk_resume_v1.py`, `k6map_walk_wide_v1.py`, `k6map_minstruct_v1.py`, `k6map_minstruct2_v1.py`, `k6map_best_check_v1.py`, `k6map_allowed_walk_v1.py`. Task 2: `k6map_pins_v1.py`, `k6map_pins_vertices_v1.py`. Outputs: `k6map_*.out`, pickles `k6map_walk_best_v1.pkl`, `k6map_walk_best_v2.pkl`, `k6map_walk_best_wide_v1.pkl`.
