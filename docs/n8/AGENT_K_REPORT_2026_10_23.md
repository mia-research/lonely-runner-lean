Rules: 5 (no runner at speed 0), 7 (covering/counting steps tagged), 15 (exact Fractions, no floats in statements), 16 (new files only), 18 (grades below).

# Agent K report, 2026-10-23: wall-generated S2 covers (A) and four movers (B)

## Files created
Lean (`LonelyRunnerFresh/Fresh/`, each compiled singly with `./check.sh`; axioms `[propext, choice, Quot.sound]`; 0 sorry/native_decide/axiom/admit/unsafe; untagged 0):
- `WallLemmas.lean`: `wall_cell` (six linear wall inequalities c1..c6 give a common clear instant of two movers in `[l, r]`, `t = max l ((n+1/8)/d1) ((m+1/8)/d2)`), `wall_cell_iff` (converse: the six inequalities are exactly the existence region for window pair (n,m)).
- `WallS2_123.lean`, `WallS2_125.lean`, `WallS2_12345.lean`, `WallS2_14567.lean`: `coreW<set>`, `exists_common_clear_W123` / `exists_union_W<set>`, and the landing theorems `land2_all_W123`, `land2_wall_125/12345/14567` (same statements as `land2_all_123` and `land2_later_<set>`; they reuse `S2CleanLemmas`, `TwoMoverCond_123` and `S2Later_<set>` landing lemmas `landL...`). Heavy lemmas use `maxHeartbeats 4000000`.
- `WallLemmas4.lean`: `r4a_rect`, `r4b_rect` (see B).
Python (`experiments/n8/`): `wall_cover_v1.py` (geometry, BSP, strip DP), `wall_dp_run_v1.py`, `wall_gen_lean_v1.py` (generator; every leaf re-checked by independent vertex enumeration before Lean is written), `wall_fail_region_v1.py`, `wall_batch_v1.sh` + `.out`, `wall_four_movers_v1.py` + `wall_four_movers_v1.out`.

## A. Wall-generated covers
Mechanism [L, pointwise]: in piece `[l, r]` with window pair (n, m) the common clear set is nonempty iff c1..c6 hold, all LINEAR in (d1, d2): c1/c2 ray walls `d2/d1 <= (8m+7)/(8n+1)`, `>= (8m+1)/(8n+7)`; c3/c4 `d1 >= (8n+1)/(8r)`, `<= (8n+7)/(8l)`; c5/c6 the same for d2. So the existence region of a piece is a union of convex polygons Q(j,n,m) bounded only by pairwise ratio walls and verticals/horizontals at `(8n +- 1)/(8 w)`. The old point witnesses and R1 boxes are subsets of these polygons.
Cover: strips in d1 between vertical walls (plus, for sets marked "free", free cuts on a 1/4 grid, which are not walls); in each strip an R1 threshold cut `d2 = C` (tail, rule `r1_rect`, counting tool, not a wall); below it a binary partition cut only along constraint lines of a polygon Q that meets the cell (wall cuts); strips chosen by dynamic programming over breakpoints (cell count minimised). `d1 > D0` by `big_both`. Tags: [PROVISIONAL: covering], [PROVISIONAL: counting tool].

Cell counts, old (S2Clean/S2Later boxes) against wall-generated [DP; Lean compiled for the first four]:
| set | old | wall | strips (free cuts) |
|---|---|---|---|
| 123 | 7 | 5 [L] | 1 (0) |
| 125 | 9 | 4 [L] | 2 (0) |
| 12345 | 52 | 35 [L] | 9 (0) |
| 14567 | 136 | 100 [L] | 42 (0) |
| 124, 134, 1234 | 17 | 9 | 4 (2) |
| 234 | 5 | 2 | 1 (0) |
| 2345 | 8 | 2 | 1 (0) |
| 23456 | 12 | 5 | 1 (0) |
| 34567 | 9 | 2 | 1 (0) |
| 1235 | 22 | 11 | pure walls |
| 1245 | 19 | 11 | 5 (2) |
| 1236 | 18 | 9 | 4 (1) |
| 1345 | 53 | 39 | 9 (3) |
| 12347 | 55 | 28 | 11 (4) |
| 1456 | 57 | 32 | 14 (4) |
[OBS] for the rows not compiled (generator output only; Lean not emitted). The wall cover is smaller in every set tested (about 30 to 80 percent fewer cells). A greedy BSP without the strip DP gave 5, 6, 46, 164 for the four compiled sets (smaller for 123/125, larger than the old cover for 14567), so the saving depends on the strip optimisation, not only on the walls.
Exact wall lists used (cut lines in the compiled covers):
- 123: ray y/x = 9/7; horizontals y = 27/7, 7; R1 threshold y = 13.
- 125: no ray/vertical/horizontal wall; R1 thresholds y = 11/2, 13/2 (two strips).
- 12345: rays 25/23, 9/7, 23/17, 5/3, 17/7, 23/9, 31/9, 13/3; vertical x = 17/3; horizontals y = 7, 50/7, 85/7, 15, 275/17, 125/7, 165/7, 205/7; R1 thresholds 11/2, 17/2, 17, 18, 22, 33.
- 14567: rays 65/63, 71/65; verticals x = 12/5, 18/5, 9, 186/17, 17, 33; 16 horizontals (7, 231/31, 138/17, 217/25, 9, 161/17, 10, 217/17, 15, 273/17, 82/5, 282/17, 17, 23, 25, 31); R1 thresholds 12, 13, 29/2, 15, 22, 23, 30, 32, 33, 40.
Failing region of the first piece [OBS, `wall_fail_region_v1.py`, y <= 60]: for 125, 1235, 12345 (identical first piece [1/8, 7/40]) four triangles/quadrilaterals with vertices such as (45/7, 15), (45/7, 765/49), (105/17, 15), bounded by the walls x = 7, x = 45/7, y = 7, 15, 23, 85/7, 165/7 and rays y = 9/7 x, 5/3 x, 17/7 x, 25/7 x, 31/9 x. For 14567 the first piece is a point (1/8) and the failing region is the complement of the lattice windows (verticals and horizontals at 8n +- 1). No failing cell is left uncovered once pieces up to J are used (generator closes with zero holes).
Interpretation: the S2 box edges (grid values k/16) are not walls; the true boundaries of existence are the walls above, and the covers are smaller when cut along them. The R1 threshold and the free 1/4-grid cuts are the only non-wall cuts.

## B. Four movers
Frozen sets: 44 sets of size 2 to 3 (readings `|i-k|` of the 3 runners left after removing the subject and 4 movers; sizes 1 do not occur; 2: 9 sets, 3: 35 sets). Sampling [OBS, exact, `wall_four_movers_v1.out`]: per set 50,000 random rational quadruples in (a, 60] (denominators up to 64) and 20,000 adversarial (near integers, near rational multiples of d1 including the (8a +- 1)/(8b +- 1) ratios, near (n +- 1/8)/piece-end, four near-equal values, near a); first lonely instant searched up to T = 40.
- Share landing in the first wide piece: 1.0000 for 25 sets (including 12, 13, 123, 23x, 34x, 4xx, 567); lowest 0.91 to 0.94 for 16, 126, 136, 146, 156; lowest overall 0.64 (random) and 0.43 to 0.49 (adversarial) for 127, 137, 147, 157, 167, whose first wide piece is index 1 (a point piece precedes it); 0.99+ for 14, 15, 124, 125, 134, 135, 145.
- Maximum piece index 4 (set 157 random); maximum 3 elsewhere in adversarial runs.
- Maximum T over all 44 sets and both samplers: 0.472 (set 137 adversarial), i.e. no landing after the first lap; count of T > 3: 0 in every set; count with no lonely instant found: 0 in every set.
No counterexample to existence was found. [OBS] only; range of d limited to 60 and to the sampler families above.
Rules proved [L] (`WallLemmas4.lean`, [PROVISIONAL: counting tool]): R4a `r4a_rect` (two movers each clear on [p,q], the other two via `two_clear_in2` when `p + 1/A <= q`); R4b `r4b_rect` (three movers clear on [p,q], the fourth via `opening_close` when `1 <= 4 dd (q - p)`).
Not done: no four-mover box cover and no Lean theorem for any four-mover frozen set. The cover is four-dimensional (sorted d1 <= d2 <= d3 <= d4) and no large-d rule exists (four blocked sets of density 1/4 can cover; the measure lemma gives nothing); time was spent on A and the observation tables. The structure observed matches the three-mover case (landing in the first wide piece or one to four pieces later, within the first lap).

## Not proved
- The walls are shown to bound the existence region exactly (`wall_cell`, `wall_cell_iff`), but the cover remains a finite cover found by search; the choice of strips is by DP, not derived from the arrangement alone. Sets other than the four compiled have counts only from the generator.
- Movers at or below the least frozen reading; the cascade's path; the four-mover existence statement.
- Nothing committed; no existing file edited; `RUNNING_LOG_order8_v1.md` untouched.
