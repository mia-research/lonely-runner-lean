# Agent E report, 2026-10-23: AP landing law beyond relative radius 1/8 (end subjects to 1/6, interior subjects)

Rules: 5 (no runner stationary; readings are differences from a positive-speed subject), 7 (no caps or move budgets as lemmas; chain inequalities only), 8 (checked through the cascade's own path), 15 (exact Fractions; no floats in any script), 16 (new files only, nothing committed), 18 (grades below).

[L] = Lean compiled with `[propext, choice, Quot.sound]` only; scan 0 sorry/native_decide/axiom/admit/unsafe; untagged Prop defs 0. Every file compiled one at a time with `./check.sh`. Scripts are [OBS].

## Lean results

Speeds within delta of `c + i` give relative readings within 2 delta (box |e_i| <= rho, rho = 2 delta, a sufficient superset of the correlated deviations).

1. [L] `APLawR4_Interior.lean`: `interior_firstIso_d`, `ap_interior_firstIso_d`, `ap_interior_lands_d`. Interior subjects k = 2..5 (farthest runner at distance <= 5): `FirstIso v k (1/(8m))` and `Lands v k m` for ALL speeds within delta <= 1/8 (rho = 1/4). The ratio condition is `5 + 2 delta <= 7 (1 - 2 delta)`, tight at 1/8. (Previously 1/16.)
2. [L] Subjects k = 1 and 6 (farthest runner at distance 6; ratio condition fails beyond delta = 1/16): exact chamber tree on the nominal readings (1,1,2,3,4,5,6), k = 6 by mirror reading order.
   - rho = 1/6 (speeds 1/12): `APLawR4_I1_6_{ChainA,ChainB,LeavesA,LeavesB,Core,Arr}.lean`, 14 leaves; `apLawR4_I1_6_core`, `apLawR4_I1_6_end_1`, `apLawR4_I1_6_end_6`.
   - rho = 1/4 (speeds 1/8): `APLawR4_I1_4_{ChainA..C,LeavesA,LeavesB,Core,Arr}.lean`, 18 leaves; `apLawR4_I1_4_end_1`, `apLawR4_I1_4_end_6`.
3. [L] `APLawR4_Interior6.lean`: `ap_interior_firstIso_8`, `ap_interior_lands_8`: ALL SIX interior subjects, speeds within 1/8 (FirstIso, and Lands via a neighbour reading).
4. [L] END subjects at relative radius 1/6 (speeds within 1/12): `APLawR4_E_6_{ChainA..V}.lean` (172 chain theorems, up to 18 moves), `APLawR4_E_6_Leaves{A..U}.lean` (201 leaf lemmas), `APLawR4_E_6_Core.lean` (`apLawR4_E_6_core`, 200 splits, 19 landing forms), `APLawR4_E_6_Arr.lean` (`apLawR4_E_6_end_0`, `apLawR4_E_6_end_7`: FirstIso at `(M+1/8)/reading`, speeds within 1/12). 376 of 376 declarations print the standard axioms.
5. [L] `APLawR4_All12.lean`: `ap_nbhd_firstIso_12`, `ap_nbhd_lands_12`: ALL EIGHT subjects, speeds within 1/12 of `c + i` (ends: item 4; 1, 6: item 2; 2..5: item 1). This improves `ap_nbhd_firstIso_8` (speeds 1/16).

Files created (Lean, in `/Users/trentpalelei/Desktop/Math Ex/LonelyRunnerFresh/Fresh/`): `APLawR4_Interior.lean`, `APLawR4_Interior6.lean`, `APLawR4_All12.lean`, `APLawR4_I1_6_*` (6 files), `APLawR4_I1_4_*` (7 files), `APLawR4_E_6_*` (45 files: Chain A..V, Leaves A..U, Core, Arr). Scripts (`/Users/trentpalelei/Desktop/Math Ex/experiments/n8/`): `ap_r4_chambers_v1.py` (exact enumerator for any nominal reading vector; own simplex from `ap_r3_chambers_v1.py`), `ap_law_gen_r4_v1.py` (Lean generator), `ap_r4_verify_v1.py` (exact audit), `ap_r4_growth_v1.py` (+ `ap_r4_growth_v1_prim.py`), `ap_r4_entry_v1.py`. Tree pickles are in the session scratchpad.

## Chamber counts (exact enumerator finished in every row listed; [OBS])

Nominal readings: end E = (1..7); interior k=1,6: (1,1,2,3,4,5,6); k=2,5: (1,2,1,2,3,4,5); k=3,4: (1,2,3,1,2,3,4). Radius is relative (rho); speeds are rho/2.

| rho | E leaves (chain types, max moves) | I1 (k=1,6) | I2 (k=2,5) | I3 (k=3,4) |
|---|---|---|---|---|
| 1/64, 1/32, 1/16 | 3, 5, 6 (max 11) | 2 | 2 | 2 |
| 1/12, 1/10 | 10 (11), 21 (18) | 2 | 2 | 2 |
| 1/8 | 39 (32 types, 18) | 2 | 2 | 2 |
| 1/7 | 126 (105, 18) | 8 (max 4) | 2 | 2 |
| 1/6 | 201 (172, 18) | 14 (max 8) | 2 | 2 |
| 1/5 | 379 (330, 26) | 16 (8) | 2 | 2 |
| 1/4 | not run | 18 (9) | 2 | 2 |
| 3/10 | not run | not run | 8 (3) | not run |
| 1/3 | not run | 137 (111 types, 15) | 42 (9) | 2 |

I2 has 2 leaves exactly up to 1/4 and I3 at least to 1/3, matching the ratio-condition limits 1/4 (distance 5) and 3/8 (distance 4); the 2 leaves are "which neighbour is nearer" with `T = 1/(8 min)`. No run at 1/4 for E (earlier attempt did not finish in four minutes; I did not retry beyond 1/5). Nothing is claimed for radii not in the table.

Exact audit (`ap_r4_verify_v1.py`): every chain inequality of every leaf is implied by box + path (exact simplex), and the leaf formula equals the cascade's first lonely instant (exact) at box corners, random, mixed, on-hyperplane, vertex and +-1e-6 points. Defects 0 for: E 1/7 (126 leaves, ~40,000 points), E 1/6 (201 leaves, ~62,000), E 1/5 (379 leaves, ~98,000), I1 1/6, I1 1/4. [OBS]; the Lean case tree is the soundness (at 1/5 for E no Lean was attempted).

Does any chamber fail the pattern? Not at any radius reached: every chamber is one conjunction of linear inequalities in the x_i (overlaps strict, end windows weak); the enumerator asserts at each witness that the cascade's own type satisfies its chain inequalities (never violated); no lap integer varies inside a leaf (the windows are part of the type and the leaf check passes); no non-linear boundary.

## Growth and structure ([OBS] unless Lean-backed)

- Leaf counts for E: 3, 5, 6, 10, 21, 39, 126, 201, 379 at rho = 1/64, 1/32, 1/16, 1/12, 1/10, 1/8, 1/7, 1/6, 1/5. For I1: 2 (<=1/8), 8, 14, 16, 18, 137 at 1/7, 1/6, 1/5, 1/4, 1/3. Growth is by jumps with plateaus (I1: 14, 16, 18 between 1/6 and 1/4, then 137 at 1/3), not a smooth rate. Largest move count: E 11 (to 1/12), 18 (1/10 to 1/6), 26 (1/5); I1 8 (1/6), 9 (1/4), 15 (1/3).
- The wall family is radius-independent and nested. Every split hyperplane, every chain-inequality hyperplane (primitive integer form) and every landing form of a smaller radius reappears at each larger radius (E: chain hyperplanes 44, 65, 75, 110, 187, 217, 219, 223, 343 at 1/64 ... 1/5, all kept; split hyperplanes 2, 4, 5, 9, 18, 25, 28, 30, 62; I1: 23, 60, 95, 106, 108, 230 chain hyperplanes, all kept). A radius selects which walls meet the box. The radius at which a wall `w.e + c = 0` enters is `|c| / sum|w_i|` (exact, `ap_r4_entry_v1.py`): for E at 1/6 all 30 split walls have entry radius <= 5/32 (two are cones, entry 0: `7e1 - e7`, `5e3 - 3e5`); at 1/5 all 62 have entry <= 11/56. The first constant-term wall `31 e2 - 9 e7 = 1` enters at 1/40, as in E569.
- Every wall involves exactly two readings: it is a ratio threshold `x_j / x_i` against an odd-over-odd rational `(8a +- 1)/(8b +- 1)` (or `(8W+7)`): a pairwise condition between zone ends. The chamber complex is the restriction to the box of the arrangement of these pairwise ratio walls, and the Lean proof of each chamber is the same zone chain.
- Landing forms `(M + 1/8)/x_i`: E has 3, 5, 6, 9, 16, 19, 19, 19, 28 distinct forms at 1/64 ... 1/5. From 1/8 to 1/6 the set is stable at 19 (all with M <= i-1; of the 22 candidates `(1,0)` and `1 <= M <= i-1`, absent are (6,1), (6,4), (7,1)). At 1/5 it grows to 28 and laps beyond i-1 appear ((4,5), (5,6), (6,6), (6,9), (7,8)): this is the first radius where the lap index leaves the range seen below, so "slowly growing" holds only up to 1/6; at 1/5 the set grows by 9.
- Interior subjects: for k = 2..5 the complex is trivial to 1/4 (k=2,5) or 3/8 (k=3,4), exactly the ratio condition. k = 1, 6 is the only interior place the chamber regime starts before 1/4: it begins at 1/7, i.e. just beyond the ratio limit 1/8 (k=1 limit `6 + rho = 7(1 - rho)`), and the complex is far smaller than the end subject's (14 against 201 at 1/6) because two readings of nominal 1 shorten the chains.

## Not proved / owed

- End subjects at rho = 1/5 (379 leaves, max 26 moves): enumerated and audited only; no Lean. Radii between 1/6 and 1/5, and 1/4: not run for E.
- Interior k = 1,6 at rho between 1/4 and 1/3 and at 1/3 (137 leaves): enumerated only. k = 2,5 beyond 1/4 and k = 3,4 beyond ratio 3/8 in Lean: not done (enumerated 42 leaves for k=2 at 1/3; no Lean).
- The box is the full relative box, a superset of the reachable deviations (`dv_j - dv_k`); no claim that a leaf is reached, nor of leaf measures.
- Statements are FirstIso / Lands for explicit neighbour readings; the subject-moving and path statements are untouched. The landing forms in each theorem are listed as a disjunction without attributing a form to its chamber (the attribution is the tree).
- Wall-family structure statements above are observations on the enumerated trees, not a theorem about all radii.
