# Digest 04: RUNNING_LOG_order8_v1.md lines 11281-12461 (E382 to E442, 61 entries; all lines read)

Grade tags are copied from the log. Paths under `LonelyRunner/experiments/nN/redo/` unless a path is given. Within each section items appear in log order by reading batch (E382-E406, E407-E420, E421-E430, E431-E438, E439-E442).

## 1. FINDINGS

- E382: followed the isolation from the AP to targets x(lam) = x0 + lam(v − x0) approaching the vertex of J=2 cell 109535 (landing 58617539133512/5056512138355 = 11.5925; vertex pins 9 rho5 = 47 rho1, 15 rho3 = 47, rho7 = 2209/297), lam in {0, 1/2, 9/10, 99/100, 1−10^-3, 1−10^-4, 1−10^-6, 1−10^-8} (log writes the last three as "10^-4, 10^-6, 10^-8" after "1 − 10^-3"); events per path 4 or 5 in all eight, no growth as lam → 1; oracle check 0 violations; every event a death, every simple death after s = 0 is E182 case 3 (counts 3,4,4,3,3,3,3,3), no case 1/2, no multi-pinch; landings along a path about 6.4 → 11.236 → target (lam = 1−10^-8: 6.39705, 11.23618, 11.96605); inside the cell landing = 89/rho7 → 26433/2209; last two events approach s = 1 with gap about 3.07(1−lam). Script `LonelyRunner/experiments/nN/redo/deform_near_vertex_v1.py`, `near_vertex_x0_v1.txt`, `deform_near_vertex_v1_N400.out`, `_N1600.out`. [TREE]/[OBS], these 8 paths only (grid 400 and 1600 agree). Not a transfer result; finiteness half of universal transfer stays open.

- E383: relocation record found already done (E216, E217, E219); the "earlier instant" crossings of E219 B (153/306 leaving/entering whole-number sets; 106/281 fine shapes) perturbed in `earlier_instant_prediction_v1.py` (+`.out`): readings in the way at t' in the old arrangement are exactly {d} in 153/153, 306/306, 106/106, 281/281 [TESTED]; grade: forced (F5), "Not a finding". Not forced [OBS]: side of d at t': entering face leaving side 225/199, entering side 81/82; leaving face leaving side 75/19, entering side 78/87.

- E384: one-runner segment with six whole-number readings frozen. D1 (by hand): for moving reading d = p/q lowest terms, q ≥ 2, the instants u + j (u in C6 ∩ (0,1], j = 0..q−1) give q equally spaced positions; open blocked arc (−1/8,1/8) of length 1/4 cannot hold all; landing < q. D2: lonely set on the segment contains every non-integer rational; closedness of the lonely set along the segment is equivalent to loneliness at its integer points. Run `one_runner_segment_v1.py` (+`.out`), 300 random frozen sixes from 1..40: P1 (landing < q) 7,009 of 7,009, q from 2 to 12 [TESTED]; 1,800 whole-number arrangements at integer d*, all with a landing; largest ratio of the d* ± 10^-k landing to d*'s is 1.88889 (six = 5,6,19,23,33,36; d* = 55) [TESTED, these samples]. Consequence: `hbound` is not an independent input on this route; the route owes loneliness of whole-number arrangements. Not in Lean. Same-day correction gives exact values (see section 2). D1 later graded [PROVISIONAL: counting tool] (E385).

- E385: case Z: whole-number 7-set, gcd 1, some six-subset with gcd g > 1 ⇒ g does not divide the remaining reading, d/g = p/q with q = g ≥ 2, D1 gives a lonely instant [PROVISIONAL: counting tool]. Complement R: every six-subset coprime; AP 1..7 is in R. Run `pigeonhole_class_v1.py` (+`.out`), every 7-subset of 1..24: Z 11,542 sets, R 334,562; no set in either has landing R > 9; largest R: Z 22/5 at (2,6,9,12,15,21,24), R 17/3 at (3,9,11,14,15,19,24). "A map of a derived condition, not a coverage claim." Exhaustiveness for R is owed.

- E386: current case list stated: (1) ≤ six readings: order seven [L]; (2) spread ≤ 7: R1 [L]; (3) spread in (7,9]: `band_lonely` [L]; (4) spread > 9: `WideStep8 M` [OWED]. `gridStep8_one_first_stretch` [L] says `GridStep8 S m 1` gives a lonely instant with 1 ≤ 8mt ≤ 7; X24 (E354; least 1, greatest 24.38…) has least lonely R = 26062497843590/2806730537001 > 7, so `WideStep8 1` is false [P by hand from the [L] theorem and the exact landing]. M = 2 (R up to 14; `CascadeGridN`: R ≤ 15) not refuted by X24. Spread > 9 splits by the d_min gate (L1): window A (landing ≤ 7) and window B (gate crossed, landing ≥ 9).

- E387: window B = R in [9,15]; K'_1 = [9,15], K'_k = K'_{k−1} minus reading k's zones ((8j−1)/ρ, (8j+1)/ρ); needed K'_7 ≠ ∅. 1-D fact [P by hand]: reading-7 zones are disjoint open intervals of width 2/ρ7 spaced 8/ρ7; "K'_6 has a window of length ≥ 2/ρ7" suffices for K'_7 ≠ ∅. Tree facts [TREE: float-LP ranges]: crossing regions' ranges for readings 2..6 identical at J = 1,2,3 (tops about 4.82, 5.28, 6.21, 7.10, 8.15; lows about 2.14, 2.81, 3.79, 4.30, 5.44); top of ρ7 among crossers 9.0 / 16.48 / 24.40 at J = 1/2/3; R8 `FastRunnerN.lonely_of_fast_runner` [L] gives ρ7 ≤ 7ρ6 for every crosser. X24 exact: window A K6 has 3 windows, K'_7 empty in [1,7]; window B K'_6 has 5 windows (longest about 0.61 vs 2/ρ7 about 0.082), K'_7 has 10 windows, first starts at 65/ρ6 exactly = 26062497843590/2806730537001. `window_b_floor_v1.py` (+`.out`): J=1 tree 18,452 members (7,567 crossers), every 10th of J=2 27,137 (760 crossers): K'_7 non-empty in all [TESTED]; sufficient condition fails in 145 and 14 crossers (smallest ratio about 0.5685 at ρ7 about 7.0018), all with ρ7 between about 7.0 and 8.3; the 77 exact J=2 crossers with ρ7 > 9 have ratio ≥ about 1.53 [TESTED, one member per region]. Not derived; no Lean.

- E388: `window_b_failures_v1.py` (+`.out`), exact: the 159 base failures and 4,750 moved arrangements still gate crossers: K'_7 non-empty in all [TESTED, exact]. Opener of landing, base: reading 7 in 113 (laps 9: 95, 8: 10, 10: 8), reading 1 lap 1 in 37 (landing exactly R = 9), reading 5 in 7, reading 4 in 1, reading 2 in 1. Moved: reading 7 3,184; 1: 1,247; 5: 244; 4: 30; 2: 20; 6: 14; 3: 11. 3,622 of 4,750 still have no K'_6 window of length 2/ρ7. K'_7 empty needs every K'_6 window nested in a reading-7 zone: (8j_i − 1)/a_i < ρ7 < (8j_i + 1)/b_i. Verified, not derived.

- E389: statement S6: for six readings, N_A = {v in (r6, 7r6] : every window of K6 in [1,7] nested in a zone of v}, N_B the same for K'6 in [9,15]; S6: N_A ∩ N_B = ∅ for every six; would give landing ≤ 15 for every arrangement whose last reading is not fast. Runs `nesting_overlap_v1.py`, `nesting_random_six_v1.py`, `nesting_perturbed_six_v1.py` (+`.out`): first six of 7,567 J=1 crossers and 760 J=2: N_A ∩ N_B empty in all [TESTED, exact; one member per region]; 118,845 random sixes: N_A empty in all (uninformative); 30,268 perturbed sixes: N_A non-empty in 27,850, N_A ∩ N_B empty in all 27,850 [TESTED, exact]. Not derived; no Lean.

- E390: owner's challenge recorded; self-assessment: E382–E389's windows, N_A/N_B, S6 are constructs of the carving, "diagnostics, not the owner's route"; S6 is cap-shaped. `pinned_six_v1.py`, exact: X24 K6 in [1,7] has 3 windows (a single point at R = 1 with reading 6 at 7 − 2.5·10^-12; 3.571…–3.646; 5.232–5.287); K'6 in [9,15] has 5 windows (lengths about 0.286, 0.009, 0.245, 0.613, 0.334), first starting at 65/ρ6. N_B empty in all four sixes (X24 and three J=2 crossers); N_A pieces: X24 (8.983…, 9.0) and (24.36…, 24.4008…); J=2 sixes (16.4633, 16.4786), (16.4611, 16.4769), (7.0, 7.0044); every piece has v within 1 of a multiple of 8. Consequence [mine, in the owner's terms; not derived]: a gate crosser is a six leaving the AP's class instants as pinned points together with a reading 7 near a multiple of 8.

- E391: candidate table for X24, exact, owner's object candidate (a,k), a in {1,3,5,7}, c = (8j+1)/rho_a, j the lap of reading a nearest ideal instant a + 8k. Period 0: each of four candidates blocked by exactly one reading (7, 6, 7, 6). Period 1: a=3 (reading 3 lap 5, R = 39423938224285/3691147638604) has no reading in the slot, lonely; a=1 k=1 (R = 9) blocked by reading 5; a=5 k=1 by reading 4; a=7 k=1 by readings 1 and 5. Period 2: all four blocked by one to three readings. Not derived: that for every allowed arrangement some candidate is unblocked. One member only; no Lean. E382–E390 constructs withdrawn as a route (diagnostics only).

- E392: owner "Ok prove it": "no proof of n = 8 obtained in this entry". (1) isolation of each runner is the statement for every allowed reading set (`EndRunnerN.lonelyRunnerAt8_of_slowest` [L]); (2) independence cannot be the engine for whole numbers (`RealEightN` [L]; AP: four isolated points per period, zero slack, E306); (3) extension of case Z [P by hand, PROVISIONAL: counting tool, not yet tested numerically]: A a subset of m ≤ 6 with gcd g, B the rest, q_b = g/gcd(g,b); if Σ_{b in B} ⌈q_b/4⌉/q_b < 1 (every q_b ≥ 2) the set is lonely; (4) owed: sets with no such subset (the AP is one) and sets with sum ≥ 1.

- E393: shape (4,3) free-edge forward move: four multiples 8E_i, three non-multiples c_j; class a odd, direction d = ±1, τ* = least τ > 0 with cofactors E_i all ≥ 1/8 from integers, s* = τ*/8, t = a/8 + d s*; (H1) no non-multiple has (a c) mod 8 equal to 7 (d=+1) or 1 (d=−1); (H2) every non-multiple has r/8 + d c s* in [1/8, 7/8]; conclusion lonely at t; proof by hand. `shape43_freeedge_v1.py` (+`.out`): 56,160 sets of shape (4,3) with readings ≤ 48; H1 holds for some (a,d) in all; rule applies in 30,936, 0 misses [TESTED, exact; the proof is the check]; leftover 25,224 (24,840 least multiple 8, 384 with 16), all with largest non-multiple above the least multiple. `shape43_leftover_v1.py` (3,153 sets): landing's nearest class a = 1 in all, backward 2,988, forward 165; cofactor window index used 0: 104, 1: 60, 2: 41, 3: 98, 4: 216, 5: 806, 6: 240, 7: 1,588. No Lean.

- E394: assembly of pieces: `RealEightN`, `EndRunnerN`; ≤ six readings order seven; spread ≤ 7 R1; (7,9] `band_lonely`; R8; §17C fields; gate L1 [P by hand]; 1-D fact [P by hand]. Second (4,3) condition (cofactor window longer than Σ 1/c_j) [PROVISIONAL: counting tool] holds in none of the 25,224 leftover sets (`shape43_two_regimes_v1.py`; cofactor windows 3/256 long). Window B for ρ7 ≥ 9: a K'_6 window of length ≥ 2/9 suffices; on the 77 J=2 crossing members with ρ7 > 9 the longest K'_6 window ≥ about 0.3268 (smallest 0.32676…) [TESTED, exact members, one per region]. Lemmas stated: (L-B1) every gate-crossing six has a K'_6 window ≥ 2/9 [tested on 77]; (L-B2) ρ7 in (ρ6, 9): K'_7 non-empty for every crosser (tested on 7,567 + 760); (L-B3) ρ7 > 7ρ6: R8 [L]. No Lean. Not derived.

- E395: parity law [P by hand; exact check A = 0..23, k = 0..15, 0 failures]: a walker with ratio exactly A + 1/2 is in the way at every even k iff A mod 8 in {0,7}, at every odd k iff A mod 8 in {3,4}, at no other k. Step 1 [OBS, existing outputs]: the 21 hand-offs of E235/E243 (`hole6_shadow_v2.out`) at flank ranks 1 (13), 2 (6), 3 (1), 4 (1); 50 shadowed flanks in `hole6_shadow_v1.out`: ranks 1: 12, 2: 19, 3: 7, 4: 8, 5: 2, 6: 2. Step 2 [derived, conditional on (C)]; step 3 parts with status. Lemma (C) not in hand: a run of N consecutive openings covered by the union of at most five walkers is covered by a single near-sharer or by an exact half-pair. No proof of n = 8; no Lean.

- E396: `RULES_n8_v4.md`: rule 7 relaxed for the moment (counting steps need [PROVISIONAL: counting tool]; covering statements permitted with [PROVISIONAL: covering]). Lean `LonelyRunner/LRC/Spec/HalfPairParityN.lean` (uncommitted; build exit 0, 2,413 jobs): `circDist_div16_lt`, `parity_law`, `circDist_lt_iff_of_mem`, `near_sharer_blocked_iff` (walker ratio 8a + 1 + ε, ε < 0, opening u with 0 < u ≤ 8/|ε|, in the way iff u < 2/|ε|); axioms `[propext, Classical.choice, Quot.sound]`, no `sorry` [L]. Not a proof of n = 8; (C) [PROVISIONAL: covering] not derived.

- E397: reformulation [P by hand; exact]: flank e dead iff every opening k ≥ 0 has a walker in the way ((8k+1)x_j mod 8e outside [e, 7e]); walker j with g = gcd(x_j, e), q = e/g, p = x_j/g blocks at most ⌈q/4⌉ classes mod q [PROVISIONAL: counting tool]; a flank is dead iff its walkers' class sets cover Z/e [PROVISIONAL: covering]. `dead_flank_types_v1.py` (+`.out`): 7-subsets of [1,20] gcd 1 (77,400): dead flanks per set 0: 28,583; 1: 28,314; 2: 15,305; 3: 4,500; 4: 657; 5: 40; 6: 1; 7: 0 [TESTED]; 2,470 distinct minimal-cover types; most frequent one walker q = 1, p ≡ 0 mod 8: 25,648; half-pairs (1,7), (1,1), (7,7): 7,805, 5,985, 1,820. Over [1,24] (345,304 sets): dead flanks by rank 121,072; 102,635; 44,330; 19,589; 8,397; 3,900; 1,404; {2,3,4,5,6,7,16} the only set with six dead flanks (survivor d_max); no set has seven dead [TESTED]; d_max dead in 1,404 sets. No proof; no Lean.

- E398: `dead_flank_pairs_v1.py` (+`.out`), 7-subsets of [1,20]: 281,380 walker occurrences; walker's own flank dead in 39,882; mutual dead pair in 11,623 [TESTED]; by type (2,1) 35,104/5,440; (1,0) 25,648/1,075; (2,7) 15,085/631; (3,2) 13,635/4,154; (3,0) 12,298/639; (4,1) 11,952/2,333; (3,1) 11,117/6,720; (4,3) 10,294/286. 41 sets with ≥ five dead flanks (40 with five, {2,3,4,5,6,7,16} with six) [TESTED]. Six-dead set: flank 16 has clear openings k = 1 and k = 14 of 16; k = 1 clear because 9x/16 ∈ [9/8, 63/16] for x in [2,7] [P by hand, exact arithmetic], the first-lap clearance of MANUSCRIPT_v22 §15 / mirror of Theorem 4.8. Consequence [PROVISIONAL: covering]: case shape on the d_max flank. No proof; no Lean.

- E399: read of `MANUSCRIPT_v22.md` §4.5, §6.9 and listed Lean files: (1) §6.9 states the covering wall (each runner blocks 2b − 1 of 8b residues; 6 × 1/4 > 1); proved there Theorems 6.8, 6.9, Prop 6.10 (a)(b), 6.13, 6.14, U/K calculus with 4,413 pinned census families and 62 one-parameter families in Lean (`decide`), eighth family for every real x in (0,8); open there: shadowing triples ((2,4,4), (3,3,3), (3,6,6), (5,5,5) found; (2,5,c) passes the residue count for every c). (2) L1(d) in Lean under a separation hypothesis: `FirstGateN.forced_nearest_move`, `crossing_iff_visits_nine`, `crossing_forces_nearest_setter`, `terminal_gate_equivalences`; without it only L1(a)–(c). (3) `CoreWindowRunN`. (4) `IntegerGridN`, `IntegerDisplacementN` (`inWay_at_grid_iff`, `lonely_of_displacement`, `move_at_grid`, `lonely8_example`). (5) `GrandReturnN`. No grade tag other than those.

- E400: residual case list at the eight shifts t = (τ + k)/8. Lean `LonelyRunner/LRC/Spec/ParityDescentN.lean` (uncommitted; exit 0, 8,338 jobs; 25 theorems axiom-clean, `experiments/nN/parity_descent_print_axioms_v3.out`) [L]: `lonely_eight_of_residual_four_multiples` (every `EightResidual` set with four multiples of 8 lonely at 1/8: shape (4,3) settled), `lonely_eight_of_three_multiples_three_odd`, `lonely_eight_of_residual_no_two_mod_four`, `lonely_eight_of_silent_four` (settles (3,4) (f,o,o,t)), `lonely_parity_descent_iff`, `paritySplit_of_cost`, `lonely_eight_of_parity_descent`, `two_le_odd_of_residual`, `exists_free_shift`, `exists_quarter_shift`, `silent_of_quarter`. Counting steps [PROVISIONAL: counting tool]. Map run (`shift_cover_types_v1.py`, `shift_cover_drop_v1.py`) [PROVISIONAL: covering; P by hand; enumeration exhaustive]: (4,3) 10 of 10 settled; (3,4) 155 patterns, 82 settled, 73 left, 20 (f,o,o,t) then settled, left (o,o,o,o) 35 and (o,o,t,t) 18; (2,5) 381, 30 settled, 351 left; (1,6) 812, 30 settled, 782 left. `mixed_threshold_v1.py`: M(2,2), M(1,3) exhaustive to 24 [T 18,216/18,216; T 5,280/5,280]. `shift_cover_drop_check_v1.py` on 2,056,220 sets: [T 34,528/34,528], [T 35,360/35,360]. `members_reach_check_v1.py`: `residual_members_C_list_v1.json` 547 of 547 in `EightResidual`, settled 81 (53, 28); `both_shadowed_members_v1.json` 287 of 287, settled 47 (33, 14); [T 128/128]; `members_5978_v1.json` loaded 0 sets. E393 re-read: its 30,936 sets are closed by `no_small_resolution` [P by hand]; its first leftover example {1,2,8,16,24,28,32} is lonely at 1/5 (R6).

- E401: cost-exactly-8 patterns of (3,4): non-multiples block all eight shifts only as a perfect partition [PROVISIONAL: counting tool; PROVISIONAL: covering]. `landing_opener_tight_v1.py` (+`.out`), 43 stored members: (o,o,o,o): opener odd 14 (sizes (1,2,2,2)), opener a multiple of 8 10 ((2,2,2,2) overlapping); (o,o,t,t): opener ≡ 2 mod 4 8 ((0,2,2,2)), odd 4, multiple of 8 7. Derivation check [T 26/26]. Open content = `PARITY_MECHANISM_v1` §5's remaining step (2026-09-07, `[OPEN]`); "no new route".

- E402: Lean [L], two new uncommitted files: `ParityDescentTwoN.lean` (exit 0, 8,339 jobs; 8 theorems: `exists_mixed_le_three`, `exists_mixed_three_one`, `quarter_silent`, `lonely_eight_of_quarter_silent`, `lonely_eight_of_eighth_silent`, `quot_pos`, `lonely_eight_of_quarter_three_one`, `lonely_eight_of_eighth_le_three`; `parity_descent_two_print_axioms_v1.out`) and `ParityCoverN.lean` (exit 0, 8,340 jobs; 10 theorems: `eight_dvd_sq_sub_one`, `odd_blocked_rel`, `odd_container`, `two_mod_four_rel`, `two_mod_four_container`, `oott_core_fin`, `oott_core`, `free_shift_oott`, `lonely_eight_of_eighth_free`, `lonely_eight_of_oott`; `parity_cover_print_axioms_v1.out`). Reach (`lean_case_reach_v1.py`): (4,3) 10 of 10; (3,4) 102 of 155; (2,5) 82 of 381; (1,6) 82 of 812; stored members 192 of 547 and 105 of 287; with M(2,2), M(1,3) (not proved): (2,5) 162, (1,6) 242. What is left listed by type (see section 6).

- E403: grid argument for tight (3,4): reduction points (odd w blocks exactly one shift at τ = m/w; 2v blocks none at τ = (2m+1)/(2v)); grid lemma (odd w, three positive integers c none divisible by w ⇒ some m in [1, w−1] with ‖c·m/w‖ ≥ 1/8 for all three) [PROVISIONAL: counting tool]. Hence a (3,4) set of type (o,o,o,o) or (o,o,t,t) is lonely unless every odd non-multiple divides some cofactor and, for (o,o,t,t), the cofactors also block every reduction point of the two readings ≡ 2 mod 4. Checks: `grid_cover_cofactors_v1.py` [T 49/49 values of w in [3,99]]; `grid_lemma_check_v1.py` on 7-subsets of [1,48] ((o,o,o,o) 212,520; (o,o,t,t) 364,320) [T 574,662/574,662]; `_v2` [T 576,818/576,818], 22 sets remain all (o,o,t,t); `_v3`: in all 22 every odd non-multiple divides a cofactor; in 4 the reading 10 divides no cofactor and cofactors {1,2,3}, {1,3,4} or {1,3,6} block all five points (2m+1)/10 [T 4 sets]; landings between 17/256 and 9/64; `tight34_members_v1.py` [T 59/59].

- E404: M(2,2) proved by hand, delegated [P, delegated], counting steps tagged [PROVISIONAL: counting tool]; M(1,3): cases a, b, c, e, f [P, delegated]; class R has no proof. `mixed_lemma_check_v1.py` (+`.out`), values in [1,40]: M(2,2) 148,200 of 148,200; M(1,3) 45,600 of 45,600; firing control: 39 failures each for M(1,4) and M(2,3) on [1,24] (first c = 4, u = (1,3,5,9)); constructed τ [T 148,200/148,200], [T 45,566/45,566]; class R 34 cases at c = 4 (10), 8 (10), 12 (10), 16 (4). Reach (`lean_case_reach_v2.py`): (2,5) 82, 162, 162 of 381; (1,6) 82, 142, 242 of 812; members C_list: Lean 192, M(2,2) +80, M(1,3) +20, open 255 of 547; both_shadowed: 105, 54, 8, open 120 of 287.

- E405: Lean [L] `LonelyRunner/LRC/Spec/ParityGridN.lean` (uncommitted; exit 0, 8,341 jobs; 12 theorems axiom-clean, `parity_grid_print_axioms_v1.out`): `nearEdge_mul_iff`, `card_nearEdge_le`, `clear_of_not_gridNear`, `zero_mem_gridBad`, `three_mul_card_gridBad_le`, `grid_point_Ico`, `grid_point`, `eight_dvd_of_blocked_at_grid`, `odd_blocked_le_one_at_grid`, `card_blocked_le_two_of_not_four`, `lonely_eight_of_free_at`, `lonely_eight_of_grid` (≤ three multiples of 8, ≤ four non-multiples none divisible by 4, an odd non-multiple w dividing no cofactor ⇒ lonely at 1/8) [L, and still PROVISIONAL: counting tool under rule 7]. Derived [P]: in the divisible family of type (o,o,o,o) the opener is always a multiple of 8. `divisible_members_v1.py` (+`.out`): construction A 6,732,680 tried, 43 residual members (opener the divided multiple 23, another multiple 20); B 8,109,293 tried, 380 members (ratio < 9 in 238; [9,26) 104; ≥ 26 38); opener a non-multiple in 0 of 423; opener the divided multiple in 309 of 423.

- E406: Lean [L] `LonelyRunner/LRC/Spec/ParityMixedTwoTwoN.lean` (uncommitted; exit 0, 8,340 jobs; 45 theorems axiom-clean, `parity_mixed_two_two_print_axioms_v1.out`): `exists_mixed_two_two`, `lonely_eight_of_quarter_two_two`, `lonely_eight_of_eighth_two_two`; M(2,2) moves from [P, delegated] to [L], counting steps stay [PROVISIONAL: counting tool]. Reach (`lean_case_reach_v3.py`): (4,3) 10 of 10, (3,4) 102 of 155, (2,5) 162 of 381, (1,6) 142 of 812 (242 with M(1,3), conditional). Stored members: C_list 547: residue cases 272, grid corollary 27, M(1,3) only 20, open 228; both_shadowed 287: 159, 16, 8, open 104; no member of shape (3,4) or (4,3) open; every open member has shape (1,6) or (2,5).

- E407: descent by any modulus q at threshold 1/8: a reading e blocks at most g·⌈q/(4g)⌉ of the q shifts σ + k/q, g = gcd(e,q) [PROVISIONAL: counting tool]; if at most six readings are divisible by q and the others' bounds sum below q, some shift is lonely. `descent_q_bound_check_v1.py`: q in [3,40], 0 violations, attained in 117 (q,g) classes [T]. Lean [L] `LonelyRunner/LRC/Spec/DescentModQN.lean` (uncommitted; exit 0, 8,338 jobs; 7 theorems, `descent_mod_q_print_axioms_v1.out`): `four_mul_sub_lt_of_near`, `card_grid_near_le`, `circDist_shift_eq_mod`, `ceil_quarter_le`, `quotient_pos`, `card_blocked_mod_le`, `lonely_eight_of_descent_mod`; uses order seven (`LRC.OrderSevenN.lonely_seven_nat`) via `lonely_eight_of_card_le_six`. Reach (`descent_mod_q_reach_v1.py`, q over [3,199], q ≠ 8): C_list 547: applies to 190 (71 with no [L] case), 0 failures; both_shadowed 287: 77 (31), 0 failures; `divisible_members_v2.json`: all 41 (A) and 371 (B), 0 failures; least q: 3 (125 members), 4 (61), 5 (15), 7 (39), 27 members at 13 other q between 10 and 41. `divisible_members_v2.py`: A 6,000,000 draws seed 1: 41 members; B 8,000,000 seed 2: 371 members, ratio < 9 in 234. `divided_flank_v1.py`: divided-flank progression [T 412/412] [PROVISIONAL: counting tool]. `left_after_rules_v1.py`: C_list 162 left, both_shadowed 75; in all 237 s1/s0 ≥ 9 (> 13 in C_list, > 25 in both_shadowed); slowest reading a multiple of 8 in 98 of 162 and 75 of 75; cascade lands at R* = 8·s0·t* < 2 in every one; opener a non-multiple in 138 and 59.

- E408: axiom records re-run: `parity_descent_two_print_axioms_v2.out`, `parity_cover_print_axioms_v2.out`; all 18 theorems `[propext, Classical.choice, Quot.sound]` except `oott_core_fin`, `oott_core` (`[propext, Quot.sound]`); E402 grades stand. `m13_class_R_v1.py`: c in [1,48], odd u in [1,79]: 474,240 cases; class R 170 (c = 4: 24, 8: 22, 12: 30, 16: 22, 20: 14, 24: 22, 28: 16, 32: 12, 36: 8); largest u3 79 (range edge); exhaustive decision finds τ in every class-R case [T 170/170]; class R "not shown to be finite". Two background tasks launched (`brief_modgap_v1`, owner's idea "an interaction between mod speeds, mod gaps"; `brief_m13_R_v1`).

- E409: M(1,3) by hand [P, delegated]; cases a (4 ∤ c: τ = 1/4), S (b_hi − b_lo ≤ 2c: τ0 = 1/(8c)), T (G ∤ m: τ0 = k/(4G)), Φ (N = 3, n = m/G = 1), P (rest, N ≥ 4: τ0 = k/(4GN)); split exhaustive; order four not used; Lemma QP and choice of j [PROVISIONAL: counting tool]. `m13_proof_v1.py` (+`.out`): Range A 474,240 cases (a 355,680, S 32,708, T 20,810, Φ 492, P 64,550); Range B (c ≤ 128, odd u ≤ 159) 10,516,480; Φ b-sets 160,200; u near 999,001 705,600; [T 11,856,520/11,856,520]; the 170 class-R cases all fall in Φ; reduction agrees at 183,872 points; firing control rejects in all 116,534 cases. (1,6) reaches 242 of 812; members gain 20 and 8. M(4,0) order five; M(3,1) [L]; M(2,2) [L]; M(1,3) [P, delegated]; M(0,4) τ = 1/4 [P, one line].

- E410: Lean [L] `LonelyRunner/LRC/Spec/BystanderN.lean` (untracked; exit 0, 2,553 jobs; 18 theorems, `modgap_bystander_print_axioms_v5.out`): `firstLonely_cons_iff`, `bystander_iff`, `clear_iff_residue`, `lonelyList_cons_iff`, `lonelyList_of_cons`, `takeover`, `takeover_of_lonely_at`, `lonely_at_of_firstLonely_cons`, `lonelyList_add_nat`, `exists_lonely_fract`, `exists_clear_in_interval`, `clear_in_interval_iff`, `lonelyList_seven_to_eight`, `clear_seven_at_inv`, `exists_dvd_of_no_lonely_seven`, `clear_seven_at_eighth`, `exists_residue_of_no_lonely_seven`, `no_long_interval_of_no_lonely_seven`. Checks (`modgap_*`): map M1–M7, P1–P7 on 7-subsets of [1,14] up to [T 11,339,328/11,339,328]; takeover [T 4,979/4,979], [T 6,210/6,210 and 6,023/6,023], [T 489/489], [T 1,807/1,807, all 6,677 members]; (3,oooo) family 25, 92, 149, 168, 101 members at K = 2, 6, 12, 18, 24, at most 4 switches, 7 moves, 9 re-blocks [OBS]; scale control [T 149/149]. (6,1) statement: at the first 1/7-component of S∖d some d clear in 547/547 (C), 287/287 (BS), 41/41 (DA), 371/371 (DB), 1,497/1,500 (T1), 28/28 hard, 1,435/1,436 `hard_sets_41_60.json`; rule B 546/547, 287/287, 41/41, 371/371, 1,489/1,500; rule D 547/547, 287/287, 41/41, 371/371, 1,496/1,500; argmin t_d 0 of 547 and 0 of 1,500; the tight sets (AP 1..7, (1,2,3,4,5,7,12)) have no good d. `modgap_shell_v1`: all 4,210 residual or hard sets walked are lonely at 1/7. Sets with no lonely instant at 1/7: 24 of 346,104 seven-subsets of [1,24]; 30 of 851,760 with d_min ∈ {1,2} of [1,30]; δ values 1/8, 2/15, 3/23, 3/22, 4/29, 5/37, 5/36; (1,2,3,4,5,6,7k) has none for k = 1..8 and 10 with δ = k/(7k+1); none of the 31 distinct sets is in `EightResidual`. `modgap_adversary_v1`: 217,980 sets, no `EightResidual` set. Grid handle [P]: forced conditions implied by `EightResidual`'s field "q divides some reading for q = 5,6,7,8"; least denominator of the first 1/7 component above 1,000 for every stored full-residual member. `modgap_r7_v1`: R₇(d) criterion certifies 28/28, 1,429/1,436, 531/547, 287/287, 41/41, 371/371, 1,457/1,500, 19,794/20,000 (control). Restated target "every `EightResidual` set is lonely at 1/7" [OBS] on 4,210 sets (F17).

- E411: Run 1 (`modgap_v1res_v1.py`, `_v2.py`): v1-residual gcd-1 sets by TOP: 30: 12,307 (12,305 lonely at 1/7); 40: 91,503 (91,501); 48: 382,658 (382,656); 56: 1,249,508 (1,249,506); 64: 3,722,833 (3,722,831); the two not lonely at every window: (1,3,4,5,7,11,24) and (1,4,5,6,7,11,16), δ = 2/15, neither in the full residual (22 fields) [T]. Run 2 (`modgap_f7_enum_v1.py`): [1,40] 49 sets with no 1/7-lonely instant (27 primitive); [1,52] 67 (30 primitive); twelve cores, identical on the two windows, each with listed seventh readings; every δ ≥ 1/8 [OBS on [1,52]]. Run 3: r-dependent block split [P by hand, not in Lean] applies to 0 of all stored sets (`modgap_split_refined_v1.out`).

- E412: slack bounds [P; PROVISIONAL: counting tool / covering]: no lonely instant at 1/7 forces d₆ < 21 d₅ and d₅ < (105/2) d₄; weaker than `EightResidual`'s d₆ < 9 d₅ and d₇ ≤ 7 d₆, so they do not reach the residual. First-component statement (`modgap_nogood_v1/v2.out`): no good d at the first component in 0, 0, 0, 0, 8, 0, 1 sets (C 547, BS 287, DA 41, DB 371, T1 5,431, 28 hard, 1,436); no good d within the first two components in 0 of all 8,141 [T]. All 9 exceptions have d_min ≡ 0 (mod 8). `modgap_dmin_perturb_v1.out`: the 8 large exceptions keep failing for every j; 113 of 126 variants with d_min' not ≡ 0 fail, 32 of 33 with ≡ 0; small exception (8,18,25,34,42,51,59) fails only at j = −1; control 0 of 14,400; the correlate does not account for the failures [T]. Shape (`modgap_exc_exact_v2.out`): 8 large have 26·d_min < d₂, d₇ < 7·d₂ in all 9, 1049/1000 < R₇ < 146/100 for the 8 large; small one ρ₂ = 9/4, R₇ = 32/9. [OBS, F17].

- E413: Lean [L] additions to `BystanderN.lean` (21 theorems, `modgap_bystander_print_axioms_v6.out`): `circDist_ge_of_band`, `clear_on_first_arc`, `lonely_cons_of_arc`. Statement [P, Lean-stated]: if the six readings C have a lonely component at 1/7 inside the first clear arc u in [1,6] of m = d_min then S is lonely at 1/7. Worked case (`modgap_cluster_v1.py`, `_v2.py`): 9 exceptions, gcd(C) = 1 in all; cluster components in u in [0,8]: 44, 471, 401, 108, 108, 100, 123, 48, 3, of which 26, 288, 252, 66, 67, 63, 79, 32, 1 inside the arc; S's 1/7 landing = left end of the first component inside the arc [T 9/9]. `modgap_gap_cluster_v1.out`: random clusters largest gap below 22/5 periods; multiples: 2622/847; AP-like clusters c₁ + i k gaps up to 746556000/37100749 periods (> 130/7): a gap bound depending only on the spread does not hold [PROVISIONAL: covering].

- E414: `modgap_aplike_v1/v2`: nearly equal clusters against residual fields: grid 14,400 sets, 0 pass every field (first failing field: free flank 8,380; common factor 3,114; q = 5,6,7,8 1,163; first lap / minus seven 1,008; rational openings N = 6,7,9 355; N dividing 8,3,5 312; small resolution D ≤ 64 68); random 120,000: passing in order 99,920; 30,930; 30,440; 7,956; 6,596; 595; 21; 0 [T over 134,400 sets; a random sample]. Arc criterion (`modgap_threshold_v1/v2/v3`): ρ in [26,200] step 1/2: 0 failing grid points in all 805 clusters; ρ in [2,26] step 1/4: 215 clusters, fails in 70, all at ρ = 2 only [T on the grid]. [OBS, F17].

- E415: arc criterion A(S) over 7-subsets (`modgap_arc_enum_v1.py`, `_v2.py`): [1,30] 2,029,245 sets, A false in 82 (23 with no 1/7 instant), greatest ρ₂ 17/4; [1,36] 8,315,063, false 280 (25), greatest 19/4, by d_min 1: 23, 2: 2, 3: 6, 4: 79, 5: 170; [1,44] 38,146,585, false 1,566 (28), greatest 24/5. `modgap_arc_threshold_v1.py`: d₂ ≥ 5m: 0 false in 1,666,461 sets (m = 5..12); d₂ = 5m − 1: 1,077,804 sets, false in 12, all lonely at 1/7 with u between 25/4 and 27/4. Observed, not derived. Proof routes stated, nothing proved.

- E416: adversarial search over real ratios (`modgap_real_adv_v1/v2/v3.py`): exact counterexamples to the arc criterion at ρ_min = 5 (landing u = 3175020/525941 with ρ = (5, 1412741/261840, 525941/88195, 5575838/821095, 189353/24304, 7946201/940370); and u = 1960260/321793) and ρ_min = 6 (u = 38869463/6239959); none found for ρ_min in {7,8,9,10,12,14,16,20} [OBS, F17].

- E417: Hunter–Worsley and third-order Bonferroni truncations for |∪ B_i| < 5: under independence S₁ = 60/7, S₂ = 300/49, S₃ = 800/343; HW bound 320/49 > 5 [P, exact arithmetic]; third-order 1640/343 (below 5 by 75/343) [P]; true union 510120/117649. `modgap_bonferroni_v1.py`: HW below 5 in 5, 8, 5, 5 of 150 clusters at ρ_min = 7, 10, 20, 50; third-order in 125, 135, 134, 138; true union below 5 in every sampled cluster [T over the 600 sampled clusters]. Truncations not sufficient as a uniform route [OBS, F17].

- E418: `modgap_real_adv_v5.py` (interval objective): exact counterexamples at every r = k/10, k = 60..71 (r = 7: ρ = (7, 294485/39188, 55586/6759, 826374/87595, 159527/14711, 809015/68981), landing u = 43/7; r = 71/10: minimum 501453/70615, landing 3036445/501453); none found for k = 72..90 [OBS, F17: one continuation path, seeded, not exhaustive].

- E419: unlogged runs read: `modgap_chain_types_v1` (24 to 28 moves; setters begin 0,5,4,3,2,1,0 for r ≥ 61/10) [OBS, F17]; `modgap_cell_lp_v1/v2/v3` (sup of ρ_min over the r = 71/10 type's cell 43/6, certified exactly); `modgap_tree_v1` window [6,12]: 35,936 nodes, 222 FAIL cells; [43/6,12]: 5,347 nodes, 1 FAIL cell, witness landing 298645/49716. `modgap_type_edge_v1.py`: sup of ρ_min over that cell is 20625/2873 [exact: dual bound and primal point], binding 13ρ_4 ≤ 15ρ_3, 13ρ_3 ≤ 15ρ_2, 34ρ_0 ≤ 22ρ_4, 6ρ_2 ≤ 50; point ρ = (20625/2873, 6355/832, 25/3, 125/13, 1875/169, 155/13), where the cascade lands at 169/125 (supremum not attained). [P, one line]: first state above 6 lies in (6,8), d_min in the way; [T 12/12]: the move from there is set by d_min and lands at u = 8; landing in d_min's second arc [8,13], at most 6419891/699039. F7: for ρ_min ≥ 9 the arc criterion is E246's W6(7) for `ArrBlockRule8 6 9` at threshold 1/7. Interval check recorded: the arc is d_min's first window (register v3 item 15, MISPLACED as a requirement).

- E420: float trees finished [TREE, float pruning]: windows R0 ≤ ρᵢ ≤ 16, R0 = 36/5, 15/2, 39/5, 8: 191,635, 175,331, 165,999, 157,199 nodes, 0 FAIL, 0 cut; slab: 36,714 nodes, 1 FAIL cell (sup 20625/2873); [6,12]: 222 FAIL cells, largest bound 20625/2873, primal attains in 158. Exact-certificate tree `modgap_tree_exact_v1.py` (Motzkin certificates) [TREE, every prune an exact certificate]: [43/6,12] 5,347 nodes, 1 FAIL (witness landing 204875/34116), 123,753 prunes, 224,258 certificates; window 36/5 ≤ ρᵢ ≤ 16: 191,635 nodes, 5,302,440 prunes, 8,841,004 certificates, no FAIL cell; slab: 36,714 nodes, 805,201 prunes, 1,483,564 certificates, 1 FAIL cell, sup 20625/2873. Two-arc statement on [6,12] (`modgap_tree_exact_v2.py`, ARCS = 2, `_a2_w6_12.out`): 41,108 nodes, 1,237,800 prunes, 2,092,681 certificates, no FAIL cell. Running: window to 20 (4,110 of 12,935 tasks, 0 FAIL). Integer populations (`modgap_arc_members_v1`, `modgap_arc_index_v1`): A holds on C 547/547, BS 287/287, DA 41/41, DB 371/371, T1 5,431/5,431, hard 1,436/1,436 [T]; E415's 1,566 A-failures: 0 in the full residual, 10 in the v1 residual; 1,538 land in d_min's second arc u ∈ [8,13] [T 1,538/1,538]. "Rule 13 is not met."

- E421: owner redirect (relayed): the mod-speeds / mod-gaps line stopped; state of every run recorded. Exact [TREE] results as in E420, each tagged [PROVISIONAL: covering]; window 36/5 to 20 stopped at 5,460 of 12,935 tasks after 28,838 s (0 FAIL at that point; "No result is claimed for that window"); `modgap_arc_members_v1.out` [T 547/547, 287/287, 41/41, 371/371, 5,431/5,431, 1,436/1,436]; `modgap_arc_index_v1.out` [T 1,538/1,538]; `BystanderN.lean` untracked, 21 theorems axiom-clean (`modgap_bystander_print_axioms_v7.out`); `brief_prior_arc_v1` result not in hand.

- E422: `block_three_check_v1.py` (core of four against a block of three at ratio 26; 3,000 sets, seed 410): [T 3000/3000] [PROVISIONAL: counting tool and covering]; superseded by E231 (core of four below a block of three with x₁ ≥ (35/3)·m is lonely, from `SplitChainN.lonely_of_split` with `lonely_five_nat`; E231's grade [derived from proved lemmas; no Lean instance built]), leaving the strip 9m ≤ x₁ < 35m/3 open. Versioning repair: v1 restored, corrected copy `block_three_check_v2.py`. "Consequence: none for the proof."

- E423: Lean [L] `LonelyRunner/LRC/Spec/ResidueCasesN.lean` (uncommitted; exit 0, 8,342 jobs; 20 theorems, `residue_cases_print_axioms_v1.out`): `paritySplit8_iff_counts`, `paritySplit8_nonmult_iff`, `paritySplit8_rest_iff`, `oottCase8_iff_counts`, `lonely_eight_of_settled_counts`, `lonely_eight_or_open_counts`, `lonely_eight_or_open_counts_five`, `crowded_counts_m4`…`_m1` (`decide +kernel`): settled 10 of 10 (m = 4), 102 of 155 (m = 3), 162 of 381 (m = 2), 142 of 812 (m = 1). Lower-order inputs: T1, T2 order seven; T3 `existenceAtN_four`; T4–T6 order four; T7, T8 only in M(2,2)'s small branch. No theorem tying a set S to its residue pattern in the file.

- E424: Lean [L] `LonelyRunner/LRC/Spec/ParityMixedOneThreeN.lean` (uncommitted; exit 0, 8,341 jobs; 19 theorems, `parity_mixed_one_three_print_axioms_v1.out`): `exists_mixed_one_three`, `lonely_eight_of_quarter_one_three`, `lonely_eight_of_eighth_one_three`, `part_a`, `part_S`, `part_T`, `part_Phi`, `part_P`, `qp_arc`, `qp_third`, `p_choice`. M(1,3) moves from [P, delegated] to [L]; counting steps stay [PROVISIONAL: counting tool]. (1,6) 242 of 812 read on residues.

- E425: Lean [L] `LonelyRunner/LRC/Spec/ResidueCasesTwoN.lean` (uncommitted; exit 0, 8,344 jobs; 7 theorems, `residue_cases_two_print_axioms_v1.out`): definition `SettledCounts8'` (adds T9, T10), `lonely_eight_of_settled_counts'`, `lonely_eight_or_open_counts'`, `lonely_eight_or_residual_open` (positive readings, at most seven, no common factor g ≥ 2: lonely at 1/8, or in `EightResidual` with `¬ SettledCounts8'` and T6 failing), `crowded_counts_one_three_m4`…`_m1`: 10 of 10, 102 of 155, 162 of 381, 242 of 812. Lower-order inputs read mechanically (`residue_cases_two_lower_order_v1.out`): T9, T10 none; T1, T2 `lonely_seven_nat` only; T3–T8 `existenceAtN_four` only; `lonely_eight_or_residual` uses `existenceAtN_four`, `lonely_five_nat`, `lonely_seven_nat` and 3,666 `LRC.OrderSixN` constants. Open patterns: 53 of 155 (m = 3), 219 of 381 (m = 2), 570 of 812 (m = 1).

- E426: (1) cap routes marked by owner ruling: `Cover8 M` (`RegimeSkeletonN.lean:71`), `WideStep8 M` (`BandRouteN.lean:92`), `WindowBound` (`PathWindowN.lean:32`); retained, not the path; path of record `lonelyRunnerAt8_iff_residual` [L]. (2) open step restated natively; "the zones do not cover" dropped as the form of the open step; the arc criterion is not the open step. (3) Lean target `LonelyRunnerAt8` (`Spec/Target.lean:401`) is pointwise, no measure; 106 Prop definitions read (`experiments/n8/lean_density_audit_v1.py`), none of the owed ones a density statement; n=8 import closure 96 modules, contains none of `Theorem52_Weyl`, `Lemma41_PositiveMeasure`, `Theorem121_Main`; `Defs.lean` carries `goodSet_measurable` [L]. (4) tally of `modgap_type_edge_v1_w6_12.json` agrees with E420. (5) `Classical.choice`: `experiments/n8/Openings_v1.lean` (`Openings.lcm_div_eq`, `[propext, Quot.sound]`); probes `ChoiceProbe_v1.lean`, `_v2.lean`: real statements carry `Classical.choice` through `Real.decidableLT`/`decidableLE`; a ℕ certificate by `decide` depends on no axioms.

- E427: grid plus deviation on every 7-subset of [1,24] with gcd 1 (345,304 sets), scripts `grid_deviation_landing_v1`, `grid_deviation_chain_v1`/`_v2`, `_chain_rank_v1`, `_chain_split_v1`, `_chain_zero_v1`/`_v2` (`experiments/n8/`): start blockers are exactly slot 0, or slot 7 with ε > 0 [T 0/345,304]; 200,194 sets do not move, 145,110 move, longest run 19 moves [OBS]; opener of the landing a start blocker in 59,829, clear at the start in 85,281 [OBS]; of those 85,281: first setter a start blocker in all (slot 0: 55,198; slot 7: 30,083), lengths 2 to 19, 42,780 of length 2, 1,534 signatures; D8 67,522 yes, 17,759 no; D0 21,958; D8 vs rank fall F agree 50,020, disagree 35,261 (wrap only 17,043, zero-convention only 9,547, tie only 7,359, wrap and zero 1,312); transitions sweep 92,779, bridge down 19,608, bridge up 46,717 [OBS]. Record read: manifests over 599 `.md` files by 42 agents. "No new theorem."

- E428: new folder `Math Ex/LonelyRunnerFresh/` (`Fresh/Framework.lean`, `check.sh`, `lean-toolchain`); 20 Prop defs (15 DEFINITION, 5 OWED: `GridGlobalIsolation`, `LonelyRunnerEight`, `DisplacementPath`, `CascadeForm`, `CandidateScaleForm`) [T 0/20 untagged]; theorem `lonelyRunnerEight_imp_displacementPath` [L]. Audit table of open propositions with verdicts (my reading, not owner rulings): `ArrBlockRule8 f T`, `ArrBoundedCovered8 T` undecided; `CaseB8`, `CaseC8` off the path; `Cover8 M`, `WideStep8 M`, `WindowBound`, `OrderFive.RCapped` imported (cap); `OrderFive.WindowConstantFive` off the path; `DoorFirstLap`, `DoorLargestFlank` refuted; `LonelyRunnerAt8`, `ExistenceOnArrangements` target. [OBS, reasoned].

- E429: `LonelyRunnerFresh/` eight modules, 2,669 lines, `./check.sh` exit 0, 148 `#print axioms` lines (146 `[propext, choice, Quot.sound]`) [L]. `PathForm.displacementPath_iff`, `Cascade.cascadeForm_iff`, `cascadeFixes_iff_isolation`, `Localisation.candidateScaleForm_iff`: each ↔ `LonelyRunnerEight` (restatements). `Localisation.lonely_ge_bound`, `certificate_iff`; `Grid.gridGlobalIsolation`, `deviation_iff`, `ap_globalIsolation_iff`, `octagon` (one step [PROVISIONAL: counting tool]); `Dilation` (t'/t < 9/7 when the setter's lap ≥ 1; shift gap·d/x with 0 < gap < 2; link rule L6); `WhereProofs` (ten claims incl. start blockers for all arrangements, `FirstMoveIsLargestStartOpening`, `enteringEdge_anyMove`, `landingIsFirstIsolation`, `cascadeFindsIsolation`). Counterexamples [L]: `Grid.unanchored_not_integral`, `Grid.grid_extra_instant`. Protection bound check `experiments/n8/protection_bound_check_v1.py`: 63,753 pairs, 0 violations, 2,795 recaptures, smallest sum 216/65 [OBS].

- E430: `LonelyRunnerFresh/` 11 modules, 3,545 lines, 195 axiom lines [L]. `Protection.lean`: `telescope_lower_edge`, `protection` (Σ b/x_k ≤ 3), `recapture_sum_gt`, `no_recapture_of_faster`, `no_recapture_one_move`, `protection_offset`, `offset_recapture_example`, `owner_iff_fails`. `ChainLaws.lean`: `later_lap_of_ge`, `setter_recur_lap`, `lap_seq_mono`, `setter_not_twice_in_row`, `per_lap_decrease`, `word_strictAntiOn_lap` (E332's [TESTED 0/372,642] now a theorem), `link_faster_persistent`. `Octagon.lean`: `isolatedAt_iff_gaps`, `not_exactly_seven`, `globallyIsolatedAt_iff_octagon`, `globallyIsolated_pairDist_eighths`, `integer_flank_isolated_iff`. "Where": landing = first isolation [L]; that it is an opening [reasoned, not yet in `Fresh/`]; existence = the conjecture, open.

- E431: `LonelyRunnerFresh/` 14 modules, 5,075 lines, 272 axiom lines [L]. `Doors.lean`: `instant_is_opening`, `landing_is_opening`, `landing_runner`, `zone_run`, `doors_agree` (five doors A–E equivalent), `global_door_iff` (each ↔ `LonelyRunnerEight`); C→B and E→B rest on a step [PROVISIONAL: counting tool]. `LonelyCells.lean`: `isClosed_lonelySet`, `cell_of_lonely`, `cell_left_end_is_opening`, `cell_right_end_is_entry`, `cells_upTo_finite` ([PROVISIONAL: counting tool]), `landing_is_first_cell_left_end`, `cell_width` (w − u = (k' + 7/8)/y − (k + 1/8)/x), `degenerate_opener_ne_closer`, `degenerate_cell_isolated`, `ap_first_cell_is_touch`, `opener_eq_closer_window` (width 3/(4x)), `states_below_landing`. `APNeighbourhood.lean`: `interior_clear`, `end_clear`, `end_clear_seven`, `ap_isolated_of_le` (radius ε ≤ 1/16), `ap_nbhd_isolated` (1/32), `apT_displacement` (|apT e k − 1/8| ≤ 2ε/7), `cx_not_isolated` (ε = 1/15: instant 15/104 of runner 1 not isolated; pair (1,7); 6 + 2ε ≤ 7(1 − 2ε) iff ε ≤ 1/16), `cx_isolated_displaced` (isolated at 135/488). `experiments/n8/ap_nbhd_counterexample_cascade_v1.py`: states 15/104, 135/736, 135/608, 135/488 [T exact, one arrangement; not formalised in Lean].

- E432: `LonelyRunnerFresh/` 15 modules, 5,824 lines, 313 axiom lines [L]. `PairLaw.lean`: `opening_at_u`, `entry_at_w` (u_a = a²/(8 d_a), w_a = a(8−a)/(8 d_b)), `interval_lonely` (ρ ≤ 1/22), `u_le_w_iff`, `pair_law`, `pair_both_iff`, `pair_touch`, `pair_exclusive`, `interval_isCell`, `interval_ends`, `interval_width`, `instant_lonely_record`, `pair_law_record` (record's radius c/20). Exception [L, T exact]: `record_interval_fails_c20`, `cx_class_seven`: the record's interval claim (E69 docstring; v9 Part I-1 row 1) is false at c/20 for class 7 (runner 2 enters first when ρ > 1/22); `displaced_cell` gives [7/8, 15/(8(2+ρ))] for ρ in [1/22, 1/14]. `experiments/n8/pair_law_class7_check_v1.py`: at ρ = 1/20 right end 35/38 not lonely, runner 2's entry 75/82 lonely; at 1/22 coincide (11/12) [T exact]. Next-tightest radii 3/46, 1/15, 7/90 [OBS]. [L, PARTIAL] for the AP with deviation radius ≤ 1/22.

- E433: `LonelyRunnerFresh/` 16 modules, 6,745 lines, 356 axiom lines [L]. `GridPairLaw.lean` (922 lines, 43 axiom lines): `setting_of_complete`, `setting_mirror`, `interior_res`, `opening_at_u`, `entry_at_w`, `u_le_w_iff` (⇔ o_A d_B ≤ o_B d_A), `pair_cover`, `grid_interval_lonely` (under `ClassHyp`, η ≤ 1/8 on rescaled positions), `grid_interval_isCell`, `grid_interval_width`, `grid_pair_law`, `grid_instant_lonely`, `drift_le`, `eta_sharp`, `ap_case`, `ap_exception_eta`, `F1_interval_fails` (ρ ≥ 3/(28m + 24)), `F1_instant_lonely`, `F1_displaced_cell`, `F2_both_instants_fail` (7/(56m + 90) < ρ < 21/(56m + 88)), `F2_example_cell` ([485/558, 35/38]), `F2_example_cascade` (one move from 245/282 to 485/558; displacement 5/13113).

- E434: `LonelyRunnerFresh/` 20 modules, 8,737 lines, 445 axiom lines [L]. `Carving.lean` (41 axiom lines): `lonelySet (insert d ds) = lonelySet ds ∩ clearSet d`; a cell dies exactly when inside one open zone of the added runner; wide cell survives ([PROVISIONAL: covering]); `cell_gap` ≥ 1/(4 d_max); `ap_first_cell_leftmost`; L2 exception ds = {8}, d = 1. `Gate.lean` (29 axiom lines): m never in the way on R in [1,7]; in the way on (7,9), next opening exactly R = 9; no isolation or landing in (7,9); landing above 7 iff [1,7] holds no isolation; `gate_lands_at_nine_iff`; L1(d) not proved. `Types.lean` (15 theorems; `StrongGate` OWED) and exact data [OBS unless marked]: all 7-subsets of {1..N}, gcd 1, N up to 56 (230,701,234 sets); full types 74 at N = 12, 604,660 at N = 56 (`firstMove_lap` [L]: infinite); rank words 48 at N = 12, 63,243 at N = 56, maximum 24 moves; coarse class (opener rank, closer rank, landing above 7) no ties: 37 for N = 19 to 44, 39 at N = 48, 41 at N = 56; with ties 32 to 1,151; integer gate crossers: none for N ≤ 44, 5 for N ≤ 56, 47 for a7 ≤ 70 (per a1 = 6..9: 2, 3, 15, 27); none with a1 ≤ 5 to a7 ≤ 100 (3,836,946,849 sets); maximum landing 657/64 at (9,23,30,37,41,51,64); crossers (6,16,21,26,29,36,45) R = 294/29, (6,16,21,26,29,37,46) 219/23, (6,18,23,29,32,40,50) 171/25, (7,17,22,29,36,40,51) 9. [L]: `no_crossing_of_small_dmin`, `strong_gate_of_gap` (15d ≥ 17m), `late_blocker_forces_slow_lap_one`. `DMax.lean`: `dmax_complete`, `dmax_globalIsolation`, `dmax_reading_unchanged`, `dmax_isolatedAt_iff` [L].

- E435: `LonelyRunnerFresh/` 22 modules, 9,979 lines, 508 axiom lines [L]. `Cycle.lean` (849 lines): `grandReturn_iff`, `grandReturn_isLeast` (1/G), `positions_period_iff`, `isolatedAt_add_grandReturn`, `readingPattern_least_period`, `isolatedAt_add_gcdDiff`, `exists_grandReturn_iff`, `sqrt2_no_grandReturn`, `grandReturn_eq_rotations`, `grandReturn_slowest_iff`, `ap18_cycles_equal`, `ap18_four_before_return`, `reading_update`, `single_change_reading`, `isolatedAt_grid_iff`, `shiftIdx_complete_iff`, `single_change_losers` ([PROVISIONAL: counting tool]). `StrongGateStudy.lean`: `idle_before_entry`, `violation_carves` ([PROVISIONAL: covering]), `late_blocker_fast` (5m < 3y), `fiveCarve_of_fiveReach`, `strongGate_of_fiveCarve`, `lonely_at_inv_of_no_multiple`, `crosser_needs_multiple`, `crosser_dmin_seven`…`_three` [L]; `FiveReach` OWED ([PROVISIONAL: covering]). [OBS]: integer 7-sets with a1 = 3, 4, 5, a7 ≤ 100 have first lonely R* at most 51/9, 68/11, 125/19; setter-into-gate counts (3,3) 22, (5,4) 9, (2,2) 6, (6,5) 5, (4,4) 3, (7,7) 2; smallest setter ratio 7/3; all 47 satisfy 17m ≤ 15d; best chain of five readings 2125/483 (LP maximum, not attained); 6-set enumeration maximum 275/64; real example R* = 65/7 [OBS, float-steered, exact verification only for the printed example].

- E436: `FRAMEWORK_COMPILATION_v10.md` written (v9 with the `ProgressionPairN` row changed; `compile-diff` 0 losses). Stage-1b rows `ArrBlockRule8`, `ArrBoundedCovered8` move to "imported, tested" [OBS] (`experiments/n8/block_rule_cascade_v1.py`: core {1}, block x = 8k: landing R = 1 + 1/x to x = 1024; 14,328 pairs 0 mismatches; suprema 6, 34, 62; 0 violations in 343,741 moved sets). `LonelyRunnerFresh/` 26 modules, 13,473 lines, 673 axiom lines [L]. `BlockLanding.lean` (44): `lonelySet_union`, `landing_union_ge_u`, `landing_union_eq_u`, `landing_union_gt_wC`, `landing_eq_u_iff`, `typeX_iff`, `inWay_bound_iff`, `nextOpening_bound` (8m·nextOpening = 1 + (m − s)/x), `core_displacement`, `singleton_core_displacement`, `u_multiple`, `singleton_one_multiple`, `cell_degenerate_iff`, `degenerate_at_bound`, `typeX_degenerate_iff`, `typeX_imp_narrow`, `not_typeX_of_wide`; {1,7,8} lands at 9/56, {2,12,15} at 3/32. `FiveReach.lean` (66): `fiveReach_iff : FiveReach ↔ Reach 5 6`; `reach_one` (9/7), `reach_two` (81/49), `reach_three` (729/343, [PROVISIONAL: covering]); `not_reach_six` (first lonely R = 4900000/562313 after 20 moves); witnesses 8500/3089 (6 moves), 6250/1421 (12 moves); `union_bound_range`, `capacity_jump`, `lap_one_return_gap`; OWED `ReachFourSharp` (289/105), `ReachFiveSharp` (2125/483). `SmallDmin.lean`: `crosser_iff_pattern`, `crosser_iff_linear_pattern`, `lonely_in_window_iff`, `crosser_iff_all_laps_fail`, `patternLinear_iff_intPattern`, `crosser_scale`, `crosser_first_zone`, `crosser_last_zone`, `crosser_index_ge_eight`, `crosser_first_two_setters`, `crosser_two_large`, `crosser_second_largest`, `int_crosser_near_multiple`, `ex_crosser`, `lonely_m3`, `lonely_m4`, `lonely_m5` (R = 17/3, 68/11, 125/19) [L]; OWED `NoSmallIntegerCrosser`, `ReadingsAboveFifteenSevenths`; [OBS] 337 cells with exact rational vertices (`Z1/cells_table.txt`), zero-crosser counts 988,172,368 / 927,048,304 / 869,107,785 sets. `GridToGrid.lean` (27): `pair_change`, `matched_reading_shift`, `new_isolatedAt_iff`, `isolatedAt_transfer`, `instants_meet_iff`, `ratio_odd_of_meet`, `counterexample_double`, `double_step_no_isolation`, `path_reading_affine`, `reading_reaches_eighth` [L].

- E437: `PathLaws.lean` (30 axiom lines) [L]: `isolatedAt_transfer`, `openness_s`, `openness_t`, `lonely_limit`, `lonely_limit_pos`, `not_isolatedAt_zero`, `isoSet_dichotomy`, `loss_needs_boundary`, `loss_no_interval`, `isoSet_open_of_cell`, `escapeEx_escape` (speeds (1, 1+s, 3, …, 8), lonely at t = N + 1 + 1/8 for s = 1/(2(N+1)), none at s = 0 where two speeds coincide), `lonely_time_escapes`, `isoSet_eq_of_owed`; OWED `PathLonelyBound`, `SuccessorIsolation`. `experiments/n8/touch_transport_v2.py` [OBS, exact Fractions]: 2,600 subject-paths over 325 paths; every death and birth of a cell is a touch in all 35,740 deaths and 33,702 births; 0 merges, 0 splits; in 35,683 of 35,740 deaths a cell persists on both sides; 57 deaths with no cell left in (0,1], the cascade's first cell beyond the window; mirror instant inside a survivor in A1: 872 of 1,115; no path with an empty lonely set. 27 modules, about 726 theorem and lemma lines.

- E438: `LonelyRunnerFresh/` 29 modules, 15,036 lines, 750 axiom lines [L]. `BlockLanding2.lean` (23): `clearFirst_zone_form`, `typeX_iff_cover`, `cover_singleton_iff`, `two_zone_needed_iff`, `landing_iff_first_open_cell`, `landing_past_least` ([PROVISIONAL: covering] at steps); [OBS]: 8 of 1,167 type-X first cells needed three or more zones (core {13}, block {6,45,32,2}, first cell [1/104, 7/104], landing 25/256). `PathClassify.lean` (24): `lre_isoSet_eq`, `lre_imp_successorIsolation`, `lre_imp_right`, `lre_imp_closed`, `successorIsolation_only_openness`, `isoSet_eq_iff_leftClosed`, `isClosed_iff_no_escape`, `escape_witnesses_diverge`, `lre_iff_leftClosed_right`, `owed_pair_imp_lre`, `pathLonelyBound_iff_localBound` ([PROVISIONAL: covering]), `not_localBound_imp_touch`, `not_localBound_imp_seq`, `strictForm_refuted`, `ap_not_strict` ([PROVISIONAL: counting tool]), `ap_const_path_isoSet`; OWED `ConjectureGivesBound`. [OBS]: touch-only integer sets: size 1–6 entries ≤ 16 none; size 7 entries ≤ 28 exactly three: (1,2,3,4,5,6,7), (1,2,3,4,5,7,12), (1,4,5,6,7,11,13), lonely times 1/8, 3/8, 5/8, 7/8.

- E439: `LonelyRunnerFresh/` 30 modules, 16,084 lines, 808 axiom lines [L]. `ZeroMargin.lean` (58): `reading_expand`, `exact_touch_survival`, `touch_survives_of_strict`, `touch_fails_of_violation`, `helly_one_dim`, `free_touch_survives`, `free_example` ((1,2,4) at t = 1/8), `scaling_B_obstruction`, `scaling_nonaffine_survives`, `ap_classes`, `div8_slack`, `sigma_antisymm` (σ_a = δ_a/a − δ_b/b, σ_b = −σ_a), `ap_mirror_survival`, `survival_form_is_linearisation`, `pair_law_is_survival_form`, `scale_flip`, `conjugate_pair_exists`, `ratio_condition` ((p + q) ≡ 0 mod 8), `ratio_condition_needs_coprime`, `commensurable_mirror`, `gordan`, `every_direction_survivor_iff`, `ap_touch_positive_dependence`, `ap_every_direction_survivor`; counting steps [PROVISIONAL: counting tool]. `touch_forms_v1.py` [OBS, exact]: touch-only sets among all 18,643,560 integer 7-subsets of [1,40]: 11, all scalings of the AP (1,…,7), (1,2,3,4,5,7,12), (1,4,5,6,7,11,13); rational sets a/Q in [1,12], Q = 2..5 (about 283 million): multiples of the same three; cones cover for each ([PROVISIONAL: covering]); 7-subsets of [1,14] and [1,18] (3,432 and 31,824): 4 sets with no positive-width cell; exception (1,2,3,4,5,6,11): under δ = (1,4,9,16,25,36,77) at e = 1/1000 both touches vanish, least lonely time 125/1001. Reading [PARTIAL]: the route accounts for the AP, its two relatives and the pair law; does not reach a general arrangement.

- E440: `LonelyRunnerFresh/` 33 modules, 17,561 lines, 858 axiom lines [L]. `TouchTheory.lean` (26): `wholeset_conjugate` (every lonely t0 has N ≡ 7 mod 8 with N·t0 lonely and roles swapped; via `simult_approx` [PROVISIONAL: counting tool]), `cones_cover_iff`, `violating_direction_exists_iff`, `singleton_touch_survives`, `touch_conjugate_cover`, `not_cover_iff`, `E439_example`, `violation_kills`, `affine_survival_classification`, `sigma_zero_nonaffine`, `window_trichotomy`, `ap_pair_survives_every_direction`, `scaling_case`, `blocked_pair_conjugate_example` (d = (1, 7, 16/7, 2, 3, 4, 5): 1/8 lonely, 7/8 not, 15/8 lonely). `Boundaries.lean` (15): `opener_unit`, `entry_unit`, `touch_units`, `width_congruence` (width m/(8xy), 8 | (m + x + y)), `finset_half_lonely_iff_odd`, `lonely_mirror`, `four_cells`; [OBS] (`experiments/n8/totient_boundaries_v1.py`, populations 3,431 / 31,788 / 170,213 sets at N = 14, 18, 22): smallest positive-width cell 1/1056 at (1,2,3,5,6,11,12); landing reduced numerator 1 (181,859), 3 (8,894), 5 (1,209), 7 (21) at N = 22; "each eighth-class at most once" refuted (34,327 of 170,213); smallest gap 1/(4N). `CarvingLineage.lean` (9): `cell_in_window`, `isCell_iff_transversal`, `ends_le_iff_pairwise`, `ancestor_isCell`, `cell_insert_unilateral`, `exists_lonely_iff_transversal`, `zones_cover_iff_all_transversals_blocked` ([PROVISIONAL: covering]; each is the conjecture); [OBS] (`carving_lineage_v1.py`): no stage-wise invariant; refuted examples (1,2,3,4,6,7,8) and (3,4,5,7,8,9,13) (window [3/8, 5/8]). (6,16,21,26,29,36,45): landing 49/232, R = 294/29.

- E441: `LonelyRunnerFresh/` 35 modules, 18,588 lines, 912 axiom lines [L]. `TwoScale.lean` (26): `lonely_iff_shift`, `residue_window`, `r1_clear`, `r1_blocked_small`, `r7_blocked_small`, `r7_clear_from_two`, `residue_slack`, `tower_two`, `compat_iff_exists_lonely` (`Compat D' C` iff D' ∪ 8C has a lonely instant), `explicit_instant` (hypothesis d·η ≤ 1, [PROVISIONAL: covering]); `CompatAll` OWED. `two_scale_v1.py` [OBS] (1,715 / 20,349 / 92,730 sets at N = 14/18/22): `explicit_instant` applies to 2,568 of 92,730; landing = η_C in 2,997; later in all 89,733 with min(D')·η_C < 1; 60,684 pairs 0 mismatches; fail set 82,368 + 384,384 + 1,860,480 pairs (c ≤ 48), 0 without a lonely instant; no unit works for 43,243 of 92,730; landing in a central cell for 9,519. `LandingExceptions.lean` (28): `cofactor_class`, `landing_le_half`, `opener_lap_bound`, `inWay_opening_iff`, `step_blocks`, `chain_blocks`, `chain_blocks_opening`, `clear_lap0_iff`, `landing_lap0_iff`, `landing_gt_of_forbidden`, `lap0_opener_is_min`, `neighbour_in_way`, `landing_no_predecessor`, `openers_at_instant`. `landing_exceptions_v1.py` [OBS]: 27,484 + 282,339 + 1,553,083 earlier openings each blocked, 0 violations; landing lap above 0 in 792 of 3,431; 13,642 of 31,788; 61,958 of 170,213; (2,3,4,5,6,17,31) lands at 17/248; (1,2,3,4,5,6,8) at 9/64, (1,2,3,4,5,6,16) at 17/128; p mod 8 = 7 sets 21 / 25 / 356 at N = 22 / 26 / 30. "No mechanism guaranteeing the transversal was found."

- E442: `LonelyRunnerFresh/` 36 modules, 19,252 lines, 951 axiom lines [L]. `RealCase.lean` (39): `clear_shift_iff`, `blocked_iff`, `clear_iff`, `slack_iff`, `lonelyAt_gate_iff`, `inWay_gate_iff`, `nextOpening_gate` (8m·nextOpening = R0 + (1 − δ)/ρ), `isMove_gate`, `isMove_of_gate`, `dev_scale`, `eps_strictAnti`, `blocked_integer_iff`, `delta_zero_shift`, `touch_ratio`, `touch_of_ratio`, `tie_ratio`, `irrational_not_ratioForm`, `generic_of_irrational`, `generic_cell_pos_width`, `isoSet_open_at_generic`, `cell_end_zero_margin`, `moebius_value_subsingleton`, `pair_equation_subsingleton`, `pair_ratio_dichotomy`, `nongeneric_params_countable`. `real_case_v1.py` [OBS]: Q = 3 5,378,824 sets; Q = 5 231,916,608; Q = 7 2,641,901,328; ties/touches 37614/170213, 399927/5378824, 7533888/231916608, 66544926/2641901328; landing in [1,7] for all sets at N = 22 and Q = 3; Q = 5 all but 14 (maximum 511/50); Q = 7 all but 183 (maximum 65/6); no landing in (7,9); rank 1 at lap above 0: 0, 0, 5, 42; R* = 1: 108255/170213, 3776650/5378824, 166764591/231916608, 1941245798/2641901328; explicit instants 126850/170213, 4653825/5378824, 205076113/231916608, 2304023325/2641901328. Existence not reduced by passing to reals or residues.

## 2. RETRACTED, REFUTED, CORRECTED

- E384 (same-day correction): decimals were renderings; the landing of d* + 10^-k is identical for k = 3,5,7,9 and d* − 10^-k equals the landing of d*: (5,6,19,23,33,36; 55) landing 3/88, from above 17/9 times; (2,6,11,19,36,37; 14) 1/16, 11/6 times; (6,14,20,23,31,37; 42) 1/48, 54/31 times; (2,3,5,13,20,22; 30) 1/16, 17/10 times. "258 of 14,400 above 1.001" withdrawn as a statement (threshold chosen after the fact). D1 is a pigeonhole using order seven: an existence step for non-integer values on this segment only, not the displacement argument. Population was a sample.

- E385 (same-day correction): "and, as far as this population shows, the sets where the cascade works" withdrawn; 22/5 in Z and 17/3 in R do not separate the classes; no set in either has a gate-crossed landing.

- E386 corrects E212: `WideStep8 1` is false at X24; E212's "M = 1 suffices" holds only on the populations it ran (spread (9,12], readings ≤ 20/24/2,000 and walks in (9,12]).

- E387/E394: the floor "longest K'_6 window ≥ 2/ρ7" is not a general mechanism: fails in 145 + 14 crossers with ρ7 in about (7.0, 8.3).

- E389 replaces E388's closing sentence ("the non-overlap of those conditions for the K'_6 windows") with S6: the conditions of both windows, jointly.

- E390/E391: E382–E389 constructs (windows, N_A, N_B, S6) withdrawn as a route; diagnostics only.

- E391 correction: draft reply quoted the numerator as 39424938224285; exact value 39423938224285/3691147638604.

- E394: the earlier replies' reasons for why it cannot be done are withdrawn (recorded on the owner's message).

- E394: second (4,3) condition (cofactor window longer than Σ 1/c_j) holds in none of the 25,224 leftover sets.

- E397: "the largest flank always survives" is false (d_max dead in 1,404 sets of [1,24]).

- E398 (same-day correction): "35 of the 41 contain the reading 1 or 2" replaced by: in 40 of the 41 sets with at least five dead flanks the least reading is 1 or 2; exception (6,7,8,9,10,11,13) (dead flanks 7 to 11, survivors 6 and 13).

- E400 on E393: E393's population checks only gcd 1, one odd reading, cost ≥ 8; its instant is the resolution certificate at D = 8h and its 30,936 sets are closed by `no_small_resolution`; `FreeFlank8` is its J = 0 case.

- E402 corrects E400: `ParitySplit8` was listed under "Derived here"; it is `TILING_AND_BLOCKS_v1` §1's block criterion (a < 2·max(u_O, u_E), 2026-09-10) read at the descent's offset τ; E400 added the Lean statement and its use with `no_one_free`, not the criterion.

- E404: the agent's summary gave class R at c ∈ {4, 8, 12}; the `.out` also has the four cases at c = 16.

- E405 on E403: the divisible family is not empty in the residual (43 + 380 constructed members; 238 not separated at ratio 9).

- E408 on E404: class R is not E404's 34 cases on [1,40]; 170 cases on the wider range, not shown to be finite. E409: class R falls inside case Φ of a written proof [P, delegated].

- E408 on E402: v1 axiom records predated the last source edit; re-run as v2, every line agrees; grades stand.

- E410: a first statement on closers "used only its first window" and was corrected ([T 489/489]). Derivation rejected: "order-6 slack gives d₇ < 6 d₆ for sets with no 1/7 instant" is wrong; (1,2,3,4,5,6,42) is a counterexample.

- E412: the d_min ≡ 0 (mod 8) correlate (all 9 exceptions) does not account for the failures.

- E414 withdraws E413: the remark that the arc length 130/7 periods "is below the 746556000/37100749-period gap of those AP-like clusters" (arc-against-gap comparison fails at ρ = 26) is withdrawn; no ρ in [26,200] fails in the direct test; the measured gaps stand. Also: header of `modgap_aplike_v2.out` says "below 1.3"; the six are within a factor below 5/4.

- E416 corrects E415: "exactly" and 5 as a sharp threshold withdrawn; exact counterexamples at ρ₂ = 5 and with all ratios ≥ 6.

- E418 supersedes E416: "none for ρ_min ≥ 7" used an unreliable grid objective; exact counterexamples at r = 7 and r = 71/10.

- E419 on the cell_lp runs: the edge 43/6 was that type's last move, not the boundary; the cell reaches 20625/2873.

- E420: the verdict line "[P, computer-checked]" in `_w36_5_16.out` is withdrawn; the grade is [TREE].

- E422: `block_three_check_v1.py` docstring had been edited in place (label E410) and `.out` overwritten (breaks rule 21); v1 restored, v2 created. The check's ratio 26 is weaker than E231's 35/3; nothing advances `ArrBlockRule8 3 9`.

- E423/E425: E423's open count at m = 1 (670 of 812) becomes 570 of 812 once M(1,3)'s rows are wired (E425).

- E425: headers named only order seven as lower-order input; mechanical read finds orders four to seven for `lonely_eight_or_residual`.

- E426: entry first appended as a second "E420", renumbered E426. `SlowestSkeletonN.lean`'s docstring sentence "the conjecture now follows from the single spread-free covering `RegimeSkeleton.Cover8`" superseded. Reply of 2026-10-06 said `Defs.lean` defines nothing with measure: wrong; it carries `goodSet_measurable`.

- E427: withdrawn: the proposal that slot descent is the rank fall between bridges up (refuted by the 35,261); the reading of (1,2,3,4,5,8,14) as a wrap (it is the zero convention); sanity line "9,286" in `grid_deviation_chain_split_v1` stated wrongly. Status-message chunk labels were wrong (contents accurate).

- E429: `Framework.IsGridWithDeviation` is vacuous (every arrangement satisfies it) [L]; `Framework.GridGlobalIsolation` is a sufficient-instants statement, not the φ(8) law's "exactly" (`grid_extra_instant`). E299's slot-7 hypothesis is idle (`enteringEdge_firstMove`). Owner's pasted text: per-step shift is gap·b/(8s) with gap < 2, not b/(8s); "≤ 3" should read "≤ 3b".

- E430: E429's "owed: the owner's reading of 'where'" withdrawn; `owner_iff_fails` [L]: the pasted iff is false in both directions.

- E431/E432: the record's `ap_nbhd_lonely` radius 1/32 re-proved at 1/16; the record's interval claim for `ProgressionPairN` (E69; v9 Part I-1 row 1) false at c/20 for class 7; full interval needs 1/22; "the closer is the mirror runner 8 − a" is wrong: the closer is whichever runner enters first. Reworded in `FRAMEWORK_COMPILATION_v10.md` (E436).

- E433: reading `GridPairLawN`'s hypothesis as a bound on deviations in grid-step units is wrong for large offsets (`F1_interval_fails`, `F2_both_instants_fail`); the record's rescaled hypothesis stands.

- E434: correction to the record: E342's "integer readings, none above 7" (66,000 sampled sets) and E357 (s ≤ 3) do not extend; integer crossers exist from d_min = 6. L2 "the added runner never kills the first cell" true only when the added runner is at least all others. E340's hand proof does not cover a blocker entering after the last state at or below 7.

- E435: "the cycle is the slowest speed's full rotation" is not the period of the pattern in general (AP 3..10; AP 3,5,…,17); equals the grand return iff the slowest speed divides every speed.

- E436: `ArrBlockRule8`, `ArrBoundedCovered8` from "undecided" (E428) to "imported, tested". A claim "past-the-cell forces zero width" is false: {2,12,15} has positive width; for {2,12,15} the formula's 6/5 is u, not the landing (3/32, R = 3/2). `Reach 6 6` false [L].

- E437: the "handover" picture is not what the cascade shows (survivor cell already present in 35,683 of 35,740 deaths); T=3 figures for population B carry no weight; the gate/`FiveReach` thread paused (my reading, for the owner to confirm or strike).

- E438: "a strictly clear instant exists at every parameter" refuted [L] (`strictForm_refuted`; AP isolations are all touches).

- E440 corrects E439: (a) AI's run time about 25 minutes, not 13; (b) "a whole-set conjugate needs commensurable disparities" took a sufficient hypothesis for a necessary one; `wholeset_conjugate` [L] holds for all positive families; (c) the integer mirror symmetry is a feature of any positive family; (d) three unused-variable warnings in `ZeroMargin.lean` (report said none).

- E439 on the brief: survival is not only first order (`reading_expand`); the expectation that a touch can lack a role-swapped partner at pair level is refuted.

- E440: AJ's pattern "the landing lies in the first window of d_min" (all 170,213 sets at N ≤ 22) is false in general ((6,16,21,26,29,36,45)); "every window of d_min contains an isolation" refuted; "the landing ancestor at stage s is the first cell not killed by any single remaining runner" refuted.

- E441 corrects E440 (AL's reading): "1/3/5/7" counts are p mod 8, not p; "k < x" is 8k + 1 ≤ 4x (t* ≤ 1/2); counts are over openers (per set 160,233 / 8,750 / 1,209 / 21). "The first setter is the smallest forbidden disparity" false in general; the residue rule (d mod 8 determines the landing class) false.

- E442: reading "every lonely instant [of a generic set] is a point of positive margin" false (`cell_end_zero_margin`); integer patterns of E440/E441 that are population-size artefacts ("R* at most 33/7", "all landings in [1,7]", "rank 1 at lap above 0 never occurs", "first setter = least forbidden") must not be extended.

## 3. OBJECTS

- Case 3 (E182, used in E382): restart: a reading in the way at b's exit.

- C6 (E384): the frozen six's clear set, periodic with period 1 and non-empty by order seven.

- D1, D2 (E384): as in section 1.

- Case Z / class R (E385): Z = some six-subset has gcd > 1 after normalising the overall gcd to 1; R = every six-subset coprime.

- `GridStep8 S m M` (E386): the bound is clear, or a grid-class instant of a grid through one of its readings e at step ≥ m/M. `WideStep8 M`: the owed statement for spread > 9.

- Window A / window B (E386, E387): A = landing ≤ 7, first stretch non-empty; B = gate crossed, landing ≥ 9, R in [9,15].

- K'_k (E387): K'_1 = [9,15]; K'_k = K'_{k−1} minus the zones ((8j−1)/ρ, (8j+1)/ρ) of reading k. K6, K'6 (E389): windows of the six's clear set in [1,7] and [9,15].

- Gate crosser (E386): L1: landing > 7 iff K_7 empty.

- R8 (E387): `FastRunnerN.lonely_of_fast_runner`: a reading V > (n−1)·s for every other s, the others lonely at 1/(n−1) by the order below ⇒ lonely.

- N_A, N_B, S6 (E389): as in section 1.

- Candidate (a,k) (E391, owner's object): a in {1,3,5,7}, k ≥ 0: c = (8j+1)/rho_a, j the lap of reading a nearest the ideal instant a + 8k (R = 8 d_min t).

- Shape (multiples of 8, non-multiples) (E393): `EightResidual`'s first nine fields leave shapes {(1,6), (2,5), (3,4), (4,3)}.

- Free-edge move, H1, H2, τ*, s* (E393): as in section 1.

- Flank rank, walkers, opening (E395): flank rank 1 = slowest block reading, 6 = fastest; walkers = the other block readings; opening u = 8k + 1; a walker with ratio r = x_j/e reads (8k+1) r mod 8 and is in the way iff within 1 of a multiple of 8.

- Lemma (C) (E395): a run of N consecutive openings covered by the union of at most five walkers is covered by a single near-sharer or by an exact half-pair.

- Dead flank (E397): flank e is dead iff every opening k ≥ 0 has a walker in the way: (8k+1) x_j mod 8e outside [e, 7e]. Walker type (q, p mod 8, class count), g = gcd(x_j, e), q = e/g, p = x_j/g.

- Pattern letters (E400 onward, as used): o = odd non-multiple, t = reading ≡ 2 (mod 4), f = reading ≡ 4 (mod 8).

- Descent shifts (E400): t = (τ + k)/8 with τ clearing the cofactors; parity split: one side's #odd + Σ gcd(d,8) below 4.

- Silenced reading (E402): one whose two positions half a lap apart both stay outside the subject's slot.

- M(a,b) (E404): there is τ with a numbers clear at 1/8 and b odd numbers clear at 1/4.

- Reduction point (E403): τ = m/w for odd non-multiple w (blocks exactly one shift); τ = (2m+1)/(2v) for 2v, v odd (blocks none).

- Divisible family (E403, E405): every odd non-multiple divides some cofactor and, for (o,o,t,t), the cofactors block the reduction points of the 2-mod-4 readings.

- Class R of M(1,3) (E404): the cases with no written proof; 34 cases in [1,40]; for 4 | c reduces to: some y with ‖y‖ ≥ 1/8 and a quarter point v with ‖(b_j/c)·y − v‖ ≥ 1/4 for j = 1,2,3.

- Divided-flank progression (E407): openings (8j+1)/(8e) of the multiple whose cofactor every odd reading divides, at lap indices j ≡ j0 mod 8·lcm(c/w).

- M(1,3) notation (E409): b = ±u ≡ 1 (mod 4); c = 4m, a = (b−1)/4; G = gcd(a_mid − a_lo, a_hi − a_mid), x = (a_mid − a_lo)/G, N = (a_hi − a_lo)/G; H_w = closed half circle [w, w + 1/2], w a multiple of 1/4.

- (6,1) statement (E410): for seven readings some d and some instant have the other six ≥ 1/7 and d ≥ 1/8. Rule B: d* = argmax t_d; rule D: soonest edge. Bystander: an added reading that keeps the landing (`bystander_iff`: for t = u/w iff d·u mod w in [w/8, 7w/8]). Takeover: landing at the added reading's edge E.

- v1 residual (E411): the record's `eight_residual`, EightResidual without the fields added since (in particular without the small-resolution clause). Full residual: all 22 fields.

- Class F7 (E411): 7-sets with no lonely instant at 1/7; core = the six smallest readings.

- Cluster shape (E412): one slow reading d_min against a cluster of six.

- Arc criterion A(S) (E413, E415): the 1/7-cascade of C = S minus m started at 1/(7m) has its first lonely instant at most 6/(7m) (u = 7·m·t in [1,6]); A(S) implies S lonely at 1/7 (`lonely_cons_of_arc` [L]).

- B_i (E417): {u in [1,6] : ‖ρ_i u/7‖ < 1/7}.

- G(ρ) (E418): the largest length of a window of K = [1,6] minus the open zones ((7j−1)/ρ_i, (7j+1)/ρ_i).

- Two-arc statement (E420): the 1/7 cascade of all seven readings lands within d_min's second arc (u ≤ 13); FAIL only if beyond.

- Motzkin certificate (E420): multipliers yₖ ≥ 0 with Σ yₖ aₖ = 0 over (ρ₀,…,ρ₅,1), weight 1 on the strict rows.

- Cap routes (E426): `Cover8 M`, `WideStep8 M`, `WindowBound`: each needs one bound (step bound M or time T) for a whole class of arrangements.

- `SettledCounts8`, `SettledCounts8'`, `CountSplit8 od a b`, `OottCounts8` (E423, E425): count forms of the residue cases T1–T8 (and T9, T10); counts = (multiples of 8, odd, ≡ 2 mod 4, ≡ 4 mod 8).

- Grid coordinates (E427): grid through d_min: y = m·q + r, slot = q mod 8, ε = r/m; start R = 1. D8 / D0: start slots strictly decreasing with 0 read as 8 / as 0. F: reading falls at every step.

- `LonelyRunnerFresh/Fresh/Framework.lean` definitions (E428): `IsArrangement` (positive, injective), `IsOrderedArrangement`, `disparitySet`, `IsDmin`, `IsSubjectDmax`, `IsolatedAt`, `Isolation`, `GloballyIsolatedAt`, `CompleteResidues`, `IsAP`, `IsGrid`, `IsGridWithDeviation`; claims `GridGlobalIsolation`, `LonelyRunnerEight`, `DisplacementPath` (a), `CascadeForm` (b), `CandidateScaleForm` (c).

- Protection (E429/E430): a reading starting at the lower edge P + 1/8 stays strictly inside (P + 1/8, P + 7/8) while Σ b/x_k ≤ 3.

- Doors A–E (E431): (A) an isolation exists, (B) the cascade fixes, (C) its instants are bounded, (D) some flank has a lonely opening, (E) every runner is in the way at finitely many cascade states.

- Cell (E431): a maximal closed interval [u, w] of isolation instants; u = (k + 1/8)/x (opener x at exactly 1/8), w = (k' + 7/8)/y (closer y at exactly 7/8). Touch / degenerate cell: single-point cell, exit of one zone equal to entry of another.

- `ClassHyp` (E433): every other runner within η ≤ 1/8 of its grid position o_j·a/8 at both class instants (rescaled positions), A not past n_A + 7/8 at w, B not before n_B + 1/8 at u.

- Gate (E434): R = 8·m·t; (7,9) holds no isolation and no landing. `StrongGate` / L1(d): the move from the first state above 7 lands exactly at R = 9. Crosser: landing above 7. Coarse class: (opener rank, closer rank, landing above 7). Full type; rank word (as counted in E434).

- `GrandReturnAt v t` (E435): every `v i * t` is a whole number.

- `FiveReach`, `FiveCarve`, `Reach k B` (E435, E436): `Reach k B`: every set of at most k disparities, all at least m, has a lonely instant with R in [1, B]; `FiveReach` = `Reach 5 6`; `FiveCarve` the same with window [1/(8m), 7/(8x)].

- Block landing objects (E436): S = C ∪ F, tC the core's landing, wC its cell's right end, u the first point at or after tC clear for F; type X: wC < u (landing past the core's cell).

- `isoSet`, `PathLonelyBound`, `SuccessorIsolation` (E437, E438): `isoSet` = parameters with an isolation; `PathLonelyBound` = lonely witnesses bounded along the path; `SuccessorIsolation` = every isolating parameter has a neighbourhood of isolating parameters. Escape point; touch-only arrangement (every lonely instant a touch).

- Opener / entry at a touch (E439): opener = reading at k + 1/8; entry = reading at k + 7/8. Survival form σ = δ_i/d_i − δ_j/d_j. Touch cone {x : x_i ≥ x_j for i in O, j in E}, x = δ/d.

- Whole-set conjugate (E440): N·t0 with N ≡ 7 (mod 8), lonely, every opener an entry and every entry an opener.

- Transversal (E440): a choice of one lap (window) per runner whose largest opening is at most its smallest entry; a cell is `[max of the openings, min of the entries]`.

- Two-scale split, `Compat D' C` (E441): D = D' ∪ 8C, t = (a + η)/8; `Compat`: an integer a and real η with a + η > 0, every d in D' in its residue window, C lonely at η. η_C: first lonely point of C alone. Forbidden zone of d_min: |d − 8j·d_min| < d_min.

- Signed residue δ, `RatioForm`, `Generic` (E442): ρR0 = 8z + δ, δ in [−4, 4); `RatioForm`: x(8k'+7) = y(8k+1) for naturals k, k'; `Generic ds`: no pair of ds has `RatioForm`.

## 4. OWNER MESSAGES

- E382 (heading): "ok test that"

- E383: "yes, do that and perturb the exceptions" (heading: "do that and perturb the exceptions"); substance recorded: the existence at the grid is not in dispute (phi(8) law); every confined arrangement is viewed against the ideal and d_min translates the deviation to show where the isolation moved.

- E384 (heading): "ok do this". Also: the owner's meaning of "bounded by the speeds of the arrangement" is order confinement (owner, 2026-10-05).

- E386: "Yes, do that and keep going on layer 5"

- E387 (heading): "do that for window B and keep going on layer 5"

- E388 (heading): "perturb the failures and keep going on layer 5"

- E389 (heading): "keep going on layer 5"

- E390: "yes, do that and keep going on layer 5"; challenge (log: "verbatim substance"): whether the work is "trying to fit my framework into another shape" or "actually looking to prove n=8 with my framework: global isolation is proved, the conjecture's possible arrangements are constrained, any possible arrangement can be viewed as referenced to an ideal, all isolation points are therefore moved and their relocation by d_min shows exactly where all the isolation points are moved to, therefore proving LRC for n=8".

- E391 (paraphrase in log, with one quoted phrase): the gate-crosser/pinned-window reading is "introducing something"; each relocated isolation point acts independently; the sum of all of them gives the arrangement's isolation points.

- E392: "Ok prove it"

- E393 (heading): "Ok"

- E394: "We should be able to piece together a full proof of n=8 from everything we have ... all the parts proved. You need to stop trying to import necessities from else. Believe in the work we have done … We have a 100% perfect oracle. That you should shove [the] 'this is an open problem so I can't do this' back into the stupid ideas closet."

- E395 (heading): "4. Ok"

- E396 (heading): "relax rule 7 for the moment and see if you can extend the work to a lean proof"

- E397 (heading): "Ok try and prove it"

- E398 (heading): "Ok"

- E399 (heading): "What do the proofs, lean/hand written, say about the missing parts of this document?"

- E400: chose "Residual case list" (a question with four options); then: work autonomously until usage runs out (paraphrase).

- E402 (verbatim): "Ok, I am heading to bed. I would like you to work autonomously toward improving, moving our n=8 proof.  You have heaps of context and tokens. If you compact context, please grep and then read the compilation document.  Spin up whatever agent you need.  I would prefer you hit usage limits than require a input from me and sit idle for hours.  the front part of the compilation is how I view the proof can be made, the rest is just about understanding how the cascade does what it does, finding the patterns and rules to locate the mechanisms and proof.  The cascade has never failed or faltered at locating isolation events for all runners at millions of different arrangements. The cascade is the workings of the proof, we just need to find the rules it is operating by to show the conjecture is forced by this arrangement.  Please keep working on it until you run out of usage or you prove n=8." Earlier the same day: "No point in writing v10.  V9 was just to capture context in an efficent way."

- E408: owner's idea "an interaction between mod speeds, mod gaps".

- E410 (verbatim): "I authorise a rule exception for this attempt"; "I said, the 7 order could be used if it used our reproof we did in lean and not the original proofs that are based on different frames"; "Ok this is a whole while attempt let see if we can complete a proof in lean for order 8. Do not suggest this is hard or can't be done because this is an open problem."; "Ok great, please proceed"; "Try both, one then the other and see how we go".

- E411 (verbatim): "Try a first if that doesn't work then b"

- E412 (verbatim): "Yes push there fore and then T1 if that doesn't work"; "Yes run that"

- E413 (verbatim): "Yes"

- E414 (verbatim): "Yes please"; "OK"

- E415 (verbatim): "Go ahdea"; "The ban is only if it does not arise natively. It bans imports not tools"

- E417 (verbatim): "Yes try that"

- E418 (verbatim): "Yes please. Then pause and take a step back. are we getting close or our we pushing things out?"

- E419 (verbatim): "Start at the top and work your way through"; "Remember to look at the framework compilation document, review memory and then continue on with this work"; quoted from 2026-10-01: "Im not sure, should we try and formalise it and see?"

- E421 (relayed, paraphrase): redirected to the residue-case line; the owner is not sure about the mod-speeds / mod-gaps line; resumes only if the owner asks directly.

- E426 (verbatim): 2026-10-06: "Is the lean setup to fail?  I would like to consider this, have we included a density requirement in our lean setup that because the framework works differently we can never resolve until we replace a density/coverage requriement in that is owed with somthing that is native to the framework"; 2026-10-07: "Yes ok."; "Also we had one attempt where we replaced classical.choice wth something else.  What was that and does classical.choice actually reflect what we are trying to do?"; from 2026-09-19: "Perfect, classical.choice was alway suspect".

- E427 (heading, paraphrase): record the item 4 chain work.

- E428 (paraphrase): plan approved; the development lives in a separate folder outside the Lean repo; stage 1 is statements only plus an audit.

- E429 (paraphrase): run autonomously with subagents; symbolic proof over enumeration; exceptions understood and not only counted; the cascade is the object, and a proxy with holes means the theory was wrong.

- E430 (paraphrase with quoted fragment): the system is deterministic, not probabilistic, and "the math [should] tell us" what a statement of "where" is.

- E431–E435 (paraphrase): continue autonomously; E433: continue with the grid-class analogue of the pair law.

- E436 (verbatim): "Yes you have my permission"; "How would I know? We need to test it and see if it works?"; "I don't know we need to find out"; "I would say the evidence decided. Im not an oracle, the cascade is. We are trying to figure out why it always gives us the isolation event. It does it without fail. The failure is ours of understanding why it must do it."

- E437 (verbatim): "lets continue on with the real target, native proof of n=8"; "Please also keep an eye on what can been proven symbolically".

- E438: "continue autonomously".

- E439 (verbatim): "Go with the zero-margin route to start and if that doesnt work go the other"

- E440 (verbatim): "The cascade doesn't see a difference. Why do we?"; "If you are going to look for things, look for totients, look for exact factions, look for boundaries"

- E441 (verbatim): "Not found: a mechanism that guarantees such a transversal exists ... Ok lets look for that"

- E442 (verbatim): "Start with one and go on to the next if you need to"

## 5. OWED, NOT DONE, NOT UNDERSTOOD

- E382: finiteness half of universal transfer stays open as a statement; paths to targets with large rho7 or other closure vertices not tested. Not discharged in slice.

- E383: side of d at t' not derived beyond the sign of the shift; "every relay started at an entering face ends in a box" (the cascade's arrival, E219) not touched. Not discharged.

- E384: loneliness of whole-number arrangements by a direct argument (the displacement from the grid). Not discharged.

- E385: exhaustiveness for R. Not discharged.

- E386: `WideStep8 M` OWED; at M = 1 must be re-aimed. Not discharged.

- E387: window B: K'_7 ≠ ∅ for every gate crosser, not derived; parts (i) ρ7 in about (7,9], (ii) ρ7 > 9 up to 7ρ6. Restated as L-B1, L-B2 in E394; not discharged.

- E389: why N_A and N_B cannot meet; no derivation attempted. (Withdrawn as a route E390/E391.)

- E391: that for every allowed arrangement some candidate is unblocked; independence of the candidates has no proof in hand. Not discharged.

- E392: sets with no subset for the extended case Z (the AP is one) and sets with sum ≥ 1; the chain ending in an isolation for every reading set ("layer 5"). The extension of case Z "not yet tested numerically". Related Lean: E407 `lonely_eight_of_descent_mod` formalises a descent by any modulus q with a budget (see E407).

- E393: existence of a common s in a later cofactor window not shown; shape (4,3) discharged by E400 `lonely_eight_of_residual_four_multiples` [L].

- E394: (L-B1), (L-B2) not proved. Not discharged.

- E395/E396/E397: lemma (C) not derived; classification of every dead flank; "not all seven flanks dead" not proved. Not discharged.

- E398: case argument on the d_max flank "not carried further here". Not discharged.

- E399: not read: `MECHANISM_MAP_v5` E295/E297, `GATE_LEMMAS_v1` beyond E376–E387, `CENSUS_WHY_v1` (MECHANISM_MAP_v5 read in full in E400).

- E400: M(2,2) and M(1,3) (running); Lean for type-level (o,o,t,t); owner's ruling on ground rule 4 (order-seven and order-four inputs); `members_5978_v1.json` format not read (owed); F14 recorded for the owner's ruling. M(2,2): by hand E404, Lean E406. (o,o,t,t) across pair classes in Lean: E402 `lonely_eight_of_oott`. M(1,3) class R: not discharged by E406.

- E401: why every component of the cofactors' clear set contains a point outside the partition states; "Not attempted here". Partly addressed E403/E405 (lonely unless divisible family).

- E403: Lean for the grid lemma and reduction points (grid lemma: E405 `ParityGridN` [L]); the divisible family (open; E405 finds members); a statement for the 2-mod-4 grids.

- E404: Lean for M(2,2) (discharged E406); independent reader for the written M(2,2) proof (E406 Lean build); M(1,3) class R (open); owner's ruling on the order-four input.

- E405: some opening of the divided flank (or another multiple) clear for the other two multiples; the (o,o,t,t) remainder; Lean for M(2,2) (E406).

- E406: M(1,3) class R; the divisible family of (3,4); a statement for (2,5) and (1,6) that couples the offsets through one τ.

- E407: the block of six (six fast readings in one window of a slow one; `ArrBlockRule8 6 9` owed); M(1,3) class R (E409 by hand); the divisible family as a pattern; owner's ruling on the order-seven input (E410 quotes the owner: order seven may be used via the Lean reproof).

- E408: two background results; M(1,3) class R (E409 [P, delegated]).

- E409: Lean for M(1,3) (agent launched, target `LRC/Spec/ParityMixedOneThreeN.lean`); independent reader; owner's ruling on counting tags and lower-order inputs.

- E410: the derivation using the readings' own openings; why residual sets are 1/7-lonely; a full read of `docs/n8` (owed through E420, not done); commit decision; independent check of the three T1 members (E412 treats the exceptions).

- E411: the classification (a set with no lonely instant at 1/7 has its six smallest readings among the twelve cores); Lean for the finite list. Not discharged.

- E412: derivation "a set of the cluster shape has a lonely instant at 1/7"; whether the second-component success has a general reason.

- E413: recurrence statement with fine-structure dependence; whether nearly equal clusters are settled by another rule (E414: 0 of 134,400 sampled in `EightResidual`).

- E414: derivation; an exact threshold; test on the F7 cores (E415 exhaustive windows).

- E415: proof of the threshold statement (E416: 5 is not a threshold); search with larger m.

- E416/E417/E418: exact boundary in ρ_min (E420: 20625/2873 within the box ρᵢ ≤ 16, [TREE]); the proof above the boundary.

- E419: slab and four windows (E420 finished); owner's ruling on c's first arc as the place of the f = 6 case (E246, open); option 3.

- E420: two-arc statement on wider windows and on ρ_min < 6; window to 20 (running); independent re-implementation of the branching rule; Lean for the certificate checker; option 3; owner's ruling (E246); commit decision; "Rule 13 is not met"; result of `brief_prior_arc_v1` not in hand.

- E421: window to 20; two-arc statement on wider windows and ρ_min < 6; independent re-implementation of the branching rule; option 3; owner's ruling on d_min's first arc (E246); commit decision for `BystanderN.lean`. Not discharged (line stopped).

- E422: f = 3 hole stands on the strip 9m ≤ x₁ < 35m/3.

- E423: library search for a theorem tying S's counts to its residues; owner's ruling (ground rule 4). M(1,3) wiring: E425.

- E424/E425: owner's ruling on counting tags and on orders four to seven; the open patterns.

- E426: owner's ruling on congruence form / choice-free check for whole-number results; memory note for items 1 and 2; full read of `docs/n8` (E427 records a read by agents' manifests over 599 files).

- E427: why the carrying-in stops inside the block (`MECHANISM_MAP_v3.md` 376–382, still open); slot descent with a mechanism or dropped; same counts for disparities above 24; v9 rewording; `N8_DOC_INDEX_v1.md` line 70 lacks the [REFUTED] tag on `DoorFirstLap`.

- E428: owner's reading of "where" (withdrawn E430); confirmation or strike of each audit row; mathlib decision; omitted framework items (cycle of one full rotation of the slowest speed; grand return; AP zero-slack Theorems 1, 2; "exactly a/(8d)"; D_max; D_min as displacement from one grid to the next) — E429 `ap_globalIsolation_iff`, `octagon` and E430 `Octagon.lean` supply Theorems 1, 2 and the AP "exactly"; converse of (a) discharged by E429 `displacementPath_iff`.

- E429: replace `IsGridWithDeviation`; bridge `certificate_iff` to an arrangement's disparity set (E430 `integer_flank_isolated_iff` for integer speeds); Theorem 1 and zone-run statements of Theorems 11–13 natively (E430 Theorem 1; E431 `zone_run`, `doors_agree`); why chains end; audit rows; mathlib provision.

- E430: Theorem 11(d) natively (E431 `landing_is_opening`); five-way equivalence of Theorem 13 (E431 `doors_agree`); why a chain ends (the conjecture).

- E431: why a chain ends; cascade run for L's counterexample in Lean; symbolic displacement beyond 1/16 or for arbitrary grids (E432 pair law, E433 grid pair law); stage-1b rows.

- E432: v9 rewording (E436 v10); grids other than the AP (E433); Lean statements that classes 1, 3, 5 hold the whole interval at c/20; linking `pds d` to an arrangement.

- E433: subjects with runners on both sides; link from `ClassHyp` to an explicit deviation bound depending on the offset range.

- E434: `StrongGate`/L1(d) (E435 reduces to `FiveReach`, OWED); why a1 = 3, 4, 5 have no crosser ("Not explained"; E435, E436 not proved); cycle, grand return, D_min grid-to-grid (E435 `Cycle.lean`; E436 `GridToGrid.lean`); the finite set of goal G2 "not yet identified".

- E435: `FiveReach`; different-d grid-to-grid (E436); minimality of the isolation period; whether the owner means absolute speeds or disparities.

- E436: `FiveReach`/`ReachFourSharp`/`ReachFiveSharp`; `NoSmallIntegerCrosser`; `ReadingsAboveFifteenSevenths`; multi-runner narrow-cell criterion (E438 `typeX_iff_cover`, exact general form; three-or-more-zone condition owed); where the landing falls after u in the past-the-cell case (E438 `landing_iff_first_open_cell`); completeness of Z1's cell list; d'/d with higher 2-adic valuation.

- E437: `PathLonelyBound`, `SuccessorIsolation` (E438 classifies: restatements or caps); no escape at an arrangement; why a further cell exists at every touch; why 27 PERSIST-BOTH-SWAP events occur at AP-symmetric parameters ("Not derived").

- E438: `ConjectureGivesBound`; exact condition for covers by three or more zones; rank 2 and higher touch-only search; whether a touch-only arrangement can host an escape.

- E439: touch positive dependence for general arrangements; second-order case σ = 0 (E440 `affine_survival_classification`, `sigma_zero_nonaffine` at the AP pair); whole-set no-partner example (E440 `wholeset_conjugate`: a conjugate always exists); the covering route (E440 stated as transversal); `ConjectureGivesBound`; `FiveReach`; `NoSmallIntegerCrosser`.

- E440: touch positive dependence for general arrangements; transversal-existence (the conjecture); cell-count structure (2·pairs + [all odd]) in Lean; an account of the two-cell sets; uniqueness of the lonely instant near a/8 at σ = 0; no bound on N. Not discharged.

- E441: `CompatAll`; fail set for c above 48; proof that rank 1 forces lap 0 (E442: equivalent to R* below 9, and false beyond N = 22 populations: 5 sets at Q = 5, 42 at Q = 7); the landing as the cascade from η_C in Lean (E442 `isMove_gate`).

- E442: `CompatAll`; the escape alternative at an arrangement (`PathLonelyBound`, `ConjectureGivesBound`); the owner's second option (comparison across n); `FiveReach`; `NoSmallIntegerCrosser`; stage-1b rows other than the two decided in E436; replacement of `IsGridWithDeviation`; why a chain ends (the conjecture).

## 6. ARBITRARY TO FINITE

- E385: finite/decidable case Z (some six-subset gcd > 1) with a counting-tool proof [PROVISIONAL: counting tool]; complement R infinite, contains the AP; "a map of a derived condition, not a coverage claim"; exhaustiveness for R owed.

- E386: case list for every arrangement: ≤ six readings [L]; spread ≤ 7 [L]; spread in (7,9] [L]; spread > 9 `WideStep8 M` [OWED], and `WideStep8 1` false at X24. Connecting route `lonelyRunnerAt8_of_wideStep8 M : WideStep8 M → LonelyRunnerAt8` [L]. Not covered: spread > 9.

- E387/E394: gate crossers' middle readings 2..6 in a bounded box identical at J = 1,2,3 [TREE: float-LP ranges]; R8 [L] bounds ρ7 ≤ 7ρ6; finite crossing family (E376–E377) named as the content of window B. Lemmas L-B1, L-B2 tested, not derived; L-B3 [L].

- E392: extended case Z: subset A (m ≤ 6, gcd g) with Σ ⌈q_b/4⌉/q_b < 1 ⇒ lonely [P by hand, PROVISIONAL: counting tool]. Not covered: sets with no such subset (the AP), sets with sum ≥ 1.

- E393/E400: `EightResidual` shapes {(1,6), (2,5), (3,4), (4,3)} (first nine fields; 22 fields in total by E400). (4,3): every residual set lonely at 1/8, `lonely_eight_of_residual_four_multiples` [L]. Residue patterns mod 8 of the non-multiples (finite): (4,3) 10; (3,4) 155; (2,5) 381; (1,6) 812; type-level and drop arguments [PROVISIONAL: covering; P by hand; enumeration exhaustive]. Not covered after E400: (3,4) (o,o,o,o) 35 and (o,o,t,t) 18; (2,5) 351; (1,6) 782.

- E397: dead-flank minimal-cover types: 2,470 distinct types at readings ≤ 20, "many and not a short list"; classification is of covering systems, "not a finite short table". "Not all seven dead" [TESTED] on [1,20] and [1,24]; not proved.

- E399: record's finite lists: 4,413 pinned census families and 62 one-parameter families in Lean (`decide`), eighth family for every real x in (0,8); shadowing-triples list open ((2,5,c) passes the residue count for every c).

- E402/E404/E406: reach of Lean cases over the finite residue-pattern lists: (4,3) 10/10; (3,4) 102/155; (2,5) 162/381; (1,6) 142/812 (242 with M(1,3), conditional) [L for the cases; counting steps PROVISIONAL]. Left (E402 list): four or more odd readings ((3,4) (o,o,o,o); (2,5) (f,o,o,o,o), (o,o,o,o,o), (o,o,o,o,t); (1,6) (f,f,o,o,o,o), (f,o,o,o,o,o), (f,o,o,o,o,t), (o,o,o,o,o,o), (o,o,o,o,o,t), (o,o,o,o,t,t)) and exactly two odd with ≥ two ≡ 2 mod 4 coverable ((3,4) (o,o,t,t), (2,5) (f,o,o,t,t), (1,6) (f,f,o,o,t,t) with both odd in one pair class; (2,5) (o,o,t,t,t); (1,6) (f,o,o,t,t,t), (o,o,t,t,t,t)).

- E403/E405: inside (3,4) tight patterns, `lonely_eight_of_grid` [L; PROVISIONAL: counting tool] covers every set (residual or not) with an odd non-multiple dividing no cofactor; not covered: the divisible family (non-empty in the residual; 238 of construction B not separated at ratio 9, so `ArrBlockRule8 3 9` (owed) would not reach them), and the (o,o,t,t) remainder.

- E407: `lonely_eight_of_descent_mod` [L; counting steps PROVISIONAL]: any set with at most six readings divisible by q and the budget condition. On the stored lists what no rule settles is 162 + 75 members, all of the shape one slow reading against six (s1/s0 ≥ 9), `ArrBlockRule8 6 9` owed.

- E409: every split of four numbers M(4,0)…M(0,4) has a proof (grades as in section 1); (1,6) 242 of 812 patterns.

- E411: finite candidate list: twelve cores (each core reading at most 14) with their seventh readings — (1,2,3,4,5,6)+{7,14,21,28,35,42,49}; (1,2,3,4,5,7)+{12,18,24}; (1,2,5,6,7,8)+{39}; (1,3,4,5,6,7)+{11}; (1,3,4,5,6,9)+{28}; (1,3,4,5,7,11)+{12,18,24,30,36}; (1,3,4,5,7,13)+{18}; (1,3,4,5,13,14)+{18}; (1,4,5,6,7,10)+{11}; (1,4,5,6,7,11)+{13,16,23,26,29,39,52}; (2,6,7,8,10,13)+{14}; (2,7,9,11,12,13)+{20}. Connecting statement: "the sets with no lonely instant at 1/7 are the twelve cores with their seventh readings" [OBS] on [1,52]; if it holds for all windows, a set that is not fast has d₇ ≤ 98, a finite list, each with δ ≥ 1/8. Not covered: the classification itself is owed, "strictly stronger than order eight", not derived.

- E419/E420: integer boxes in ratio space with exact certificates: arc criterion holds for 20625/2873 ≤ ρ_min, ρ_max ≤ 16 [TREE: every prune an exact certificate]; one 28-move FAIL cell below; two-arc statement holds on the cube [6,12] [TREE, exact]. With `lonely_cons_of_arc`, `takeover_of_lonely_at` [L] these are existence statements at 1/7 for those boxes only [PROVISIONAL: covering]. Not covered: unbounded ρ_max (scale reduction, architecture §4), ρ_min < 6, completeness of the branching rule not independently re-implemented.

- E423/E425: finite count patterns: `lonely_eight_or_residual_open` [L]: a whole-number set (positive readings, at most seven, no common factor g ≥ 2) is lonely at 1/8, or is an `EightResidual` member with open counts. Settled 10/10, 102/155, 162/381, 242/812 (`decide +kernel`; "a consistency check between two encodings", not a cascade statement). Not covered: open patterns 53 of 155 (m = 3), 219 of 381 (m = 2), 570 of 812 (m = 1); no Lean theorem ties a set to its residue pattern; pattern-by-pattern agreement is not a Lean theorem.

- E426/E428: owed case families listed: `ArrBlockRule8 f 9` for f = 3..6, `ArrBoundedCovered8 9`, the `EightResidual` obligation; E428 verdicts `ArrBlockRule8`, `ArrBoundedCovered8` undecided (owner words cited: M060 find the finite set first; M077 a finite set once d_min, d_max and scale are removed).

- E427: 1,534 distinct slot/ε signatures of chains in 345,304 sets [OBS]; descriptive counts, no mechanism.

- E434: type counts over all gcd-1 7-subsets of {1..N}, N ≤ 56 [OBS]: full types do not settle (infinite, `firstMove_lap` [L]); rank words do not settle; coarse class without ties 37 (N = 19..44), 39 (N = 48), 41 (N = 56). Entry's statement: a finite rank-word set for all arrangements is a move cap (rule 7 shape) [reasoned]; "The finite set the goals ask for (G2) is therefore not yet identified; it is not the full type, the rank word, or the coarse class as counted here."

- E436: crossers are exactly a union of open polyhedral cells given by setter-lap patterns (`crosser_iff_pattern`, `crosser_iff_linear_pattern` [L]); 337 cells found with exact rational vertices [OBS]; list "not proved complete" (extended twice by uncovered random crossers); crossing region not bounded. Block rule: no threshold T0(f) fixes the landing [OBS]; block decomposition `BlockLanding.lean` [L] (conditional on a lonely point existing).

- E438: touch-only integer 7-sets with entries ≤ 28: exactly three [OBS, exact, finite families]; not a classification.

- E439/E440: touch-only sets: among all 18,643,560 integer 7-subsets of [1,40], 11, all scalings of three primitive sets (AP (1,…,7), (1,2,3,4,5,7,12), (1,4,5,6,7,11,13)); same three among rational sets a/Q, Q = 2..5 [OBS]; "a theorem classifying them is not available".

- E440: `exists_lonely_iff_transversal` [L; PROVISIONAL: covering]: an isolation exists iff a transversal exists (each side is the conjecture); no stage-wise invariant found [OBS].

- E441: `compat_iff_exists_lonely` [L]: existence iff `Compat` ("makes nothing easier"); `CompatAll` OWED. Rare landing classes (p mod 8 = 7, 5, 3) are finite lists at N = 22 (2, 4, 14 admissible (x,k) pairs; 2, 3, 7 realised) [OBS]; rarity is a population effect.

- E442: `dev_scale` [L]: δ unchanged under common scaling (a rational set is cascade-equivalent to its numerator set); generic sets have only positive-width cells; non-generic parameters on an affine path countable. Not covered: existence; the escape alternative.

