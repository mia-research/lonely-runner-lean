# Step rules of the cascade (v1)

Files: `pred_lib_v1.py` (generators, independent zone enumeration), `pred_step_rules_v1.py/.out` (main run), `pred_features_v1.py/.out` (survey re-run, long-path features), `pred_extra_v1.py/.out` (zone-pointer chain, same-lap check, search for reading 1 as a blocker). Raw counters: `pred_step_rules_v1.pkl`.
Counter keys that never fire do not print in the `.out` files; every `*_viol` name in the lists below is a counter in the code and its value is 0 unless stated.

## Samples
Main: 50,000 exact arrangements, 131,659 steps, from six generators (each is a function in `pred_lib_v1.py`):
random (6,000), AP deformed (6,000), strip_multi: readings in strips (8j-1,8j+1) for j in {1..5}, 2-6 of them (8,000), first_strip: 3-6 readings in (7,9) (4,000), chain: each new reading is drawn so that the previous exit R2 lies in one of its zones (22,000), climb: hill-climb on the number of moves from a strip_multi start (4,000). Moves per arrangement: 0:6343, 1:10351, 2:9716, 3:8707, 4:6794, 5:4093, 6:2034, 7:905, 8:496, 9:279, 10:151, 11:68, 12:63. Arrangements with >=5 moves: 8,089.
Survey: the 20,000 in `outcome_survey_v2.pkl` (20,511 steps, up to 12 moves; 0:7307, 1:8202, 2:2634, 3:1059, 4:411, 5:226, 6+:161).
Fresh run for the extra checks: 60,000 arrangements (101,609 steps) plus the survey.

## (a) Which blocker is the setter
State R, reading y, lap j_y = round(R rho_y / 8), p_y = R rho_y - 8 j_y. y blocks iff |p_y| < 1. Exit e_y = (8 j_y + 1)/rho_y = R + (1 - p_y)/rho_y.

Rule A. Setter = the blocker maximising (8 j_y + 1)/rho_y, i.e. the largest R-jump (1 - p_y)/rho_y. Pairwise form: blocker a beats blocker b iff (8 j_a + 1) rho_b > (8 j_b + 1) rho_a. Depends on (rho, j) of the blockers only.
- Checked against an independent enumeration of all zones (y, j) containing R (not using `path`): blocker set and laps equal `path`'s (A1_viol 0, A1b_viol 0); setter attains the maximal exit (A2_viol 0); pairwise form (pair_viol 0). Ties in the maximal exit between two readings: 0 in 131,659 + 20,511 steps. Landing R* is contained in no zone (landing_viol 0).
- Counts: main 131,659 steps, survey 20,511 steps, fresh 101,609 steps (samelap/mixedlap steps). All 0 violations.
- A2c, A2d, markov, ratio_test are identities in the exit formula (they restate R2 = (8j+1)/rho, R-jump = (1-p)/rho); they are listed as arithmetic checks, 0 violations, and carry no empirical content.

Rule A', the lowest-rank rule (the established 97% rule), made exact. Let x = lowest-rank blocker.
- If every blocker is on the same lap, the setter is x. Fresh run: 55,745 + 14,094 (survey) such steps, 0 failures (samelap_LR_viol 0).
- Single blocker: trivial (65,165 steps in the main sample).
- A blocker y beats x only if y is faster than x and j_y > j_x and (8 j_y + 1) rho_x > (8 j_x + 1) rho_y. Main sample: lowest-rank rule fails in 9,753 of 131,659 steps (7.4%; 4,703 of them at the first step); survey 1,273 of 20,511 (6.2%). In all 11,026 failures the setter is faster than x with a strictly higher lap (fail_char_viol 0). Lap gap j_y - j_x in the main failures: 1:5033, 2:2270, 3:1230, 4:685, >=5:535. Failures occur only with >=2 blockers (LR_viol 0): blocker count 2:5012, 3:2731, 4:1145, 5:571, 6:294.
- Setter's position when blockers are sorted by rank (main): lowest 121,906; second 8,255; third 1,236; fourth 216; fifth+ 46. So the lowest-rank blocker or the next one is the setter in 98.9% of steps; the rest needs the exit comparison.
- The 7.4% comes largely from the chain and climb generators, which put several readings on different laps into one state. The survey's own rate here is 1,273 of 20,511 steps (6.2%), against the 330 of 12,303 (2.7%) in the task statement; the step sets differ (the 12,303 subset is not identified in the files given) and I did not reconcile the two.

Depth of the rule. The state after a move is R2 = e(Z_k), a function of the previous setter's zone Z_k = (y, j) alone, and the next setter is argmax of exit over the zones containing R2. Zone-pointer chain: starting from the zones containing R0 and iterating "zone -> max-exit zone containing its exit", carrying no R, reproduces the whole (setter, lap) sequence and the landing in all 60,000 fresh arrangements and the 20,000 survey (chain_viol 0). So a rule with history length 0 beyond the current setter's zone suffices; lookahead is not required for the next step, and the n-th step needs n applications of the pointer.

## (b) Link rule after a move to R2 = (8 j_s + 1)/rho_s
Reading y != s blocks R2 iff dist((8 j_s + 1) rho_y/rho_s, 8Z) < 1 (ratio_test_viol 0: identical to the direct test). Its lap there is j_y = round((8 j_s + 1) rho_y/(8 rho_s)).
- Slower (rho_y < rho_s): j_y <= j_s. Violations 0 over 44,148 new slower blockers in the main sample (link_viol_slower 0; the survey run has 5,999 slower and 3,858 faster, also 0). Same lap j_s: 22,468 (main); lower lap: 21,680. A slower reading on lap j_s needs rho_y/rho_s > (8 j_s - 1)/(8 j_s + 1) (window_viol 0).
- Faster (rho_y > rho_s): j_y >= j_s + 1 (link_viol_faster 0, 92,051 main instances); lap difference 1:18,590, 2:16,988, 3:16,190, >=4:40,283.
- The setter itself does not block R2 (open zone; setter_still_blocks_viol 0).
- A reading that blocked at R and blocks again at R2 is on a strictly higher lap (returned_lap_viol 0; 9,536 main instances); the other 126,663 new blockers were clear at R. A reading's lap never decreases along the path (lap_decrease_viol 0).
- The next setter is slower than the current one in 38,095 steps and faster in 49,907 (main); the same reading never sets twice in a row (0 in the >=6-move paths; for reading y the next lap is strictly higher by the link rule).

## (c) Inert readings
Object: reading y is "inert for blocking" if it blocks at no visited state, "inert for setting" if it is no setter.
- Rank 1 (rho_1 = 1, d_min): never a blocker and never a setter in 70,000 arrangements (main + survey). Largest visited R in all samples: 5.03 (normalised so rho_1 = 1), below the 7 that rho_1 needs to reach its first zone (7,9). Hill-climb on the largest visited R from chain starts, 2 processes x 240 s (436,000 evaluations): best 4.73, no arrangement where reading 1 blocks (`pred_extra_v1.out`). The sufficient criterion is therefore "reading y is inert if the cascade never reaches 7/rho_y"; for y = 1 it is 0 violations in this search; it is not proved here that R stays below 7.
- Zone-closure criterion (readings only, no stepping of R): zones containing R0 are active; if Z is active and the exit e(Z) lies in zone Z', Z' is active (all branches, no max rule). Readings with no active zone are inert for blocking. Soundness: every visited blocker zone is in the closure (closure_zone_viol 0, closure_reading_viol 0 over 50,000 + 20,000; the cap on R was 3,000 and was never hit, closure_over 0). Slack: closure holds 281,737 zones, visited blocker zones 255,746 (9.2% extra); readings in closure but never blocker 13,365 of 229,870 (5.8%). Survey: 534 of 36,732.
- No strip reading <=> no move: strip0 == 0 and n > 0: 0; nstrip == 0 and n > 0: 0; nstrip > 0 and n == 0: 0 (70,000 arrangements). Arrangements with no strip reading have all 7 readings inert.
- Exact set of setters: the orbit of the zone pointer in (a) (pointer chain, 0 violations). I did not find a closed-form readings-only test that is tighter than the closure and exact; the pruned (max-only) closure is the pointer orbit itself.
- Inert-for-setting rates by rank (main + survey, 70,000 each): rank 1: 70,000; 2: 36,172; 3: 45,487; 4: 47,962; 5: 48,398; 6: 48,441; 7: 49,568. Inert-for-blocking: rank 1: 70,000; 2: 32,774; 3: 29,523; 4: 28,256; 5: 26,849; 6: 25,403; 7: 24,492. Blocker-but-never-setter readings: 92,617 in the main sample (dominated at every state it was met).

## (d) Number of moves, long paths
Moves distribution: see Samples. The generators control the tail, so only comparisons within a generator are meaningful. In the unbiased survey (families random, AP deformed, grid+laps, clump, strips): 0:36.5%, 1:41.0%, 2:13.2%, 3:5.3%, 4:2.1%, 5:1.1%, >=6:0.8% (161).
Long paths (>=6 moves; 3,996 main, 161 survey):
- Distinct setters 4-6 (main: 4:148, 5:1723, 6:2125); moves beyond 6 need a reading to set twice, on a higher lap. Repeats (moves - distinct): 0:674, 1:1742, 2:915, >=3:665. The setters are always ranks 2-7.
- Number of readings in a strip at R0 (strip0): 1 or 2 in 76% of the main long paths (1:1542, 2:1482, 3:716, 4:199, 5:48, 6:9). P(>=6 moves | strip0 = k) falls with k: survey 90/5787, 43/2949, 15/1499, 7/1014, 2/841, 4/603 for k = 1..6; zero for k = 0 (no moves at all). A large first jump to the maximal exit passes the later zones.
- Readings in (7,9): 0:1842, 1:1954, 2:192, 3:8, none with 4+. Survey: 0:41, 1:93, 2:25, 3:2.
- Consecutive setters alternate in direction: faster 12,049, slower 12,069 (main); survey faster 325, slower 604. Setter laps on long paths spread over 1-12 (lap 1: 4384, 2: 4230, 3: 4565, 4: 3746, 5: 3351, 6: 3141, 7: 2241, 8: 1538).
- R_end/R_0 on long paths: 1.3-3.0 by family (mean); the largest visited R is 5.03.
- Shared structure (observed): each setter's exit lies in a zone of the next setter (that is the definition of the chain), with the next reading near a fixed ratio to the current one: rho_next/rho_s about (8 j_next +- 1)/(8 j_s + 1), which is what the link rule restricts; arrangements built by choosing readings along such ratios (the chain generator) produce 6+ moves in 1,840 of 22,000 main draws against 62 of 6,000 for AP-deformed and 40 of 6,000 for random.

## Exceptions and failures
- Rule A, link rule, pointer chain, closure soundness: no violation in any run.
- Lowest-rank rule fails in 6-7% of steps (characterised above, 0 steps outside the characterisation).
- Closure over-approximates blocking by 5.8% of readings: it cannot be used as an exact test of "visited".
- Rank-1 inertness rests on max R = 5.03 over all samples and the 436,000-evaluation search; it is not a derived bound.
- Generator coverage: the longest path found is 12 moves (63 main + 2 survey); no generator was aimed at paths longer than the climb reaches (hill-climb on moves gives up to 11-12). Absence of paths with more than 12 moves is not claimed.
- The 12,303 / 330 figures given in the task were not reproduced; the file totals differ (see (a)).
