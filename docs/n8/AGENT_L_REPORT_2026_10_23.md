Rules: 5 (no runner stationary; all readings positive), 7 (no existence-shaped argument offered; pruning is a necessary-condition filter, not a proof form), 8, 15 (exact integers/Fractions; floats only as display or search steer), 18 (grades), 21 (new files only, nothing edited, nothing committed).

# Agent L: tight points of g* at order 8 (seven readings), extended search, slack structure, slack over U

Grades: [P] = exact computation, complete for the stated range; [OBS] = exact values at sampled points; [OWED] = not established.
g*(r) = max over t>0 of min_i distInt(r_i t). For integer readings the period is 1 and the maximum is attained at t = m/q, q in {2 r_i, r_i + r_j, |r_i - r_j|}.

## 0. Files (all new, in experiments/n8/, prefix tight_)

- tight_enum_v1.c (exhaustive search), outputs tight_enum_N150_d27_200.out, tight_enum_N70_N7_3000_d27_200.out, tight_enum_N100_d1_7.out, tight_enum_N80_d1_6.out
- tight_gstar_lib.c (exact g* of an integer vector, C, integer arithmetic), tight_slack_v1.py (+ outputs tight_slack_single_v1.out, tight_slack_pairs_v1.out, tight_slack_full_v1.out), tight_plateau_v1.py/.out, tight_line_v1.py/.out, tight_maximisers_v1.py/.out, tight_torus2_v1.py/.out, tight_slack_U_v1.py/.out
- tight_gstar_lib.dylib is a build product of tight_gstar_lib.c.

## 1. Extended tight search [P]

Method. DFS over r_1 < ... < r_7. Pruning is a certified necessary condition, not a heuristic: for a prime M = 8191 > every reading, every grid time t = a/M with all seven distInt(r_i a/M) >= delta certifies g* >= delta. Each reading covers exactly c grid points (a -> r a mod M is a bijection), so a set can have g* < delta only if the grid-uncovered set is empty; a 6-prefix whose uncovered count exceeds c, or a 7th reading failing a bit test, is discarded. Survivors with gcd 1 get g* by exact integer arithmetic (candidate times above) and are kept iff g* < delta by integer cross-multiplication. The N=22 run reproduces the lead's 13 sets exactly (same values, same vectors); the lead's u_tight_integers_v2 list is a subset check that passes.

Range reached, with delta = 27/200 (g* < 1/8 + 1/100):
- all gcd-1 subsets of {1..150}: C(150,7) = 294,109,729,200 subsets, 1.37e10 depth-6 nodes visited.
- r_1..r_6 <= 70 and r_7 <= 3000 (a far last reading).
- N = 40, 60 also run (same list).

Result, identical for N = 22, 40, 60, 70 (r_7 <= 3000), 150: exactly 16 subsets with g* < 27/200:

| g* | vector | in U |
|---|---|---|
| 1/8 | (1,2,3,4,5,6,7) | yes |
| 1/8 | (1,2,3,4,5,7,12) | yes |
| 1/8 | (1,4,5,6,7,11,13) | yes |
| 3/23 | (1,2,3,4,5,7,18), (1,3,4,5,7,13,18) | yes |
| 2/15 (11 sets) | (1,2,3,4,5,6,14), (1,3,4,5,6,7,11), (1,3,4,5,7,11,12), (1,3,4,5,7,11,18), (1,3,4,5,7,11,24), (1,3,4,5,13,14,18), (1,4,5,6,7,10,11), (1,4,5,6,7,11,16), (1,4,5,6,7,11,26), (1,4,5,6,7,11,39), (2,6,7,8,10,13,14) | yes, all |

Tight (g* = 1/8) subsets of positive integers with gcd 1 and largest reading <= 150: exactly the three known; none new. Rational scale-free arrangements clear to integer vectors with gcd 1, so this covers every rational reading vector whose cleared form has height <= 150 (and, with the last reading free, r_1..r_6 <= 70, r_7 <= 3000). Not covered: heights above these bounds; irrational vectors (section 3).

Lower g* levels: the sets with g* < 1/7 for N <= 100 (40 sets) are in tight_enum_N100_d1_7.out; 31 lie in U, 9 do not (smallest g* outside U: 6/43). The values below 1/7 include the family (1,2,3,4,5,6,7k) with g* = k/(7k+1) for k = 1..6 observed (1/8, 2/15, 3/22, 4/29, 5/36, 6/43), tending to 1/7 = g*(1,2,3,4,5,6). The next distinct values above 1/8 are 3/23, 2/15, 5/37, 3/22, 4/29, 9/65: the nearest value above 1/8 is 3/23, a gap of 1/184, and no value accumulates onto 1/8 from above among heights <= 150.

The three tight vectors: exact maximising times in (0,1] are t* in {1/8, 3/8, 5/8, 7/8} for all three (tight_maximisers_v1.out); the active pairs at 1/8 are readings (1,7); at 3/8 they are (3,5) for AP and T1 and (11 | 5,13) for T2.

## 2. Slack growth near each tight point [OBS, exact]

Claim to retire: g* - 1/8 does not grow linearly with the distance from a tight point. It jumps. Evidence (g* of the integer vector D*T + k, exact, D = 64, 256, 1024):

(a) One reading moved by +-j/D, j/D from 1/1024 to 1/4 (tight_slack_single_v1.out). The slack is independent of the radius, the sign and D, equal at every radius tested:

| moved reading | AP slack | T1 slack | T2 slack |
|---|---|---|---|
| 1 | 7/72 | 7/72 | 15/136 |
| 2 | 5/88 | 5/88 | - |
| 3 | 5/88 | 15/136 | - |
| 4 | 1/8 | 7/136 | 1/8 |
| 5 | 3/40 | 3/40 | 3/40 |
| 6 | 1/24 | - | 5/24 |
| 7 | 1/56 | 3/104 | 1/16 |
| 11 / 12 / 13 | - | 1/24 (12) | 5/88 (11), 3/104 (13) |

The minimum single-reading slack is 1/56 (AP, reading 7), 3/104 (T1, reading 7), 3/104 (T2, reading 13); that is g* = 1/7, 2/13, 2/13.

(b) Mechanism, checked by tight_plateau_v1.py (D = 1024, random moves |k| <= 24): moving one reading by any nonzero rational detaches it from T's closed orbit (the moved reading's phase becomes free over t up to ~1/|e|), so g*(T+e) = g*(T without that reading). This matched exactly in 7/7 single-reading cases for each of AP, T1, T2. For two moved readings it matched in 19/21 (AP), 21/21 (T1), 19/21 (T2); for three, 27/35, 26/35, 19/35. The mismatches go to a different value (sometimes below the plateau, still above 1/8): readings that are moved together by commensurate amounts stay coupled to each other and form a second block (g* = min of the two blocks' values).

(c) Two readings moved (tight_slack_pairs_v1.out, all 21 pairs, rings of sup-norm j/D, D = 64 with j = 1,2,4,8; D = 256 with j = 1,2,4,8; D = 1024 with j = 1,2,4): minimum slack on every ring equals the smaller of the two single-reading plateaux; zero-slack ring points: 0 in all rings listed.

(d) Seeded random full 7-reading perturbations (tight_slack_full_v1.out; D = 64: 3000 per radius j/D, j = 1,2,4,8; D = 256: 1500 per j; D = 1024: 600 per j, j = 1,2,4): negative slack: 0 of 59,400 samples (so no counterexample to g* >= 1/8); slack exactly 0: 0 of 59,400. Minimum sampled slack per radius: AP 1/56 at radius 1/64 and 1/256, 1/24 at 1/1024; T1 3/104, T2 3/104; the minimum is at the plateau values of (a), not shrinking with the radius.

(e) Line through each tight vector (tight_line_v1.py: last reading r_7 -> r_7*(p/q), q <= 24, 1074 values): for k = p/q within 10% of 1 and k != 1, the minimum g* is 1/7 for AP, 1/6 for T1, 2/13 for T2. The curve is g*(1) = 1/8 and at least these plateaux for every k != 1 at q <= 24. For integer k the AP line gives k/(7k+1), rising to 1/7.

Reading of this: g* is not continuous at the tight points (as a function on real vectors it is only lower semicontinuous: g*(T) <= liminf). The relevant quantity is not "slack over distance" but "no non-trivial rational neighbour has g* below the plateau": in the exhaustive lists, the nearest non-tight vector with g* < 1/6 to each tight vector (N = 80, tight_slack_U_v1.out) has spread 78/77 from AP with g* = 1/7 (vector (11,22,33,44,55,66,78)), 43/42 from T1 with g* = 2/13, 79/78 from T2 with g* = 2/13; these are the single-reading plateaux. Flat directions (directions in which g* stays exactly 1/8): none found other than the trivial rescaling e proportional to T. For the exhaustive range this follows from section 1 (any rational T+e of height <= 150 with g* = 1/8 would be a fourth tight vector); for the sampled larger-denominator perturbations it is [OBS]. The first-order local computation is not offered as a result: at a maximising time t* the exact crossing value of the pair (i rising, j falling) is 1/8 + t*(r_j e_i - r_i e_j)/(r_i + r_j) [derived by hand, not run], which is zero to first order along e_2, e_4, e_6 for AP, yet the exact g* is positive there because far times t ~ 1/|e| supply the gain; the exact data in (a) is the authority.

## 3. Slack picture over U [OBS for the minimum, exact for the points listed]

Distance. In log-reading coordinates modulo overall scale, d(r,T) = (max_i ln(r_i/T_i) - min_i ln(r_i/T_i))/2; "outside the ball of radius rho" is tested exactly as the rational spread s = max_i(r_i/T_i)/min_i(r_i/T_i) >= e^{2 rho} through a six-digit bracket of e^{2 rho}; no point fell inside a bracket.

Exact min of g* over the enumerated rational vectors (all gcd-1 vectors of height <= 80 with g* < 1/6; 26,390 vectors, 26,159 in U), in U, outside the balls around all three tight vectors:

| rho | min g* | minimisers |
|---|---|---|
| 0.2 | 3/23 | (1,2,3,4,5,7,18); (1,3,4,5,7,13,18) |
| 0.1 | 3/23 | same |
| 0.05 | 3/23 | same |

The value is the same at all three radii because every other vector in U with g* between 1/8 and 3/23 does not exist in the enumeration (section 1: nothing between 1/8 and 3/23 up to height 150), so even removing no ball the minimum over U minus the three points themselves is 3/23. Where the minimisers sit: (1,2,3,4,5,7,18) is T1 with the last reading moved by the factor 3/2 (spread 3/2 from T1, i.e. distance (1/2)ln(3/2) ~ 0.2027, just outside the rho = 0.2 ball; spreads to AP and T2 are 18/7 and 36/13); (1,3,4,5,7,13,18) has spreads 18/7, 13/7, 24/13 (display) to AP, T1, T2, so it is far from all three. The second-lowest level 2/15 is attained by 11 vectors (list in section 1), the nearest to a tight vector being (1,4,5,6,7,10,11) at spread 13/11 from T2 (distance ~ 0.083, inside the rho = 0.1 ball).

Within each ball the minimum over non-tight points is the plateau of section 2 (1/7 for AP, 2/13 for T1 and T2 at heights listed), which exceeds 3/23. So min over U minus the tight points ~ 3/23 at height <= 150 regardless of rho, and the "slack away from the tight point" is 3/23 - 1/8 = 1/184 for the lowest vectors but these lie at distance >= 0.2.

Real (non-rational) vectors. A real vector's g* is the max of min_i distInt(x_i) over the closure of its orbit, a subtorus. Vectors whose readings lie in Z + Z*alpha have a 2-dimensional closure. tight_torus2_v1.py samples 7,320 and 7,408 such vectors in U (alpha ~ 144/233 and 233/377 as rational approximants, exact g* of the approximant, readings n_i + m_i alpha with 0 <= n_i <= 9, |m_i| <= 4): none has g* < 1/7. The 1-dimensional closures are exactly the rational vectors covered by the enumeration. Vectors with a split into independent blocks give g* = min of the blocks' values, each at least 1/(block size + 1) >= 1/7 by the order <= 7 theorem [derivation, not run]. Not established: any lower bound on g* over U minus balls for heights above 150, or over all irrational closures.

## 4. Summary and what it suggests

- Tight points: three (1,2,3,4,5,6,7), (1,2,3,4,5,7,12), (1,4,5,6,7,11,13) among all gcd-1 integer vectors with height <= 150 (and r_7 <= 3000 with r_1..r_6 <= 70). All lie in U: AP satisfies 7 < 42, 6 < 60, 5 < 108; T1: 12 < 49, 7 < 60, 5 < 108; T2: 13 < 77, 11 < 84, 7 < 162. The next level above 1/8 is 3/23, then 2/15; all 16 sets with g* < 27/200 lie in U.
- Slack growth: no linear growth. g* jumps from 1/8 to at least the single-reading plateau (1/7, 2/13, 2/13) for every sampled nearby rational vector, independent of the size 1/1024..1/4 and of D; the plateau is g* of the six-reading sub-vector. No flat direction apart from rescaling was found.
- Slack elsewhere: minimum 3/23 (1/184 above 1/8) at two vectors at distance >= 0.2 from the tight points; every other enumerated vector is at 2/15 or higher.
- Proof-strategy reading (suggestion, not a result): the problem splits into (i) a local statement at each of the three tight vectors, whose natural form is "every rational vector within spread 1+eta, other than a multiple of T, has g* >= plateau", proved by the decoupling mechanism: the moved readings leave T's orbit and the unmoved block has g* >= 1/7 by order 7 (this uses the native order-7 theorem, and needs the coupled-block exceptions of section 2(b) handled); and (ii) a slack lemma away from the three points, g* >= 3/23 or merely > 1/8 on U minus the balls. The slack lemma is the open one: 3/23 is the exact minimum only over enumerated heights; whether a smaller value exists at larger heights is [OWED].

## 5. Not established

- Completeness above height 150 (and above r_1..r_6 <= 70 with r_7 <= 3000); irrational closures other than the random 2-dimensional sample.
- That the plateau equality in 2(b) holds for every perturbation (checked on 3 x 7 single-reading cases at D = 1024 and sampled elsewhere; the mismatching multi-reading cases are listed in tight_plateau_v1.out).
- That g* >= 1/7 on a full punctured neighbourhood of each tight vector: shown for the enumerated vectors and the sampled perturbations only.
- The sampled minima over directions at each radius are minima over samples, not lower bounds over all directions.
