# Lattice arrangements: exhaustive enumeration (v1)

Scope after owner guidance (2026-10-03): one family, integer 7-subsets {s=a_1<...<a_7}, gcd = 1, readings a_i/s (halves and thirds are s=2, s=3; gcd 1 excludes common multiples). Novelty is by path word against the J2 known set (`terminals7_J2.pkl`, 140,727 distinct paths, rho_7 <= 17; J1's 12,599 paths are a subset).
Code: `lat_enum2_v1.py` (path() verbatim; closer/opener/width code reproduced from outcome(), 0 mismatches in 5,000 random exact comparisons), `lat_chain_v1.sh`, `lat_analyse_v1.py`, `lat_known_v1.py`. Logs/state: `lat_enum2_log_v1.out`, `lat_state2_s{1,2,3}_v1.pkl`, `lat_known_paths_v1.pkl`. An earlier s=1 run to a_7 <= 32 (`lat_enum_v1.py`, `lat_state_m1_v1.pkl`) agrees (11,848 path words at a_7 <= 32).

## Exhaustive families (every count below is exhaustive over its family, all arithmetic Fractions)
- s=1: all 3,262,623 sets 1<a_2<...<a_7<=40 (rho_7 <= 40).
- s=2: all sets 2<a_2<...<a_7<=44 with gcd 1: 5,191,522 computed, 54,264 excluded by gcd (rho_7 <= 22).
- s=3: all sets 3<a_2<...<a_7<=45 with gcd 1: 5,242,783 computed, 3,003 excluded (rho_7 <= 15).
Not reached by this search: any s >= 4; s=3 with rho_7 > 15; s=2 with rho_7 > 22; s=1 with rho_7 > 40. The "large s, fine ratios" and rho_7 in (22, 60] regions are not covered.

## Key results (details and per-step tables below)
1. Hole check (completeness): every arrangement with rho_7 <= 17 in the three families (s=1: a_7<=17; s=2: a_7<=34; s=3: a_7<=45 i.e. rho_7<=15) has its path in the J2 set. Distinct path words not in J2: 0, 0, 0. Not reached by this search: a hole in the tree at those lattices. The families reach 407 (s=1), 5,511 (s=2), 5,446 (s=3) of the 140,727 known paths.
2. New regions (path not in J2, rho_7 > 17): s=1: 37,411 words (rho_7 in 18..40); s=2: 8,932 words (rho_7 in (17,22]); s=3: none exist in range. 8,025 of the s=2 words are in neither J2 nor s=1's words. Across s=1,2,3: 57,578 distinct path words, 3,484 occurring for more than one s.
3. Stabilisation (s=1, N = 12,16,...,40; table below): the pair set (opener rank, closer rank) stabilises at 37 pairs from N=20 (s=1), N=16 (s=2), N=12 (s=3), identical set for all three (union 37; 6 no-move pairs (None,2..7) and 31 with a move; no pair has opener rank 1). Landing values, (opener,closer,window) classes, path words, lap-free words and reduced words keep growing at every step N -> N+4 (new items per step in the +columns; new path words per step for s=1: 48, 263, 517, 1993, 2580, 6447, 8526, 18007).
4. Maximum landing (exact): s=1: 49/13 at (1,5,6,7,8,11,13), found at N=13, unchanged to N=40; ratio to 4s: 49/52. s=2: 33/7 at (2,8,11,14,19,30,31) and (2,6,8,9,11,14,15); ratio 33/56. s=3: 17/3 at (3,9,11,14,15,19,24); ratio 17/36. No lattice arrangement lands above 7 (landing > 7 count 0 in all three families); no counterexample to "landing <= 7 on lattices" in these families. Maximum grows with s (49/13, 33/7, 17/3), all below 4s.
5. No-move (lonely at R=1): 1,344,904 (s=1), 1,920,660 (s=2), 2,323,068 (s=3). Smallest: s=1 (1,2,3,4,5,6,7); s=2 (2,3,4,5,6,7,8); s=3 (3,4,5,6,7,8,9) (the progressions a/s with a=s..s+6 ).
6. Lemmas re-checked on every arrangement: closer rank = opener rank with opener rank != 7: 0 violations; gate (landing > 7 iff rank 1 is a setter): 0 violations (the equivalence holds on every arrangement; both sides are false throughout, so the gate is exercised only as 'no rank-1 setter occurs and no landing exceeds 7').
7. Top five landings (below) are not near the staircase 7(7/9)^k beyond the ratios shown (R*/value from 0.89 to 1.11; s=2 member 89/21 is within ratio 1.000832 of 7(7/9)^2 without equalling it); the formula 9(8a+1)(8b+1)/(8c-1)^2 has no solution (a,b,c < 120) for 14 of the 15 top landings; solutions exist for 99/19 (s=3), listed below. Not reached by that search: any representation for the others.

# Raw analysis output (lat_analysis_v1.out)

## s = 1 (readings a/1, gcd(a)=1, a_1=1, a_7 <= 40; exhaustive over this family: a_7 from 7 to 40)
arrangements computed 3262623 (skipped for gcd>1: 0); total 3262623

| N (a7 <= sN) | rho_7<= | arrangements | landing values | max R* | pairs | classes | words | lap-free | reduced | words not in J2 set | +land | +pair | +cls | +word | +free | +red | +newword |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 12 | 12 | 462 | 12 | 25/7 (3.571428) | 26 | 81 | 48 | 48 | 32 | 0 | +12 | +26 | +81 | +48 | +48 | +32 | +0 |
| 16 | 16 | 5005 | 32 | 49/13 (3.769230) | 36 | 357 | 311 | 284 | 245 | 0 | +20 | +10 | +276 | +263 | +236 | +213 | +0 |
| 20 | 20 | 27132 | 46 | 49/13 (3.769230) | 37 | 808 | 828 | 697 | 665 | 56 | +14 | +1 | +451 | +517 | +413 | +420 | +56 |
| 24 | 24 | 100947 | 64 | 49/13 (3.769230) | 37 | 1669 | 2821 | 1867 | 2465 | 1864 | +18 | +0 | +861 | +1993 | +1170 | +1800 | +1808 |
| 28 | 28 | 296010 | 82 | 49/13 (3.769230) | 37 | 2786 | 5401 | 2931 | 4667 | 4431 | +18 | +0 | +1117 | +2580 | +1064 | +2202 | +2567 |
| 32 | 32 | 736281 | 106 | 49/13 (3.769230) | 37 | 4542 | 11848 | 5240 | 10818 | 10878 | +24 | +0 | +1756 | +6447 | +2309 | +6151 | +6447 |
| 36 | 36 | 1623160 | 130 | 49/13 (3.769230) | 37 | 6334 | 20374 | 7271 | 18691 | 19404 | +24 | +0 | +1792 | +8526 | +2031 | +7873 | +8526 |
| 40 | 40 | 3262623 | 159 | 49/13 (3.769230) | 37 | 9079 | 38381 | 10986 | 36115 | 37411 | +29 | +0 | +2745 | +18007 | +3715 | +17424 | +18007 |

Hole check (rho_7 <= 17, a7 <= 17): distinct path words not in the J2 known set: 0 []
J2 known paths reached by this family with rho_7<=17: 407 of 140727
Words not in J2 (all a7 in family): 37411; arrangements whose word is in J2: 1734535 of 3262623
max R* = 49/13 = 3.769230 ; ratio to 4s = 49/52 (decimal 0.942307); landing > 7: 0 arrangements
Top five (readings a_i with s=a_1):
  R*=49/13 (3.769230) ks=(1, 5, 6, 7, 8, 11, 13) ; nearest 7(7/9)^k: k=2 value 4.234567 ratio R*/value 0.890109 ; 9(8a+1)(8b+1)/(8c-1)^2 solutions (a,b,c<120 search): []
  R*=29/8 (3.625000) ks=(1, 3, 4, 5, 7, 18, 40) ; nearest 7(7/9)^k: k=3 value 3.293552 ratio R*/value 1.100635 ; 9(8a+1)(8b+1)/(8c-1)^2 solutions (a,b,c<120 search): []
  R*=25/7 (3.571428) ks=(1, 3, 4, 5, 7, 12, 40) ; nearest 7(7/9)^k: k=3 value 3.293552 ratio R*/value 1.084369 ; 9(8a+1)(8b+1)/(8c-1)^2 solutions (a,b,c<120 search): []
  R*=25/7 (3.571428) ks=(1, 3, 4, 5, 7, 12, 32) ; nearest 7(7/9)^k: k=3 value 3.293552 ratio R*/value 1.084369 ; 9(8a+1)(8b+1)/(8c-1)^2 solutions (a,b,c<120 search): []
  R*=25/7 (3.571428) ks=(1, 3, 4, 5, 7, 12, 24) ; nearest 7(7/9)^k: k=3 value 3.293552 ratio R*/value 1.084369 ; 9(8a+1)(8b+1)/(8c-1)^2 solutions (a,b,c<120 search): []
Landing > 7 smallest-a7 examples: []
No-move (lonely at R=1) count 1344904; first examples: [(1, 2, 3, 4, 5, 6, 7), (1, 2, 3, 4, 5, 6, 9), (1, 2, 3, 4, 5, 7, 9), (1, 2, 3, 4, 6, 7, 9), (1, 2, 3, 5, 6, 7, 9)]
Violations: closer==opener with opener rank != 7: 0 ; gate (landing>7 iff rank 1 sets a move): 0
moves histogram: [(0, 1344904), (1, 593775), (2, 669984), (3, 364396), (4, 162868), (5, 73389), (6, 32430), (7, 12585), (8, 5092), (9, 1886), (10, 747), (11, 315), (12, 135), (13, 66), (14, 22), (15, 17), (16, 6), (17, 4), (19, 1), (24, 1)]

## s = 2 (readings a/2, gcd(a)=1, a_1=2, a_7 <= 44; exhaustive over this family: a_7 from 8 to 44)
arrangements computed 5191522 (skipped for gcd>1: 54264); total 5245786

| N (a7 <= sN) | rho_7<= | arrangements | landing values | max R* | pairs | classes | words | lap-free | reduced | words not in J2 set | +land | +pair | +cls | +word | +free | +red | +newword |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 12 | 12 | 74151 | 51 | 33/7 (4.714285) | 35 | 798 | 551 | 538 | 578 | 0 | +51 | +35 | +798 | +551 | +538 | +578 | +0 |
| 16 | 16 | 588770 | 85 | 33/7 (4.714285) | 37 | 2676 | 4214 | 3429 | 4394 | 0 | +34 | +2 | +1878 | +3663 | +2891 | +3816 | +0 |
| 20 | 20 | 2733549 | 121 | 33/7 (4.714285) | 37 | 5680 | 10916 | 7720 | 11257 | 2671 | +36 | +0 | +3004 | +6702 | +4291 | +6863 | +2671 |
| 22 | 22 | 5191522 | 145 | 33/7 (4.714285) | 37 | 7766 | 17482 | 11205 | 17986 | 8932 | +24 | +0 | +2086 | +6566 | +3485 | +6729 | +6261 |

Hole check (rho_7 <= 17, a7 <= 34): distinct path words not in the J2 known set: 0 []
J2 known paths reached by this family with rho_7<=17: 5511 of 140727
Words not in J2 (all a7 in family): 8932; arrangements whose word is in J2: 4544550 of 5191522
max R* = 33/7 = 4.714285 ; ratio to 4s = 33/56 (decimal 0.589285); landing > 7: 0 arrangements
Top five (readings a_i with s=a_1):
  R*=33/7 (4.714285) ks=(2, 8, 11, 14, 19, 30, 31) ; nearest 7(7/9)^k: k=2 value 4.234567 ratio R*/value 1.113286 ; 9(8a+1)(8b+1)/(8c-1)^2 solutions (a,b,c<120 search): []
  R*=33/7 (4.714285) ks=(2, 6, 8, 9, 11, 14, 15) ; nearest 7(7/9)^k: k=2 value 4.234567 ratio R*/value 1.113286 ; 9(8a+1)(8b+1)/(8c-1)^2 solutions (a,b,c<120 search): []
  R*=22/5 (4.400000) ks=(2, 6, 9, 12, 15, 21, 24) ; nearest 7(7/9)^k: k=2 value 4.234567 ratio R*/value 1.039067 ; 9(8a+1)(8b+1)/(8c-1)^2 solutions (a,b,c<120 search): []
  R*=89/21 (4.238095) ks=(2, 5, 7, 9, 12, 16, 42) ; nearest 7(7/9)^k: k=2 value 4.234567 ratio R*/value 1.000832 ; 9(8a+1)(8b+1)/(8c-1)^2 solutions (a,b,c<120 search): []
  R*=82/21 (3.904761) ks=(2, 9, 11, 13, 15, 21, 24) ; nearest 7(7/9)^k: k=2 value 4.234567 ratio R*/value 0.922115 ; 9(8a+1)(8b+1)/(8c-1)^2 solutions (a,b,c<120 search): []
Landing > 7 smallest-a7 examples: []
No-move (lonely at R=1) count 1920660; first examples: [(2, 3, 4, 5, 6, 7, 8), (2, 3, 4, 5, 6, 7, 9), (2, 3, 4, 5, 6, 8, 9), (2, 3, 4, 5, 7, 8, 9), (2, 3, 4, 6, 7, 8, 9)]
Violations: closer==opener with opener rank != 7: 0 ; gate (landing>7 iff rank 1 sets a move): 0
moves histogram: [(0, 1920660), (1, 1300270), (2, 931048), (3, 577753), (4, 261686), (5, 111343), (6, 52164), (7, 21572), (8, 8744), (9, 3871), (10, 1404), (11, 580), (12, 245), (13, 120), (14, 35), (15, 15), (16, 5), (17, 5), (18, 1), (19, 1)]

## s = 3 (readings a/3, gcd(a)=1, a_1=3, a_7 <= 45; exhaustive over this family: a_7 from 9 to 45)
arrangements computed 5242783 (skipped for gcd>1: 3003); total 5245786

| N (a7 <= sN) | rho_7<= | arrangements | landing values | max R* | pairs | classes | words | lap-free | reduced | words not in J2 set | +land | +pair | +cls | +word | +free | +red | +newword |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 12 | 12 | 1107106 | 90 | 17/3 (5.666666) | 37 | 2156 | 1702 | 1652 | 1808 | 0 | +90 | +37 | +2156 | +1702 | +1652 | +1808 | +0 |
| 15 | 15 | 5242783 | 135 | 17/3 (5.666666) | 37 | 5137 | 5446 | 4892 | 5751 | 0 | +45 | +0 | +2981 | +3744 | +3240 | +3943 | +0 |

Hole check (rho_7 <= 17, a7 <= 51): distinct path words not in the J2 known set: 0 []
J2 known paths reached by this family with rho_7<=17: 5446 of 140727
Words not in J2 (all a7 in family): 0; arrangements whose word is in J2: 5242783 of 5242783
max R* = 17/3 = 5.666666 ; ratio to 4s = 17/36 (decimal 0.472222); landing > 7: 0 arrangements
Top five (readings a_i with s=a_1):
  R*=17/3 (5.666666) ks=(3, 9, 11, 14, 15, 19, 24) ; nearest 7(7/9)^k: k=1 value 5.444444 ratio R*/value 1.040816 ; 9(8a+1)(8b+1)/(8c-1)^2 solutions (a,b,c<120 search): []
  R*=75/14 (5.357142) ks=(3, 11, 14, 15, 19, 24, 26) ; nearest 7(7/9)^k: k=1 value 5.444444 ratio R*/value 0.983965 ; 9(8a+1)(8b+1)/(8c-1)^2 solutions (a,b,c<120 search): []
  R*=75/14 (5.357142) ks=(3, 11, 14, 15, 17, 19, 24) ; nearest 7(7/9)^k: k=1 value 5.444444 ratio R*/value 0.983965 ; 9(8a+1)(8b+1)/(8c-1)^2 solutions (a,b,c<120 search): []
  R*=75/14 (5.357142) ks=(3, 8, 11, 14, 15, 19, 24) ; nearest 7(7/9)^k: k=1 value 5.444444 ratio R*/value 0.983965 ; 9(8a+1)(8b+1)/(8c-1)^2 solutions (a,b,c<120 search): []
  R*=99/19 (5.210526) ks=(3, 7, 11, 15, 19, 24, 26) ; nearest 7(7/9)^k: k=1 value 5.444444 ratio R*/value 0.957035 ; 9(8a+1)(8b+1)/(8c-1)^2 solutions (a,b,c<120 search): [(0, 653, 12), (3, 26, 12), (0, 4415, 31), (21, 26, 31)]
Landing > 7 smallest-a7 examples: []
No-move (lonely at R=1) count 2323068; first examples: [(3, 4, 5, 6, 7, 8, 9), (3, 4, 5, 6, 7, 8, 10), (3, 4, 5, 6, 7, 9, 10), (3, 4, 5, 6, 8, 9, 10), (3, 4, 5, 7, 8, 9, 10)]
Violations: closer==opener with opener rank != 7: 0 ; gate (landing>7 iff rank 1 sets a move): 0
moves histogram: [(0, 2323068), (1, 1020578), (2, 1013156), (3, 507010), (4, 211905), (5, 82195), (6, 42964), (7, 22441), (8, 11135), (9, 4858), (10, 1912), (11, 807), (12, 426), (13, 186), (14, 75), (15, 45), (16, 19), (17, 2), (18, 1)]

Union over s=['1', '2', '3'] of (opener rank, closer rank) pairs: 37: [(None, 2), (None, 3), (None, 4), (None, 5), (None, 6), (None, 7), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 2), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 7), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7)]
Path words total over s=['1', '2', '3']: 57578; words occurring in more than one s: 3484; words only in s=2 and not in J2: 8025; only in s=3 not in J2: 0
Words in s=2 (rho_7 in (17,22]) not in J2 and not in s=1 words: 8025

## Cross-family: words not in J2 across the listed s: 45436 distinct (first occurrence s,example kept)