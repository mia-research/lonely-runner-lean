# Outcome taxonomy of arrangements, v1

Objects: readings rho_1=1<...<rho_7 (all positive, normalised so rho_1=1), R>=1. Zone (y,j): 8j-1 < R*rho_y < 8j+1; entry n(y,j)=(8j-1)/rho_y, exit e(y,j)=(8j+1)/rho_y. Z(R) = set of zones containing R. Strip reading: |rho_y-8j|<1 for some j>=1 (equivalently y in Z(1)).

- Cascade: R:=1; while Z(R) nonempty, R:=max exit over Z(R). Landing R*. nm = number of jumps.
- Chain-free landing (used by the independent labeller): R* = least R in {1} U {exits >= 1} with Z(R) empty. Reason: a jump from R goes to the largest exit among zones containing R, and [R, exit) lies inside that zone, so every point passed over is blocked.
- Opener (s,j): the zone with exit R*; among several zones with the same exit, the one with the smallest entry, then the highest rank. (Rule "highest rank" alone disagreed with the cascade setter in 9 of the 9 tied rows; the smallest-entry rule agreed in 9 of 9, see taxo_tie_v1.out.)
- Closer (c,k): least entry n(y,k)>=R*, k>=1, lowest rank on ties. width = n(c,k)-R*.
- "same" = c==s (closer is the opener's reading, so width = 6/rho_s).

Conditions are checked by an independent labeller (taxo_lib_v1.label_conditions: first-step inequalities for nm, least clear point of {1} U exits for R*, direct zone tests for opener and closer; no cascade iteration) against the cascade labeller (outcome() of outcome_classes_v2.py). "Violation" = the two labels differ on an arrangement.

## Class table (sample: 52,000 exact arrangements, 50,709 distinct; 8 generators)

| class | definition | condition on the readings | size | violations |
|---|---|---|---|---|
| K0 | nm=0, width>0 | every rho_y has dist(rho_y,8Z)>=1 (Z(1) empty), and no rho_y in {7,15,23,...} | 14,418 | 0 |
| K0z | nm=0, width=0 | Z(1) empty and some rho_y = 8k-1 (entry equals 1) | 4,029 | 0 |
| K1a | nm=1, opener lap 1, closer differs, width>0 | Z(1) nonempty, Z(R2) empty with R2=max exit over Z(1); opener (s,1): 7<rho_s<9 and 9/rho_s=R2; closer reading != s | 11,258 | 0 |
| K1b | nm=1, opener lap j>=2, closer differs | as K1a with opener lap j>=2: 8j-1<rho_s<8j+1, (8j+1)/rho_s=R2 | 9,067 | 0 |
| K1s1 | nm=1, opener lap 1, closer = s | K1a opener, and 15/rho_s < every other entry >= R2 (strictly) | 93 | 0 |
| K1s2 | nm=1, opener lap j>=2, closer = s | K1b opener, and (8j+7)/rho_s < every other entry >= R2 | 341 | 0 |
| K1z | nm=1, width 0 | Z(1) nonempty, Z(R2) empty, and some entry equals R2 (rho_y*R2 = 8k-1) | 5 | 0 |
| K2a | nm>=2, opener lap 1, opener a strip reading, closer differs | (see empty classes) | 0 | 0 |
| K2b | nm>=2, opener strip reading, lap j>=2, closer differs | Z(1) nonempty, Z(R2) nonempty (R2 as above); opener (s,j), j>=2, s strip with j != round(rho_s/8); closer != s | 2,482 | 0 |
| K2c | nm>=2, opener not a strip reading, lap 1, closer differs | Z(1), Z(R2) nonempty; opener (s,1), rho_s=9/R* <=7 (not in (7,9)), closer != s | 4,198 | 0 |
| K2d | nm>=2, opener not a strip reading, lap j>=2, closer differs | Z(1), Z(R2) nonempty; opener (s,j), j>=2, rho_s not in any (8j'-1,8j'+1), closer != s | 5,394 | 0 |
| K2s1 | nm>=2, opener lap 1, closer = s | Z(1), Z(R2) nonempty; opener (s,1) and 15/rho_s < every other entry >= R* | 0 | 0 |
| K2s2 | nm>=2, opener lap j>=2, closer = s | Z(1), Z(R2) nonempty; opener (s,j), j>=2, (8j+7)/rho_s < every other entry >= R* | 621 | 0 |
| K2z | nm>=2, width 0 | Z(1), Z(R2) nonempty and some entry equals R* | 94 | 0 |

14 classes, mutually exclusive and exhaustive by construction (order of tests: nm; width=0; closer=s; opener lap; opener strip). Sizes sum to 52,000. Violation count on the final rule set: 0 in 52,000 (taxo_relabel_v1.out).

Other checks, all on the 52,000 (taxo_report_v1.out, taxo_lemma_v1.out): landing differs from the least clear point of {1} U exits: 0. Landing differs from (8j+1)/rho_opener: 0. Negative width: 0. nm=1 with a non-strip opener: 0. nm>=2 with an opener zone that contains R=1: 0.

## Exception found and what it showed (first version of the rule)

With the opener rule "highest-rank zone whose exit equals R*", 7 arrangements were mislabelled (K2c vs K2d), e.g. [1,6,7,8,38,39,40], [1,6,7,14,22,24,25], [1,7,33,39,40,58,63], [1,4,7,8,22,57,63]. Common feature: two zones end at the same R*, the zone of the cascade's setter (lower rank, lap 1) and a higher-rank zone of a high lap (entry later than the previous cascade point, so that reading did not block at the last step). The zones with a common exit are nested, the cascade's setter is the one with the earlier entry. Rule changed to smallest entry then highest rank; 0 violations afterwards. Not a failure of the class structure; the opener has to be read from the zone that contains the last jump's origin, and the smallest-entry zone does.

## Empty classes in the sample

K2a and K2s1.

K2a: empty by argument, with a check. If s is a strip reading with rho_s in (8j'-1,8j'+1), its zone (s,j') contains R=1, so its exit (8j'+1)/rho_s <= R2. An opener of a cascade with nm>=2 has exit R* > R2, so the opener's lap j != j' = round(rho_s/8). A lap-1 opener has R*=9/rho_s>=1, so rho_s<=9, so a strip opener would have j'=1 = j. Contradiction. Check on the sample: nm>=2 openers that are zones containing R=1: 0 of 12,789. No arrangement can be constructed in K2a, since the argument excludes it; "unreached" does not apply.

K2s1: no proof found and no construction found. Searches (cascade labeller, exact, all returning 0 hits): 52,000 sample rows, 120,000 from three searching modes (taxo_search_v1.out), 99,802 from a family built for it (s in (5.4,7], strip blockers of laps 1-3, fillers in (1,3); 41,644 of them with nm>=2, taxo_search2_v1.out). Observations from the sample: nm>=2 with opener lap 1 occurs 4,273 times (K2c) with rho_s from 2.481 to 7; no row has nm>=2 with lap-1 opener and rho_s>7. Partial reduction: a lap-1 opener with nm>=2 needs 7/rho_s < R2 < R* = 9/rho_s, and R2 <= 9/7, so rho_s > 49/9 = 5.44 or the zone does not reach R2... (this was derived by hand and is not exhaustively verified); a strip blocker t with lap-1 has next entry 15/rho_t < 15/rho_s whenever rho_t > rho_s, which puts a competing entry in front of s's. The case with a lap-2+ strip blocker was not closed by hand. Status: empty in all searches run, reason not established; this is an unreached/unproved class, not a proved-empty one.

Rare but non-empty: K1z (5), K1s1 (93), K2z (94). K0z is large because integer and deformed-AP families contain 8k-1.

## Scope notes
- terminals5_J1.pkl and outcome_survey_v2.pkl were not used for the table. Note: in outcome_survey_v2.pkl the 'rho' field of families grid+laps and clump is not normalised to rho_1=1, so a rank-based "strip" test on it mis-classifies (that produced apparent nm=1 non-strip openers in a first look); the fresh sample normalises.
- Sample is a union of generators, not a measure on arrangements; sizes describe this sample only. 1,291 duplicate arrangements (integer and grid families).
- Generators: five from outcome_survey_v2.py (random 8000, AP deformed 8000, grid+laps 6000, clump 6000, strips 6000) plus added near8 (readings 8j+-u, laps 1-4; 6000), ladder (geometric a^k, a in {6/5,...,3}; 6000), integers (distinct integer readings; 6000).

## Files
taxo_lib_v1.py (generators, both labellers), taxo_sample_v1.py/.out/.pkl, taxo_report_v1.py/.out (first-version run, with the 7 violations), taxo_tie_v1.py/.out, taxo_relabel_v1.py/.out (final rule: 0 violations), taxo_search_v1.py/.out, taxo_search2_v1.py/.out, taxo_lemma_v1.py/.out.
