# ph2_catalogue_v1 -- phase 2 of the cascade (from state 9) and the effect of the fastest reading

Scripts: `ph2_task1_v1.py` (-> `ph2_task1_v1.out`, `ph2_words_J1_v1.tsv`, `ph2_words_J2leaf_v1.tsv`), `ph2_task2_v1.py big|j1` (-> `ph2_task2_big_v1.out`, `ph2_task2_j1_v1.out`). Exact Fractions; `path()` from cascade_path_map_v1.py; `res()` in task 2 is checked against `outcome()` on 150 members (asserts). Data: `cell_members7_J1.pkl` (18,452 exact members of 19,679 J=1 regions, leaf + stop), `cell_members_J2.pkl` (110,081 exact members, J=2 LEAF regions only; `terminals7_J2.pkl` / `cell_members7_J2.pkl` do not exist on disk, so every J=2 statement is leaf-only). Phase-1 word = moves before the reading-1 move (1,1) (state -> 9); phase-2 word = moves after it.

## Proved (inequalities derived by hand, each also checked exactly on every move below)
- P1 (link rule). If (a,j) sets a move, the new state is R=(8j+1)/rho_a and a is at position 1 there (clear), so the next setter b != a has a zone lap k with (8k-1)/rho_b < R < (8k+1)/rho_b, i.e. rho_b/rho_a in ((8k-1)/(8j+1),(8k+1)/(8j+1)). Hence rho_b > rho_a => k > j (strict); rho_b < rho_a => k <= j. Checked: 0 violations in 160,024 consecutive pairs (J=1) and 106,721 (J=2 leaf).
- P2. Consecutive setters differ (P1), and no (reading,lap) is a setter twice (states increase and a zone ends at its exit). Checked: 0 and 0.
- P3 (move count bound, per arrangement). Every phase-2 move is a distinct zone whose exit lies in (9,R*]. So N2 <= B1 := sum over ranks 2..7 of #{j : 9 rho_y < 8j+1 <= R* rho_y}, and N2 <= B2 := the longest chain of zones (exit increasing, each zone contains the previous exit, consecutive readings differ, first zone contains 9). B2 <= B1 is checked, not derived. B2 does not change when the cut-off R* is replaced by any X >= R* (a zone containing a point <= R* with exit > R* would contain the clear state R*, so no chain crosses R*); with X = 12 it is therefore a bound for every arrangement with landing <= 12. Checked exactly: N2 <= B2 <= B1 in 7567/7567 (J=1) and 4939/4939 (J=2 leaf).
- Uniform number: B1 with X = 12 and rho_y <= 9 is at most 6*(floor(3*9/8)+1)=24 (algebra); the max of B1(12) over J=1 gate-crossing members is 17 and of B2(12) is 11.
## Observed (not derived)
- N2 <= 9 in both member lists (max N2 = 9, one member each; max B2 = 11). The step "landing < 12" is the float-LP supremum 26433/2209 = 11.966 (E349), not derived. A bound 9 on N2 independent of the arrangement is not derived: B2 (11) is the best derived-in-form number found, and its slack over N2 is 0..5 (J=1: 0:1630, 1:890, 2:2672, 3:2009, 4:336, 5:30).

## Task 1 results (J=1, all regions, 7,567 gate-crossing members; landing > 7 iff (1,1) set: 0 failures in 18,452 and in 110,081)
- Distinct phase-2 words: 330 (J=1 all regions), 284 (J=1 leaf regions only), 289 (J=2 leaf-only). Phase-2 length distribution over words (0..9): 1,14,56,79,73,52,28,18,8,1; over members: 597,1293,2169,1760,1115,425,135,56,16,1. Landing range: 9 .. 11.592485 (J=1). Per length ranges in the .out. Full list with counts and landing min..max: the .tsv files.
- Length 0 (landing exactly 9): 597 members in J=1 (8 in J=2 leaf-only; E346's 8 are the leaf ones).
- Words by first move: 19 distinct first moves (rank,lap) in J=1: (2,3..5),(3,4..6),(4,5..7),(5,5..8),(6,7..9),(7,8..10). The first move (rank r) has lap in 3..10 (observed laps 3..10; no derivation of the minimum).
- Closure: 233 of the 330 words have their parent (word minus last move) also an occurring word; so the set is not prefix-closed (97 words have no occurring parent). The setter is the lowest-rank blocker in 14,534 of 18,835 phase-2 moves, the highest-rank blocker in 12,971 (identical count to "blocker of largest lap" -- count only, not tested move by move to be the same moves), so no setter rule by rank holds. Blocker counts at a phase-2 move: 1: 9940, 2: 5580, 3: 2710, 4: 594, 5: 11. The setter is by definition the maximum exit; no rule simpler than that was found by these tests.
- (a) Determinacy (pair counts of members, J=1 / J=2 leaf):
  * phase-2 word vs phase-1 word: same phase-2 word with different phase-1 words: 506,888 / 159,162 pairs; same phase-1 word with different phase-2 words: 221,771 / 81,675; same both: 8,584 / 4,331. 535 of 571 phase-1 words carry >1 phase-2 word (J=1). So neither word determines the other.
  * keys read at state 9 (coarser than the readings): lap vector at 9 (55 values; 37 carry >1 word; pairs same key different word 4,980,971); lap vector + blocker set (214 values; 122 ambiguous; 558,100 pairs); + order of the blockers' exits (370 values; 207 ambiguous; 393,104 pairs). So positions/laps at 9 with the blockers' exit order do NOT determine the word.
  * the endpoint order type of all zones of ranks 2..7 on (9,12] (5,708 values): 37 values carry >1 word, 91 member pairs (same key, different word). This key does not determine the word either (expected: it stops at 12 and drops information that the order of entries before 9 and exits beyond 12 carries -- cause not tested). 
  * Phase 2 is a function of rho_2..rho_7 alone (it needs phase 1 only to certify that the chain reaches 9).
- (c) Stabilisation: J=1 windows rho_7 in (7,8]: 304 words, (8,9]: 63 words of which 26 new (cumulative 330). J=2 leaf-only with rho_7 in (9,17]: 59 gate-crossing members, 6 words, 3 not among the 330 J=1 words: `(6,8)`; `(5,7)(6,8)(7,18)`; `(7,17)(5,7)(6,8)(7,18)`; (rho_7 in (9,11]: 14 members, 1 word; (11,15]: 0 members; (15,17]: 45 members, 5 words). 44 of the 330 J=1 words are absent from the J=2 leaf list (leaf-only versus all-region comparison; not like for like). Not stabilised in the data: new words appear at each window with members; the J=2 stop regions were not available.
## Task 2 results (rank 7 = fastest reading)
Classes by REMOVAL (compare the 6-reading cascade of rho_1..rho_6 with the 7-reading one; "gate" = landing>7 differs):
- J=1, all 7,567 gate-crossing members: 7,567 changes gate (6-reading landing <= 7 in every one). (All other J=1 members were not tested.)
- J=2 leaf regions with rho_7 > 9 (102,792 members; selection = the 59 gate-crossing + every 40th other index, 2,627 members; the others not reached): changes gate 59; changes landing (gate same) 2412; no effect (same path) 111 (closer same 80, closer differs 31); one extra move (landing same) 0; other (path differs, landing same, not a single deleted move) 45.
- Rule A "6-reading word = 7-reading word with rank-7 moves deleted": holds 145 (all non-gate-crossing), fails 2,482 (59 gate-crossing, 2,423 other); counterexamples with exact readings are listed in `ph2_task2_big_v1.out` and `ph2_task2_j1_v1.out` (e.g. 7-word (2,1)(3,2)(7,3)(6,3)(5,3)(4,3)(7,4)(3,3)(6,4)(2,2)(5,4)(4,4)(7,5) against 6-word (2,1)(3,2)). Rule A fails because deleting a rank-7 move changes the later states, hence which zones block.
- Replacement of rank 7 by rho_6 + d, d in {1/8,1/2,1,2,4,8} (15,762 pairs, relative to the 6-reading cascade): same path 10,599; changes landing 4,725; other 438; changes gate 0; one extra move 0.
- Shift rho_7 -> rho_7 + 8k/R_i (R_i every visited state and the landing, k in {-2,-1,1,2}; 131,278 shifts): identical path+landing+closer 1,152; same path, closer differs 1,150; path differs landing same 7,288; changes landing 116,035; changes gate 5,653. In all but 7 of these shifts the original rank 7 blocks at some visited state (tuple counts in the .out). Exception to "an inactive rank 7 can be moved by 8k/R_i without effect": rho = [1, 4109783601874447/562949953421312, ..., 17], R_i = 1 (first state), k=2: word (2,1) -> (2,1)(7,5), landing 1.2328 -> 1.2424.
- Classes {no effect, one extra move, changes landing, changes gate}: "one extra move" was not reached in the removal search over the 2,627 members (and 7,567 J=1 members) nor in the 6-replacement search; it is not claimed absent. The effect classes observed: changes gate (J=1: 7,567/7,567; J=2 leaf rho_7>9: 59/59 gate-crossing), changes landing (dominant among the rest), no effect (111 of 2,627), plus the residual class "other".

## Raw outputs

### ph2_task1_v1.out
```
== J=1 (rho_7<=9), all outcome regions: members 18452; gate-crossing (landing>7) 7567; (landing>7) xor (reading 1 sets a move) failures 0; members with >1 reading-1 move 0
   of which members of leaf regions: 4885; of stop regions: 2682
-- J=1 all regions: 7567 gate-crossing members; distinct phase-2 words 330; distinct phase-1 words 571
   key [w1 (phase-1 word)]: distinct key values 571; key values carrying >1 phase-2 word 535 (of 571); pairs same key & different w2: 221771; pairs same w2 & different key: 506888; pairs same key & same w2: 8584
   key [lap vector at 9]: distinct key values 55; key values carrying >1 phase-2 word 37 (of 55); pairs same key & different w2: 4980971; pairs same w2 & different key: 339867; pairs same key & same w2: 175605
   key [lap vector + blocker set at 9]: distinct key values 214; key values carrying >1 phase-2 word 122 (of 214); pairs same key & different w2: 558100; pairs same w2 & different key: 421779; pairs same key & same w2: 93693
   key [lap vector + blocker set + order of blockers' exits at 9]: distinct key values 370; key values carrying >1 phase-2 word 207 (of 370); pairs same key & different w2: 393104; pairs same w2 & different key: 427243; pairs same key & same w2: 88229
   key [endpoint order type of all zones of ranks 2..7 on (9,12]]: distinct key values 5708; key values carrying >1 phase-2 word 37 (of 5708); pairs same key & different w2: 91; pairs same w2 & different key: 512503; pairs same key & same w2: 2969
-- J=1 all regions catalogue: distinct phase-2 words 330; by length (words): [(0, 1), (1, 14), (2, 56), (3, 79), (4, 73), (5, 52), (6, 28), (7, 18), (8, 8), (9, 1)]; by length (members): [(0, 597), (1, 1293), (2, 2169), (3, 1760), (4, 1115), (5, 425), (6, 135), (7, 56), (8, 16), (9, 1)]
   words whose parent (word minus last move) is also an occurring word: 233 of 330
   distinct first phase-2 moves (rank,lap) over words: 19; as list with word count: [((2, 3), 32), ((2, 4), 9), ((2, 5), 3), ((3, 4), 22), ((3, 5), 7), ((3, 6), 1), ((4, 5), 40), ((4, 6), 15), ((4, 7), 1), ((5, 5), 12), ((5, 6), 72), ((5, 7), 6), ((5, 8), 1), ((6, 7), 33), ((6, 8), 9), ((6, 9), 2), ((7, 8), 44), ((7, 9), 19), ((7, 10), 1)]
   distinct last moves (the opener) over words: 19
   landing range overall: min 9 = 9.000000, max 440706653985595377864088223744/38016583061531177866283066705 = 11.592485
   length 0: landing range [9.000000, 9.000000]
   length 1: landing range [9.000387, 9.761938]
   length 2: landing range [9.253521, 10.405995]
   length 3: landing range [9.334419, 10.552586]
   length 4: landing range [9.850522, 10.991691]
   length 5: landing range [10.212829, 11.237248]
   length 6: landing range [10.490564, 11.385170]
   length 7: landing range [10.663762, 11.592485]
   length 8: landing range [11.307692, 11.567053]
   length 9: landing range [11.561741, 11.561741]
   10 most frequent words (count, landing min..max, word):
     597  9.00000..9.00000  ()
     275  9.25352..9.83140  ((3, 4), (7, 9))
     265  9.00039..9.28510  ((7, 8),)
     247  9.25352..10.03619  ((2, 3), (7, 9))
     230  9.00118..9.38210  ((5, 6),)
     221  9.00423..9.76194  ((2, 3),)
     189  9.63663..10.04680  ((2, 3), (3, 4), (7, 9))
     183  9.46154..10.04113  ((2, 3), (4, 5))
     179  9.00048..9.24931  ((7, 9),)
     168  9.25352..9.72405  ((4, 5), (7, 9))
   phase-2 moves examined 18835; setter = lowest-rank blocker in 14534; = highest-rank blocker in 12971; = blocker of largest lap in 12971; blocker-count distribution [(1, 9940), (2, 5580), (3, 2710), (4, 594), (5, 11)]
   LINK RULE over all consecutive move pairs (phase 1 and 2) of these members: 160024 pairs; consecutive equal setters 0; link-rule violations 0; (reading,lap) setters used twice in one path: 0
-- J=1 all regions phase-2 move count N2 vs per-arrangement bounds (exact): B1 = sum over ranks 2..7 of #zones with exit in (9,X]; B2 = longest chain of zones (exit increasing, next zone contains the previous exit, consecutive readings differ, first zone contains 9) with exits in (9,X]
   X = landing R*: violations of N2 <= B2 <= B1: 0 of 7567; max B1 11, max B2 11, max N2 9; slack B2-N2 distribution [(0, 1630), (1, 890), (2, 2672), (3, 2009), (4, 336), (5, 30)]; slack B1-N2 [(0, 1481), (1, 464), (2, 2498), (3, 2410), (4, 659), (5, 55)]
   X = 12 (uses landing < 12, observed): violations 0; max B1 17, max B2 11; slack B2-N2 distribution [(0, 1630), (1, 890), (2, 2672), (3, 2009), (4, 336), (5, 30)]
-- J=1 new phase-2 words by window of rho_7 (cumulative, ascending rho_7 windows of width 1; members sorted by window):
   rho_7 in (1,2]: members 0; words 0; new words 0; cumulative 0
   rho_7 in (2,3]: members 0; words 0; new words 0; cumulative 0
   rho_7 in (3,4]: members 0; words 0; new words 0; cumulative 0
   rho_7 in (4,5]: members 0; words 0; new words 0; cumulative 0
   rho_7 in (5,6]: members 0; words 0; new words 0; cumulative 0
   rho_7 in (6,7]: members 0; words 0; new words 0; cumulative 0
   rho_7 in (7,8]: members 6392; words 304; new words 304; cumulative 304
   rho_7 in (8,9]: members 1175; words 63; new words 26; cumulative 330
== J=2 (rho_7<=17), LEAF REGIONS ONLY (cell_members_J2.pkl; the stop regions of J=2 are not on disk): members 110081; gate-crossing (landing>7) 4939; (landing>7) xor (reading 1 sets a move) failures 0; members with >1 reading-1 move 0
-- J=2 leaf-only: 4939 gate-crossing members; distinct phase-2 words 289; distinct phase-1 words 602
   key [w1 (phase-1 word)]: distinct key values 602; key values carrying >1 phase-2 word 446 (of 602); pairs same key & different w2: 81675; pairs same w2 & different key: 159162; pairs same key & same w2: 4331
   key [lap vector at 9]: distinct key values 58; key values carrying >1 phase-2 word 28 (of 58); pairs same key & different w2: 2152634; pairs same w2 & different key: 85088; pairs same key & same w2: 78405
   key [lap vector + blocker set at 9]: distinct key values 196; key values carrying >1 phase-2 word 114 (of 196); pairs same key & different w2: 252936; pairs same w2 & different key: 127254; pairs same key & same w2: 36239
   key [lap vector + blocker set + order of blockers' exits at 9]: distinct key values 340; key values carrying >1 phase-2 word 161 (of 340); pairs same key & different w2: 178452; pairs same w2 & different key: 129920; pairs same key & same w2: 33573
   key [endpoint order type of all zones of ranks 2..7 on (9,12]]: distinct key values 3700; key values carrying >1 phase-2 word 22 (of 3700); pairs same key & different w2: 37; pairs same w2 & different key: 161539; pairs same key & same w2: 1954
-- J=2 leaf-only catalogue: distinct phase-2 words 289; by length (words): [(0, 1), (1, 14), (2, 42), (3, 72), (4, 69), (5, 47), (6, 21), (7, 15), (8, 7), (9, 1)]; by length (members): [(0, 8), (1, 666), (2, 1448), (3, 1326), (4, 969), (5, 365), (6, 94), (7, 47), (8, 15), (9, 1)]
   words whose parent (word minus last move) is also an occurring word: 156 of 289
   distinct first phase-2 moves (rank,lap) over words: 20; as list with word count: [((2, 3), 31), ((2, 4), 8), ((2, 5), 3), ((3, 4), 21), ((3, 5), 5), ((3, 6), 1), ((4, 5), 35), ((4, 6), 11), ((4, 7), 1), ((5, 5), 11), ((5, 6), 53), ((5, 7), 7), ((5, 8), 1), ((6, 7), 30), ((6, 8), 8), ((6, 9), 2), ((7, 8), 40), ((7, 9), 18), ((7, 10), 1), ((7, 17), 1)]
   distinct last moves (the opener) over words: 20
   landing range overall: min 9 = 9.000000, max 9903520314283042199192993792/854305237337811163612999167 = 11.592485
   length 0: landing range [9.000000, 9.000000]
   length 1: landing range [9.000387, 9.556077]
   length 2: landing range [9.253521, 10.405995]
   length 3: landing range [9.334419, 10.552586]
   length 4: landing range [9.579302, 10.916818]
   length 5: landing range [10.217437, 11.237248]
   length 6: landing range [10.490564, 11.331890]
   length 7: landing range [10.636364, 11.592485]
   length 8: landing range [11.307692, 11.567053]
   length 9: landing range [11.561741, 11.561741]
   10 most frequent words (count, landing min..max, word):
     222  9.25352..10.03619  ((2, 3), (7, 9))
     218  9.25352..9.83140  ((3, 4), (7, 9))
     168  9.00039..9.28510  ((7, 8),)
     147  9.63663..10.04680  ((2, 3), (3, 4), (7, 9))
     136  9.00048..9.24931  ((7, 9),)
     135  9.00199..9.38210  ((5, 6),)
     130  9.25352..9.72405  ((4, 5), (7, 9))
     98  9.46222..9.99636  ((2, 3), (6, 7), (7, 9))
     85  9.52925..10.04680  ((2, 3), (4, 5), (7, 9))
     82  9.28651..10.00949  ((2, 3), (6, 8))
   phase-2 moves examined 14263; setter = lowest-rank blocker in 11128; = highest-rank blocker in 9933; = blocker of largest lap in 9933; blocker-count distribution [(1, 7688), (2, 4209), (3, 1967), (4, 395), (5, 4)]
   LINK RULE over all consecutive move pairs (phase 1 and 2) of these members: 106721 pairs; consecutive equal setters 0; link-rule violations 0; (reading,lap) setters used twice in one path: 0
-- J=2 leaf-only phase-2 move count N2 vs per-arrangement bounds (exact): B1 = sum over ranks 2..7 of #zones with exit in (9,X]; B2 = longest chain of zones (exit increasing, next zone contains the previous exit, consecutive readings differ, first zone contains 9) with exits in (9,X]
   X = landing R*: violations of N2 <= B2 <= B1: 0 of 4939; max B1 11, max B2 11, max N2 9; slack B2-N2 distribution [(0, 698), (1, 668), (2, 1885), (3, 1435), (4, 223), (5, 30)]; slack B1-N2 [(0, 607), (1, 364), (2, 1772), (3, 1679), (4, 467), (5, 50)]
   X = 12 (uses landing < 12, observed): violations 0; max B1 17, max B2 11; slack B2-N2 distribution [(0, 698), (1, 668), (2, 1885), (3, 1435), (4, 223), (5, 30)]
-- word-set comparison: J=1 all 330, J=1 leaf-only 284, J=2 leaf-only 289; J=2 leaf words not among J=1 all-region words: 3; not among J=1 leaf-only words: 5; J=1 all words not among J=2 leaf words: 44
-- J=2 leaf-only: words new relative to J=1 all-region words, by window of rho_7:
   rho_7 in (9,11]: members 14; words 1; new 1; cumulative incl. J=1 331
   rho_7 in (11,13]: members 0; words 0; new 0; cumulative incl. J=1 331
   rho_7 in (13,15]: members 0; words 0; new 0; cumulative incl. J=1 331
   rho_7 in (15,17]: members 45; words 5; new 2; cumulative incl. J=1 333
   (J=2 members with rho_7 <= 9: 4880)
```

### ph2_task2_j1_v1.out
```
J=1 (all outcome regions, rho_7<=9): processed 18452 of 18452; gate-crossing 7567. REMOVAL of rank 7 classes:
   changes gate                                                           7567
RULE A holds/fails: [(False, 7567)]
   counterexample to RULE A: readings ['1', '8345545086619319/2251799813685248', '5804876924667009/1125899906842624', '1742791081414927/281474976710656', '3981241417470989/562949953421312', '1144941322391439/140737488355328', '2485860035482239/281474976710656']
      7-word ((5, 1), (4, 1), (3, 1), (7, 2), (2, 1), (4, 2), (7, 3), (6, 3), (3, 2), (5, 3), (7, 4), (4, 3), (6, 4), (2, 2), (3, 3), (6, 5), (4, 4), (7, 6), (5, 5), (6, 6), (3, 4), (2, 3), (5, 6), (6, 7), (1, 1), (4, 7), (3, 6))
      6-word ((5, 1), (4, 1), (3, 1))
   counterexample to RULE A: readings ['1', '8242086617568053/2251799813685248', '716708666853555/140737488355328', '1720124857676231/281474976710656', '3943760808190123/562949953421312', '4525629244049771/562949953421312', '4905163742756077/562949953421312']
      7-word ((5, 1), (4, 1), (3, 1), (7, 2), (2, 1), (4, 2), (7, 3), (6, 3), (3, 2), (5, 3), (7, 4), (4, 3), (6, 4), (2, 2), (3, 3), (6, 5), (4, 4), (7, 6), (5, 5), (6, 6), (3, 4), (2, 3), (5, 6), (6, 7), (1, 1), (5, 8), (3, 6))
      6-word ((5, 1), (4, 1), (3, 1))
   counterexample to RULE A: readings ['1', '2073683240785181/562949953421312', '1442383435541277/281474976710656', '1732180041068595/281474976710656', '1972439761169685/281474976710656', '4551881239215407/562949953421312', '1235362397785657/140737488355328']
      7-word ((5, 1), (4, 1), (3, 1), (7, 2), (2, 1), (4, 2), (7, 3), (6, 3), (3, 2), (5, 3), (7, 4), (4, 3), (6, 4), (2, 2), (3, 3), (6, 5), (4, 4), (7, 6), (5, 5), (6, 6), (3, 4), (2, 3), (5, 6), (6, 7), (1, 1), (5, 8), (3, 6))
      6-word ((5, 1), (4, 1), (3, 1))
```

### ph2_task2_big_v1.out
```
members with rho_7>9: 102792 (J=2 leaf regions); region-path gate flag vs exact landing>7 on 3500 members (flag, landing>7): [((False, False), 3500)]
flagged scan covered 102792 of 102792 members; selected 2627 (gate-crossing found + every 40th)
processed 2627 of 2627 selected members in 212 s
REMOVAL of rank 7 (6-reading cascade vs 7-reading cascade), classes over processed members:
   changes gate                                                           59
   changes landing (gate same)                                            2412
   no effect (same path) / closer differs                                 31
   no effect (same path) / closer same                                    80
   other: path differs, landing same, not a single deleted move           45
   among gate-crossing (7-reading landing>7) members only:
   changes gate                                                           59
RULE A: "the 6-reading word = the 7-reading word with its moves set by rank 7 deleted": holds / fails by (gate-crossing?): [((False, False), 2423), ((False, True), 145), ((True, False), 59)]
   counterexample to RULE A: readings ['1', '8456490692095743/1125899906842624', '7066297345698643/562949953421312', '3855164874337765/281474976710656', '2028867893080607/140737488355328', '8812504606162369/562949953421312', '17']
      7-word ((2, 1), (3, 2), (7, 3), (6, 3), (5, 3), (4, 3), (7, 4), (3, 3), (6, 4), (2, 2), (5, 4), (4, 4), (7, 5))
      6-word ((2, 1), (3, 2))
   counterexample to RULE A: readings ['1', '7889846794063003/1125899906842624', '5071533555532785/562949953421312', '1559021811453253/140737488355328', '6632173486109959/562949953421312', '1800643003479375/140737488355328', '15']
      7-word ((2, 1), (5, 2), (4, 2), (7, 3), (3, 2), (6, 3), (5, 3), (4, 3), (2, 2), (6, 4), (3, 3), (5, 4), (4, 4))
      6-word ((2, 1), (5, 2), (4, 2))
   counterexample to RULE A: readings ['1', '3946150834413475/562949953421312', '399391064076175/35184372088832', '3616988316487937/281474976710656', '3888092230345171/281474976710656', '15', '4489447144451309/281474976710656']
      7-word ((2, 1), (4, 2), (3, 2), (7, 3), (6, 3), (5, 3), (4, 3), (7, 4), (3, 3), (2, 2), (4, 4), (7, 5))
      6-word ((2, 1), (4, 2), (3, 2))
   counterexample to RULE A: readings ['1', '1112353078430532719972893907027/158456325028528675187087900672', '23438273781238184121235262997/2475880078570760549798248448', '465015351819749023693368479855/39614081257132168796771975168', '129729315497590979773300993303/9903520314283042199192993792', '297105609428497959349246287339/19807040628566084398385987584', '161178846527292679725815723405/9903520314283042199192993792']
      7-word ((2, 1), (4, 2), (7, 3), (6, 3), (3, 2), (5, 3), (7, 4), (4, 3), (6, 4), (2, 2), (7, 5), (3, 3), (6, 5), (4, 4))
      6-word ((2, 1), (4, 2))
REPLACEMENT of rank 7 by rho_6 + d, d in {1/8,1/2,1,2,4,8} (class relative to the 6-reading cascade; a "no effect" here also covers closer changes):
   changes landing (gate same)                                            4725
   no effect (same path)                                                  10599
   other: path differs, landing same, not a single deleted move           438
SHIFT rho_7 -> rho_7 + 8k/R_i, k in {-2,-1,1,2}, R_i over the visited states and the landing (only rho_7' > 0, distinct):
   changes gate                                                           5653
   changes landing                                                        116035
   identical path, landing, closer                                        1152
   path differs, landing same                                             7288
   same path, closer differs                                              1150
   by (rank 7 blocks at some visited state in the original?, which R_i, unchanged-path?) counts: [((False, 'first', False), 1), ((False, 'first', True), 2), ((False, 'landing', True), 4), ((True, 'first', False), 8528), ((True, 'first', True), 199), ((True, 'landing', False), 10129), ((True, 'landing', True), 375), ((True, 'middle', False), 110318), ((True, 'middle', True), 1722)]
   exception example (rank 7 never blocks at a visited state, shift changes landing/gate): readings ['1', '4109783601874447/562949953421312', '4306691614622471/281474976710656', '4426287361987141/281474976710656', '4545883109351811/281474976710656', '2332739428358241/140737488355328', '17'] i=0 k=2
      word ((2, 1),) -> ((2, 1), (7, 5)) ; landing 1.232802033294645 -> 1.2424242424242424
```
