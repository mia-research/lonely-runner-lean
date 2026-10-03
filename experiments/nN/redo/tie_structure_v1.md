# Zero-width landings, ties, and the pair-law avoidance (tie_structure_v1)

Directory `experiments/nN/redo/`. Every number is an exact-Fraction computation (`path()`, `outcome()`, `windows()`, `verify()` from `cascade_path_map_v1.py`, `outcome_classes_v2.py`, `win_lib_v1.py`) or an inequality derivation checked exactly where stated. Floats appear only inside the LP box bounds stored in `terminals7_J1.pkl` (one use, flagged in section 6). Grades: PROVED = derivation given here plus an exact check; VERIFIED-INSTANCE = exact computation on the named sets; OBSERVED = holds on the named sets, no derivation; OPEN.

Reused, not rebuilt: `path/outcome/windows/verify` (above); the class definitions K0z/K1z/K2z of `taxo_outcome_classes_v1.md`; window data `win_rec_*.pkl` and counts of `win_lonely_set_v1.md` (E355); the old member statistics of `disc_outcome_structure_v1.md` (11 zero-width members, p_7 = 7); X6 of `EXCEPTIONS_LOG_v1.md` (a touch is not a crossing); the progression pair law of `LRC/Spec/ProgressionPairN.lean` (`pair_law`, `instant_lonely`: at readings j·c the instants a in {1,3,5,7} have runner a leaving (a·a = 1 mod 8) and runner 8-a entering (a(8-a) = 7 mod 8)); the mirror R -> 8-R of `MirrorCentreN`. No new object was needed for the criterion below; section 4 shows the pair law's instants are exactly the integer-reading case of it.

Scripts and outputs (all `tie_*_v1.*`): `tie_types` (single-point windows, all datasets), `tie_first` + `tie_first_report` + `tie_first_summary` (zero-width landings of the J=1 and J=2 stored points), `tie_taxo_first` (sampler and integer sets; constructed examples), `tie_instants` (where the points sit; integer law on lat1), `tie_integer_law`, `tie_infima` (smallest readings per class), `tie_r7_search` (landing at 7), `tie_pair` (pair-law rule and tests), `tie_region` (the example's region).

## 1. The criterion (PROVED)

Notation: p_y(R) = R rho_y mod 8; reading y is clear at R iff p_y(R) in [1,7]; its open zones are ((8j-1)/rho, (8j+1)/rho), j >= 1. The clear set of R >= 1 is closed.

**Theorem T (single-point window).** For R0 > 1, the closed window [R0, R0] occurs iff (i) every p_y(R0) lies in [1,7], (ii) some reading a has p_a(R0) = 1, (iii) some reading b has p_b(R0) = 7. At R0 = 1 (the start of the cascade) only (i) and (iii) are needed.
Derivation. p_y is strictly increasing in R at rate rho_y. Just below R0, reading y blocks iff p_y(R0) = 1 (p_y(R0) in (1,7] gives clear positions below; p_y(R0) = 1 gives positions just below 1, which are blocked). Just above R0, y blocks iff p_y(R0) = 7. There are finitely many readings, so a neighbourhood works for all at once. R0 = 1: nothing below is part of the cascade. In the language of zones: (ii) is the exit (8j+1)/rho_a = R0 of the lap-j zone of a, (iii) is the entry (8j'-1)/rho_b = R0 of the lap-j' zone of b. Reading 1 supplies (ii) at R0 = 1 itself (p_1(1) = 1, lap 0: the zone (-1,1)), so the start is the same type as a pinch with exit = (reading 1, lap 0). VERIFIED-INSTANCE of the theorem: `tie_types_v1.out`, for every window of every set, point windows listed by `windows()` satisfy (i)-(iii) and every candidate (8j+1)/rho (j <= 3) and the start that satisfies (i)-(iii) is listed: 0 mismatches in 18,452 J1 points, 52,000 sampler arrangements, 5,005 + 18,564 + 4,000 + 4,000 lattice sets.

**Corollaries.**
(a) a and b are never the same reading (8j+1 and 8j'-1 are not equal), and (8j+1) rho_b = (8j'-1) rho_a. So rho_b/rho_a = (8j'-1)/(8j+1): b has higher rank than a iff j' > j (8j'-1 > 8j+1 iff j' >= j+1), lower rank iff j' <= j. The ratio is rational: a touch is a codimension-one condition on the readings.
(b) Persistence. If the touch holds and the other five positions are in the open interval (1,7), scale (rho_a, rho_b) together by a factor near 1 (R0 moves to R0/factor, the relation is kept) and move the others slightly: the single-point window persists. So touching arrangements form a family of the dimension of the reading space minus one, with no further coincidence needed among the other readings (exact witnesses with all other readings generic in section 3).
(c) **First window.** The first window is [R*, min_y of the next entry]; its width is min_y (7 - p_y(R*))/rho_y. Hence **the first lonely window is a single point iff some reading has p_y(R*) = 7 exactly** (the landing is the upper clear edge of that reading), where R* = 1 (no move) or R* = (8j+1)/rho_a is the exit of the opener a (p_a = 1). Then rho_b R* = 8j'-1 for the closer b. This is the content of "p_7 = 7 exactly", with b any rank (section 2 shows all ranks 1..7 occur as closer).
(d) R* > 1 implies rho_7 > 7: R = 1 is blocked iff some rho_y lies in (8k-1, 8k+1); with rho_y <= rho_7 the least such is k = 1, so rho_7 > 7. K0z (R* = 1, zero width) needs a reading 8j'-1 in {7, 15, ...}, so rho_7 >= 7.
(e) Same-reading touch is impossible; two different readings can touch only with rational ratio (a), so a zero-width landing is never generic (X6 of the exceptions log: a touch at an identity change is not a crossing).

## 2. Touching types and their smallest examples

Types, by what supplies the exit and the entry (the reading-1 zones are (7,9), (15,17), (23,25), so reading 1 supplies exits at R0 in {9, 17} and entries at R0 in {7, 15, 23}; "start" is its lap-0 exit at R0 = 1):

| type | R0 | exit (ii) | entry (iii) |
|---|---|---|---|
| S start | 1 | reading 1, lap 0 | reading b = 8j'-1 (7 or 15 ...) |
| E1 reading-1 entry | 7, 15, 23 | reading a, rho_a = (8j+1)/R0 | reading 1 |
| X1 reading-1 exit | 9, 17 | reading 1 | reading b, rho_b = (8j'-1)/R0 |
| N pinch, neither is reading 1 | any | reading a >= 2 | reading b >= 2 |
| ties | any | >= 2 readings at p = 1 | >= 2 readings at p = 7 |

**All single-point windows in [1,23]** (`tie_types_v1.out`, `tie_instants_v1.out`): J1 stored points 5,552 point windows: E1 3,610 (R0 = 7: 1,521; 15: 1,233; 23: 856), X1 1,561 (9: 773; 17: 788), N at non-integer R0 379, S 2. lat1: 19,080 point windows (S 1,254; E1 3,762; X1 2,508; N at integer R0 5,256; N at non-integer R0 6,300). Sampler (52,000): 52,143 point windows (S 4,029; N at integer R0 15,758 including R0 in {6, 10, 20, 22}; non-integer 14,201). Ties (exits, entries): up to (2,2) in lat1; up to (3,3) at lat3 and (4,2), (1,5) in lat5/lat7 and the sampler.

**First window a single point** (zero-width landing):

| class | definition | smallest examples (exact) | what forces it |
|---|---|---|---|
| K0z | no move, R* = 1 | rho_7 = 7: [1,2,3,4,5,6,7], first window [1,1] (`tie_taxo_first_v1.out`, verify True). rho_7 >= 7 is PROVED (1d). | reading b at p_b(1) = 7, i.e. rho_b = 7 (or 15 ...), every other rho in [1,7] mod 8 clear. In lat1 this is "a reading in {7,15} and none in {8,16}": 1,254 = C(13,6) - C(11,6) sets (`tie_integer_law_v1.out`). lat3: 6,188 (the sets containing c = 21, rho_7 = 7). |
| K1z | one move | for every d > 0: rho_7 = 7+d, rho_6 = 7 rho_7/9, readings 1,2,3,4,5 below: R* = 9/rho_7, opener (7,1), closer (6,1), width 0, first window [R*,R*], verified for d = 1/10, 1/100, 1/1000, 1/10^6 (`tie_region_v1.out`). The infimum 7 of rho_7 is not attained (1d). Smallest explicit: d = 1/2, [1,2,3,4,5,35/6,15/2], R* = 6/5. | R=1 blocked by reading 7 alone (rho_7 in (7,9)), its exit 9/rho_7 is clear except that reading b sits at p = 7: rho_b = 7 rho_7/9 (relation (a) with j = j' = 1). |
| K2z | two or more moves | integer sets: smallest rho_7 = 10, [1,2,3,6,7,8,10], R* = 3/2, three moves, opener (4,1), closer (7,2) (`tie_taxo_first_v1.out`, lat1 and sampler agree). Tree points: smallest rho_7 = 1013836678644867/140737488355328 (7.2037), opener (4,3), closer (2,2), R* = 2814749767106560/597068132416543. | the same relation between the opener and the closer at the final state; no rule on which pair occurs beyond (a). |

Counts among stored tree points (one point per outcome region; not the box): J1 18,452 points: 161 zero-width (K0z 2; K2z 159; **K1z 0**), tied 8 (all exit ties). J2 271,361 points: 1,576 zero-width (K0z 13; K2z 1,563; K1z 0), tied 95 (exit ties 83, entry ties 19, both 7). Among the 161 J1: 60 land at R* = 7 with opener (6,6), closer (1,1), and in all 60 rho_6 = 7 exactly (type E1; the stored LP vertex sits on the box face rho_6 = 7; in J2, 65 of these); 143 of the 161 have an integer reading in {7, 9}, 18 have none. Closer ranks (entries) in J1: 1: 60, 2: 28, 3: 14, 4: 5, 5: 22, 6: 15, 7: 17; in J2: 1: 65, 2: 231, 3: 504, 4: 265, 5: 182, 6: 171, 7: 177. So the old statement "closer rank 7, p_7 = 7" (`disc_outcome_structure_v1.md`, 11 members) is a statement about that member list. K1z exists inside the J=1 reading range (rho_7 = 15/2 above) while no stored point is K1z: the stored point of a region is one witness, and zero-width is a property of where in the region the witness sits (the stored zero-width points sit on region faces: the touch relation is a face of the cell; one side of it keeps the path word with positive width, the other side has the closer's zone overlapping the landing and the cascade moves on).
lat1 (5,005): first window a point in 1,318 sets: S 1,254; pinch 64 (3 moves 49; 5 moves 10; 7 moves 2; 9 moves 1; 10 moves 2).
Landing at R* = 7 with other openers: not reached by the search of `tie_r7_search_v1.out` (reading a = (8j+1)/7 for j = 1..9, 40,000 draws each of four readings on a 1/100 grid in [1.01,9.5] plus one reading, reading 1 fixed; 0 landings at 7 in 356,000 draws). The only stored landings at 7 have rho_6 = 7.

**Smallest readings for a point window at a given instant** (`tie_infima_v1.out`; search: R0 = u/v lowest terms, u odd, 1 < R0 <= 23, v <= 12, candidate endpoints <= 12; derivation: reading rho is allowed at R0 iff rho in a closed interval [(8m+1)/R0, (8m+7)/R0], exits sit at left endpoints, entries at right endpoints, and the other readings can be placed anywhere in the allowed set). The infimum of rho_7 shrinks as R0 grows (it is a function of the allowed R0 range), so these are statements about R0 <= 23: X1 at R0 = 17: rho_7 = 23/17, attained, [1,53/51,55/51,19/17,59/51,61/51,23/17]; E1 at R0 = 23: infimum 25/23, not attained, witness [1,25/23,376/345,377/345,126/115,379/345,76/69]; N at integer R0 = 21: 25/21, attained, [1,191/189,193/189,65/63,197/189,23/21,25/21]; N at non-integer R0 = 275/12: 12/11, attained, [1,2476/2475,2477/2475,826/825,2479/2475,276/275,12/11]. Each witness: point window at R0, `crit` and `verify()` True. So single-point windows occur with all seven readings inside (1, 1.36]: the touching relation constrains two readings only.

## 3. Which touches integer readings force (PROVED, checked on lat1)

Integer readings rho_y. Let R0 = u/v lowest terms.
- Exit: rho_a u = (8j+1)v. Entry: rho_b u = (8j'-1)v. Since gcd(u,v) = 1: u divides 8j+1 so u is odd, v divides rho_a and rho_b, and rho_a/v = u^-1 = u (mod 8), rho_b/v = -u (mod 8) (u^2 = 1 mod 8).
- Conversely these residue conditions (plus clearness of the others, which is a condition on positions rho u/v mod 8) give p_a = 1, p_b = 7. So for integer readings **no equality between readings is needed: the touch is a statement about residues.**
- Integer R0 = r odd: the touch occurs iff some rho = r and some rho = -r (mod 8) and no reading is divisible by 8. Even integer R0: impossible. Non-integer R0: u odd, v | the touching readings (lat1: only v = 2, 3 occur, 3,780 and 2,520 point windows).
- Check (`tie_integer_law_v1.out`, `tie_instants_v1.out`): lat1 19,080 point windows, 0 violations of the residue form; 115,115 (set, odd instant 1..23) pairs, 0 violations of the odd-instant law; no point window at an even integer instant.
- Period and mirror: for integer readings the windows are 8-periodic and symmetric under R -> 8-R. The point windows at 1, 7, 9, 15, 17, 23 occur together iff a reading is 7 mod 8 and none is 0 mod 8 (1,254 sets; reading 1 supplies the "1 mod 8" side), and those at 3, 5, 11, 13, 19, 21 together iff readings 3 and 5 (mod 8) are both present and none is 0 mod 8 (876 sets). These are the pairs (1,7) and (3,5): at the progression readings 1..7 both classes are present, which is the pair law's four lonely instants as four point windows.
- Ties are forced the same way: at an odd integer instant r every reading = r (mod 8) is at p = 1 and every reading = -r (mod 8) at p = 7, so (#exits, #entries) = (#readings = r, #readings = -r) mod 8. Non-lattice ties need an extra rational relation: exit tie rho_a'/rho_a = (8j''+1)/(8j+1), entry tie (8j''-1)/(8j-1) ... (most common stored tied exits in J2: (rank 2 lap 1, rank 4 lap 2), ratio 17/9).
- Not forced by integrality (non-lattice touches): any rational ratio; E1 with rho_a = (8j+1)/7 (9/7, 17/7, ...; reading 1 enters at R0 = 7); X1 with rho_b = (8j'-1)/9; K1z with rho_6/rho_7 = 7/9 (all with irrational or arbitrary other readings, by corollary (b)).

## 4. Pair-law avoidance: the rule (PROVED), tests, counterexamples

Set: a window containing an instant of {8k+1, 8k+7} and an instant of {8k+3, 8k+5} (same period k = 0, 1, 2; windows never straddle (7,9) or (15,17)). A window is an interval, so this holds iff it contains [8k+1, 8k+3] or [8k+5, 8k+7] ([1,5] contains [1,3]; [3,7] contains [5,7]). Write x = 8k+1 or 8k+5, so the interval is [x, x+2].

**Rule R (PROVED).** [x, x+2] is clear iff every reading rho_y lies in I(x) = union over m >= 0 of [(8m+1)/x, (8m+7)/(x+2)].
Derivation: a reading's clear R-set is the union of the closed intervals [(8m+1)/rho, (8m+7)/rho] (positions [1,7] on lap m). [x, x+2] lies in one of them iff 8m+1 <= x rho and (x+2) rho <= 8m+7 for some m; the largest m with 8m+1 <= x rho is the best (`inI` in `tie_pair_v1.py`). Positions swept: the reading moves 2 rho in position, so 2 rho <= 6.
**Corollary R1.** Nonempty I_m needs 8m+1 <= 3x, hence every admissible rho <= (8m+7)/(x+2) <= 3(x+2)/(x+2) = 3, with equality only if 3x = 8m+1, i.e. x = 3 (mod 8), never for x = 1, 5 (mod 8). So **an occurrence needs rho_7 < 3, and then R* = 1 (no move).** x = 1: all readings in [1, 7/3]. x = 5: all other readings in [9/5, 15/7] (width 12/35). Larger x: finitely many narrow intervals (counts in `tie_pair_v1.out` section 2).

**Why the avoidance in the stored sets.** (i) lat1: distinct integers give rho_7 >= 7 > 3, so none (PROVED, R1). (ii) lat_M with readings c/M, c > M integers: the number of lattice points of I(x) is below 7 for every x in X and M = 1..4, so none (exact counts, M = 2, 3, 4 give 0 sets; `tie_pair_v1.out` section 2 lists the first M with sets: M = 5). (iii) The 18,452 J1 stored points: all have rho_7 >= 7 (minimum exactly 7; 0 with rho_7 < 3; the largest number of the seven readings lying in one I(x) is 4, at 1 point; counts 1: 14,474; 2: 3,963; 3: 14; 4: 1). (iv) near the progression (Lean hypothesis |d_j - j c| <= c/20): rho_7 = d_7/d_1 >= 139/21 > 3, so the pair law's neighbourhood never has a window holding both classes (PROVED from R1). In every case the avoidance is the reading condition rho_7 < 3 failing; it is not a feature of the cascade or of the J=1 box.

**Does a six/seven-reading condition forbid it for rho_7 <= 9 and not beyond?** No. The occurrence set (all seven readings in a union of intervals I(x), x in X) lies inside rho_7 < 3 and is nonempty there: it meets the J=1 reading range (rho_7 <= 9) and is empty for rho_7 >= 3, including every arrangement beyond 9. The avoidance is therefore stronger than a J=1 statement for rho_7 >= 3 and is false for rho_7 < 3.

**Sampler example 'grid+laps' 20982** (`tie_region_v1.out`): readings [1, 10888/10505, 4657/4202, 12392/10505, 13071/10505, 27061/21010, 28101/21010]; rho_7 = 28101/21010 (1.3375) < 7/3, so x = 1 holds; windows in [1,23]: [1, 147070/28101], [9, 105050/9367], [17, 483230/28101]; first window contains 1, 3, 5 (147070/28101 = 5.2336). Path word (), R* = 1, closer (7,1), width 118969/28101. **It lies in the J=1 tree region index 0** (stop region, path word (), reading box rho_2..rho_7 in [1,7]; the box test uses the float LP bounds of `terminals7_J1.pkl` rounded to rationals, the path equality is exact; the other path-() region, index 1, is the face rho_7 = 9). Its window set is **not** in `win_rec_J1_0_v1.pkl`: that file holds, for region 0, the label ('J1', 0) = the stored member [1, 981444729981389/562949953421312, ..., 7] (readings 1.74, 2.79, 3.85, 4.90, 5.95, 7 to two places) with 14 windows ([1,1], [17/7, ...], [25/7, ...], ..., [7,7], ...), a different set; the example's window set is in `win_rec_taxo_17000_v1.pkl` under ('taxo','grid+laps',20982) (compared equal). The window set is not a function of the path word: the path fixes only the first window's start and closer. So "no J=1 member has a window holding both classes" is a statement about the stored points (one per region, chosen with rho_7 >= 7), and its region-level form is false: region 0 contains arrangements with such windows.

**Tests of Rule R (direct = a window of `windows()` holds both classes; rule = some x in X with all readings in I(x))**: 0 mismatches on J1 18,452; sampler 52,000 (251 occurrences, all with the rule true); lat1 5,005; lat3 18,564; lat5 4,000; lat7 4,000; 20,000 built near progressions: family A (10,000, readings y(1+e_y), |e| <= 0.02..0.3 of five scales) 0 occurrences, 0 mismatches; family B (10,000, readings 1+(y-1)d plus deviation up to d/2, d = k/50, k = 1..25) 4,296 occurrences, 0 mismatches (examples in `tie_pair_v1.out`; seed 20261003; 14 s).

**Counterexamples to the weaker rules** (exact):
- "No window in the J=1 region holds both classes": the example above (region 0).
- "Lattices avoid it": lat5 {5,...,11}: readings 1, 6/5, 7/5, 8/5, 9/5, 2, 11/5, windows [1, 35/11], [25/2, 25/2], [205/11, 115/6], [125/6, 235/11], x = 1. lat7 {7,...,13}: first window [1, 49/13]. lat15 {15,27,...,32}: readings 1, 9/5, 28/15, 29/15, 2, 31/15, 32/15, windows [1,105/32], **[5,7]**, [85/9,345/32], [125/9,465/32], rule x = [1,5] (the [5,7] window is x = 5). The earlier lat5/lat7 zeros (`win_lonely_set_v1.md`, 4,000 random sets each) are not reached by random draws: M = 5 has exactly 1 set with x = 1, M = 7 has 84. Lattice counts for M <= 40 are in `tie_pair_v1.out` (for example M = 40: 22,957,480 sets with x = 1).
- No counterexample to Rule R was found (0 mismatches above); R is a derivation, not an inductive statement.

## 5. Status

| item | grade |
|---|---|
| Theorem T and corollaries (a)-(e) | PROVED (derivation) plus VERIFIED-INSTANCE (0 mismatches, all datasets) |
| type list S / E1 / X1 / N / ties; counts | VERIFIED-INSTANCE on the stated sets |
| K0z needs rho_7 >= 7; R* > 1 needs rho_7 > 7 | PROVED |
| K1z infimum 7 not attained; family rho_6 = 7 rho_7/9 | PROVED relation, VERIFIED-INSTANCE at four d |
| integer residue law; ties forced by residues | PROVED, VERIFIED-INSTANCE on lat1 (19,080 point windows; 115,115 odd-instant checks) |
| smallest-reading table (section 2) | VERIFIED-INSTANCE for R0 <= 23, v <= 12, endpoints <= 12; depends on the R0 range |
| Rule R, corollary R1 (rho_7 < 3), near-progression avoidance | PROVED; VERIFIED-INSTANCE, 0 mismatches in ~108,000 sets |
| region-level J=1 avoidance | false (counterexample, region 0) |

## 6. Exceptions and scope

- Stored tree points are one witness per region (LP vertex or small jitter), many on region faces (readings exactly 7 or 9: 143 of 161 zero-width J1 points). Every statement about "members" is about those points; K1z has no stored point though it exists in the range (rho_7 = 15/2).
- The old "p_7 = 7" statement holds for the 11 members of `disc_outcome_structure_v1.md`; in the present lists the closer takes every rank 1..7.
- Landing at R* = 7 with an opener other than (6,6): not reached by the stated search.
- Smallest-reading table depends on the stated R0 range; the infimum moves with R0 (single-point windows beyond R0 = 23 are outside the data).
- One float use: the region-box test for the example (LP bounds). The conclusion rests on the exact path word () and on rho_2..rho_7 in [1,7].
- Second-opinion gate on the pair-law derivation (CLAUDE.md section 7 adversarial pass) was not run in this task.
