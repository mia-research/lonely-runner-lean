# V8_2 isolated audit v1 — `MANUSCRIPT_v8_2.md` (833 lines, read in full)

Line numbers are those of `docs/n8/MANUSCRIPT_v8_2.md`. A finding that belongs to two rules or checks appears once, in the table that fits it best; other tables point to it and do not count it again. "Current" means the passage is v8's own framing. "Historical" means the passage labels it as v7's or the ledger's.

## R1. No window, no bound on when

| line(s) | quote | conflicts with | historical or current | minimal change |
|---|---|---|---|---|
| 68–69 | "the first runner's lonely instants during its nearest neighbour's first relative lap are exactly `1/8, 3/8, 5/8, 7/8`" | R1: the claim is tied to the first lap, but the differences 1…7 make it hold every lap (period 1 in `t`). Appendix A.1 (723–725) repeats the scoping | current (§1.2) | "are exactly the instants ≡ `1/8, 3/8, 5/8, 7/8` (mod 1)" |
| 297–298 | "Each runner's window re-anchors at its own `1/(8·d_min)`." | R1; 85 "v8 has no such window" | current | "Each runner's bound re-anchors at …" |
| 483–484 | "no `R ≥ 16` found in one round of adversarial search over `S ∈ [7, 10]`" | R1 (a cap on `R` is not required); 487 | current (§6.7 evidence) | Drop the `R ≥ 16` threshold, or say that no threshold on `R` enters Existence |
| 642–646 | "**Order 5 is open.** In the cascade's quantity it is `R = d_min/D_final < 4`. `[OPEN]`", followed by "`R < (3/2)³ = 27/8`" and "the largest `R` found is `≈ 31/9`" | R1 (`R < n − 1` is named as a bound that is not a requirement); 441–443 (the open statement is a fixed point, not `R < 4`) | current | "Order 5: Existence with four differences at `n = 5` is open". If `R < 4` is kept, label it a sufficient condition |
| 649–650 | "Largest nearest readings found at `n = 6, 7, 8, 9`: 8.60, 9.04, 11.66, 10.66, each below `2n − 1`." | R1 (`R ≤ 2n − 1` is named as a bound that is not a requirement) | current | Delete "each below `2n − 1`" |
| 731–732 | "a reading `s` has about `3s/4` zones per lap of the nearest runner — seven readings supply about 24" | 156: the zones `((8k − 1)/(8s), (8k + 1)/(8s))` give `s` zones per unit of `u`. `3s/4` is the count inside `[1/8, 7/8]`, the withdrawn window | current (Appendix A.2, no label) | "about `s` zones per lap", and recompute "about 24", or label the figure as v7's window count |
| 741–742 | "A reading `s = 8` does split the nearest runner's first lap into 7 zones and 6 clear intervals of `3/32`" | Over `u ∈ [0, 1)` the clear intervals of `s = 8` are `[(8k+1)/64, (8k+7)/64]` for `k = 0…7`, which is eight. Line 170 uses `[57/64, 63/64]` as one of them. Six is the count inside `[1/8, 7/8]` | current (Appendix A.3, no label) | "8 clear intervals (6 inside v7's window `[1/8, 7/8]`)" |
| 738–739 | "none of the 231,294 reaches `u = 7/8`" | R1: `7/8` is the edge of the withdrawn window, used here as the benchmark | current (Appendix A.2 data) | Delete the clause; the maximum `0.589` is already given |

## R2. The cascade is not a search, prediction or picking

| line(s) | quote | conflicts with | historical or current | minimal change |
|---|---|---|---|---|
| 53; 81; 474 | "the construction is unchanged and returns an irrational instant"; "§6 proves what the cascade returns"; "eight distinct positive speeds with gcd 1 return for every runner" | R2 ("returns" in the algorithmic sense); 332 (the cascade is a sequence of moves, not a procedure that returns) | current | "names", "reaches" and "have a lonely instant for every runner", respectively |
| 818 (with 809–810) | "each step is a finite test — at scale `D = k·d_min`, `4k` candidates; no search is performed." | R2 ("candidates"); 330–332 (a move is fixed by the runners in the way; there is no candidate set) | Appendix C, dated to "the construction as it stood when tested, 2026-09-14" (791–792); not labelled v7 | "each step is one move (§6.1), fixed by the runners in the way at `t`" |
| 800 | "the rules fired for 76.7–87.0%" | R2 ("rules" in the sense of v7's predictor) | ledger, 2026-09-14; not labelled v7 | Label it as the rule-based construction before v8 |
| 827–830 | "either by rules whose conditions are exhaustive or by proving that the stepping reaches its instant"; "every runner the rules missed had at least one difference that is a multiple of `8g`" | R2 ("rules", "missed"); R4/R6 (conditions that exhaust the space are a covering route); 441–443 (the obligation is Existence) | current: it sits under "What remains" and is offered as where to start | State the obligation as Existence only. Label the note on missed runners as data from the old rules, integer differences only (see also R3) |
| 376, 579; 433; 688 | `exists_clear_candidate`; `WHY_IT_PREDICTS_v1`; `complete_predictor_replication_v1.py` | R2 (these are legacy names in current citations) | current citations of names that cannot change | No change to the names; optionally note once that they are legacy names |

## R3. Scale-free; irrational speeds are not a separate case

| line(s) | quote | conflicts with | historical or current | minimal change |
|---|---|---|---|---|
| 51–53 | "For commensurate speeds … an isolation instant is *named*. For incommensurate speeds the construction is unchanged and returns an irrational instant" | 14 ("a construction that names instants"); 18 ("the same construction runs on real speeds"). "Named" is attached to the commensurate case only | current | Say that the instant is named in both cases and only the arithmetic of the test differs |
| 831–833 | "Two objections stand …: … exactness holds only for commensurate speeds (§1.1, §2.2) — a claim about the method, not a failure of it" | R3: exact rational computation is fine and is not a limitation. It is listed as a standing objection | current (Appendix C closing paragraph) | Remove it from "objections stand" |
| 353; 360 | "step `D` is dead for difference `d` iff `d = 8k` with `D \| k`"; "For integer readings, with a slot-sharer at reading `S_b`" | 344, 349: scales are real (`D_final = 7/9`), and 351 defines slot-sharing for a real `D` ("a multiple of `8D`"). The dead lattice and the one-slot step are stated only for natural `D`, `d` and integer readings | current | Label them as the integer representation, or give the real form (`d/D ∈ 8ℤ`) |

## R4. Firewall

| line(s) | quote | conflicts with | historical or current | minimal change |
|---|---|---|---|---|
| 523 | "and the slowest runner's lap is the cycle in which instants are counted" | R4 (no global clock); 156 (instants are read in the per-runner coordinate `u = d_min·t`); 45–46. No other line counts instants in the slowest runner's lap | current (a firewall qualification) | Delete the clause, or replace it with "each runner's instants are read in its own `u = d_min·t`" |
| 288; 736–738 | "Of the 77,400 anchored arrangements to `v_8 ≤ 20`"; "Over every arrangement to `v_8 ≤ 20` …"; "(at `(0, 2, 8, 10, 11, 13, 16, 17)`, runner 0" | R4 (no stationary frame). 77,400 is exactly the number of arrangements `0 = v_1 < … < v_8 ≤ 20` with gcd 1 (Möbius sum over `C(⌊20/g⌋, 7)`), so these are pinned-frame enumerations. 471–474 carries the pinned-frame caveat for the `v_8 ≤ 40` sweep only | current | Add the caveat and the difference-invariance sentence of 471–474 |
| 580 (with 383–385) | "`Run.covers`" in the Theorem 6.2 row. The Lean docstring reads "A run covers everything from its start up to its end" | R4 (no covering language); 525 | current (declaration name; the prose avoids the word) | Drop `Run.covers` from the row or gloss it. The Lean name cannot change |
| 746–747 vs 170 | "the clear interval `((8k+1)/(8σ), (8k+7)/(8σ))`" vs "the clear interval `[57/64, 63/64]`" | R4 (boundary discipline). Zones are open (61–62), so clear intervals are closed; 747 writes one open | current | `[(8k+1)/(8σ), (8k+7)/(8σ)]` |

## R5. The conjecture is named once, in §9

| line(s) | quote | conflicts with | historical or current | minimal change |
|---|---|---|---|---|
| 806 | "Producing an instant does not settle the conjecture \| an instant at which a runner is lonely is what the conjecture asks of that runner (§9)" | R5 (a second link between the framework's output and the conjecture, beside 667); 779 ("the conjecture is named once, in §9") | Appendix C, ledger 2026-09-14; not labelled v7 | "an instant at which a runner is lonely is Existence for that runner (§6.7, Corollary 6.4)", or delete the row |

## R6. Imports from other Lonely Runner work

| line(s) | quote | conflicts with | historical or current | minimal change |
|---|---|---|---|---|
| 165–167; 616–618 | "it would need `1/(4s′) ≥ 3/(4σ)`, that is `s′ ≤ σ/3`"; "Whatever obstruction these local bounds present, it is not weaker at larger `n`." | R6 (zone-length comparison used as the framework's reasoning). Prop 3.3 compares a zone's length with an interval's length. 616–618 presents the length bounds as an obstruction to the result | current | State Prop 3.3 as endpoint containment. Delete the "obstruction" sentence |
| 742–745 | "so the conclusion survives with margin, but the counting argument for it does not"; "Over 300,000 draws of five readings, the most closed was three of the six" | R6: this is a counting frame of readings against intervals, refuted in the same item, yet used to keep a conclusion that holds only in the first window (see R1, 741–742) | current (Appendix A.3) | Delete "the conclusion survives with margin", or label that conclusion as v7's |

Also R6, counted elsewhere: 827–830 (exhaustive rules, see R2) and 288/736 (pinned enumerations, see R4).

## R7. How long, how much, when: not obstacles

| line(s) | quote | conflicts with | historical or current | minimal change |
|---|---|---|---|---|
| 466–467; 487 | "No ceiling on the number of moves has been found"; "Nothing here bounds the number of moves or `R` for every arrangement." | R7: how long the cascade runs is presented as a missing result; 823–824 | current | Replace with "Existence is open (above)". Drop the framing about bounds on moves and `R` |
| 475–476 | "Nothing above `v_8 = 40` is in the sweep." | R7: how much of the space is covered is presented as a limitation; 469 already gives the scope | current | Delete |
| 830–831 | "Two objections stand and are stated where they apply: the evidence is finite (§6.7)" | R7; 823–824 (the test Appendix C itself states) | current | Remove "the evidence is finite" from the standing objections |
| 652 | "**What does not carry over.** The reach figures of §4.5 and the evidence of §6.7 are measurements at order 8." | R7 (coverage presented as a limitation); also C5 (276, 772: these shares are "not the construction's reach") | current | "The settled-at-once shares of §4.5 and the counts of §6.7 are order-8 computations." |

## C1. Each object named and defined one way

| line(s) | quote | conflicts with | historical or current | minimal change |
|---|---|---|---|---|
| 113 vs 482 | "where `R = (d·a) mod m`" vs "The time ratio `R = d_min/D_final`" | `R` has two definitions | current | Rename the residue in Prop 2.1 (for example `ρ`) |
| 142, 233, 283, 355 vs 468, 483 | "makes the gap `S/7`"; "`S` is the spread"; "`S ≤ 7·m*`"; "at most `S/(8g)`" (all in speed units) vs "at most `(7/8)·S·R + 7`"; "spread `S = d_max/d_min ≈ 7.44`" (a ratio) | `S` means the speed spread in one group and `d_max/d_min` in the other. The move-count bound at 468 holds only with the ratio. 360 adds `S_b` | current | Use a separate symbol for `d_max/d_min` |
| 93–94 vs 118, 128, 340 | "`D = { d_j = \|v_j − v_i\| : j ≠ i }` and `d_min = min D`" vs "at the instant `1/(8D)`", "every real gap `D > 0`" | `D` is the set of differences in one place and the scale in the others | current | Rename the set |
| 344, 349 vs 809–810, 818 | "`D_{j+1} = D_j · min{ s/(8N + 1) : … }`", "ends at `D_final = 7/9`" (with `d_min = 1`) vs "The gap is a scale, `k·d_min`"; "at scale `D = k·d_min`" | The cascade's scales fall below `d_min` (`7/9 < 1`). `k·d_min` with integer `k ≥ 1` never does. "Scale" has two incompatible definitions | Appendix C, 2026-09-14 | "The gap is a real scale (§6.2)" |
| 186 vs 232 | "both gaps flanking it on the track" vs "the two speed gaps flanking a runner" | "Flank" means track neighbours at 186 and speed-order neighbours at 232; 96 separates the two orderings | current | At 232: "the two speed gaps adjacent to it in speed order" |
| 258–259 vs 395–402, 23 | "(d) **Integral readings localise.** … lonely at some `u ∈ [1/8, 7/8]`" vs "**Theorem 6.3 (Localisation).**" | "Localise" names two different statements. The one at 258 is a first-window statement | current | Rename (d), for example "Integral readings recur each lap" |
| 300 vs 98 | "pinched between the readings `9/8` and `15/8`" vs "The readings are `s_j = d_j/d_min`" | The readings are 3 and 5; `9/8` and `15/8` are their positions `s·u` | current | "between the positions `9/8` and `15/8` of the readings 3 and 5" |
| 523 vs 156, 383 | "the slowest runner's lap" vs "one per lap `k` of the reading" and "a runner's `N`-th relative lap" | "Lap" is a relative lap everywhere except 523 (counted under R4) | current | See R4 |
| 80, 161, 242, 340–341, 498 | "first spine point"; "the progression's spine"; "the spine instant indexed by a unit `p`"; "the spine `r = 3` of scale `δ`" | "Spine" is used five times and never defined; 132 describes the instants `r/(8D)`, `r` coprime to 8, without the name | current | Define "spine" once in §2.3 |
| 112, 282, 326; 410–412 vs 596 | "`t = a/m`"; "`m*` the smallest speed gap"; "`m = d_min`"; "the instants `n/(8m)`", "`n = 8K + r`" vs "threshold `1/n`" | `m` has three meanings. `n` is the own-AP index in §6.6 and the order in §8 | current | Rename the own-AP index (for example `j`) |
| 360–363 vs 332 | "at `u = p/8 + 1/(8·S_b)` … This is one move of the cascade" vs "The **cascade** is the sequence of moves from the **bound** `1/(8m)`" | The step starts at `u = p/8` for any unit `p` (the bound is `p = 1`). It is a §6.1 move only if the slot-sharer is the only runner in the way there; readings with `s·p mod 8 = 7` are not covered | current | "This is a §6.1 move when the slot-sharer is the only runner in the way at `u = p/8`" |
| 474–475 vs 10, 596 | "eight distinct positive speeds with gcd 1 … at thresholds `1/5` to `1/10`" | Elsewhere the threshold is `1/n` for `n` runners (`1/8` for eight). Eight speeds at `1/5` does not match that | current | State the runner count for each threshold |

## C2. Counts and identifiers agree

| line(s) | quote | conflicts with | historical or current | minimal change |
|---|---|---|---|---|
| 482, 739 vs 649 | "largest found **≈ 11.96**"; "`R ≈ 11.96`" vs "Largest nearest readings found at `n = 6, 7, 8, 9`: 8.60, 9.04, 11.66, 10.66" | At the fixed point the nearest reading is `d_min/D_final = R` (647–648). The order-8 maximum is 11.96 in two places and 11.66 in one | current | Reconcile the figure, or state the two populations |
| 29–30 vs 544–546 | "both with no `sorry` and every theorem on `propext`, `Classical.choice` and `Quot.sound` alone" vs the `Construction8` axiom cell: "the gate checks 23 headline declarations; the 16 further …" | §7 claims "**every theorem**" only for `Cascade`. For `Construction8` it reports 23 + 16 = 39 of 85 declarations checked | current | Abstract: "every `Cascade` theorem, and every `Construction8` declaration cited" |
| 466–467 | "an adversarial climb over speeds up to 400 reached 29, at `(27, 70, 107, 137, 159, 188, 344, 393)`, runner 393" | The §6.1 move, iterated in exact rationals from `1/(8·49)`, reaches `t = 49/1872` after **28** moves. The same code gives 23, 22, 1, 1 for the four integer rows of §6.8, matching 493–496, so the counting convention is the table's | current | Re-run and state 28, or state the convention that gives 29 |
| 144–145 | "of the 45,568 eight-subsets of `[1, 20]` that fit …; of the 80,357 that do not fit" | 45,568 + 80,357 = 125,925, but `C(20,8)` = 125,970. The difference, 45 = `C(10,8)`, is the subsets with gcd 2, so the population is the gcd-1 subsets. That filter is not stated | current | "eight-subsets of `[1, 20]` with gcd 1" |

## C3. Grades agree

| line(s) | quote | conflicts with | historical or current | minimal change |
|---|---|---|---|---|
| 832–833 vs 798, 443 | "the incommensurate runners are proved lonely at their instants (§6.8)" vs "now also proved on instances in Lean (§6.8)" and Existence "`[OPEN …]`" | Two proved instances are graded as if every incommensurate runner were covered. That is Existence, which is OPEN | current | "the incommensurate instances of §6.8 are proved lonely" |
| 433; 356 | "(`WHY_IT_PREDICTS_v1` §2). `[PROVED there]`"; "`[PROVED — revision-list item 21]`" | Both are graded PROVED on working documents, with no proof in the text and no Lean row. 320 says "Nothing else is cited" | current | Grade as `[DERIVED — working document]`, or give the proof in the text |

## C4. §7 table of Lean declarations

Every declaration name the manuscript cites was found as a `theorem`/`def`, or as a namespace for the `.*` entries, under `LonelyRunner/LonelyRunner/LRC/{Construction8,Cascade,ConstructionN}`. That covers 104 extracted names plus `lonely_iff_flanks_first`/`_last` and `nearest_on_ideal_below`; `TerminationThree` and `TerminationFour` are namespaces in `Cascade/SmallOrders.lean`. The statements of the cited `LemmaPass`, `Bounds`, `Iteration`, `SmallOrders`, `FourDifferences`, `VersionB` and `Irrational` declarations were read against the text; none claims more than the text states.

| line(s) | quote | conflicts with | historical or current | minimal change |
|---|---|---|---|---|
| 221 | "global isolation forces commensurable speeds (`commensurable`)" | No §7 row names `commensurable`. It exists (`Construction8/LemmaPass.lean`) and is in `v8_axiom_check_v1.lean` | current | Add it to the Thm 4.7 row |
| 627–630, 635–640 vs 585 | `two_diffs_stop_within_one_move`, `three_diffs_stop_within_three_moves`, `four_diffs_stop_ge_six`, `stops_slowest_recursion`; `move_growth`, `return_growth`, `return_lemma`, `no_return_after_faster`, `no_four_alternation`, `no_return_after_few_faster`, `nearest_reading_recurrence` | All are graded "`[PROVED — Cascade]`" (622), but row 585 names only the `VersionB` forms plus "the sections behind them". All exist, in `SmallOrders.lean` and `FourDifferences.lean` | current | List them in row 585 |
| 316 vs 576 | "`instants_on_grid`, `coprime_of_isolation`, `isolation_forces_coprime_grid`" vs row 576 (three names) | `instants_on_grid` and `coprime_of_isolation` are cited but have no row | current | Add them to row 576 |
| 587–588 vs 601–602, 610–611 | "only the `2σ` containment is formalised" vs "Six carry `n = 8`, all of them the zone geometry of §3: … the two ratio bounds" and the rows "first-zone overlap (Appendix A, 2)" and "descent through consecutive integers" | The Appendix A.2 bounds are formalised: `Construction8.first_stretch_overlap` (the `9/7` bound) and `Construction8.consecutive_break` (`2s > 9`), both in `Coords.lean`. Line 602 also places them in §3, while 610–611 place them in Appendix A | current | 587–588: "the `9/7` overlap bound and the consecutive-integer break (`Construction8`) and the `2σ` containment (general-`n` line) are formalised". 602: "§3 and Appendix A.2" |

## C5. Contradictions

| line(s) | quote | conflicts with | historical or current | minimal change |
|---|---|---|---|---|
| 53–55; 498 | "returns an irrational instant … `Irrational` proves every runner … lonely at its named instant, the second runner at the irrational `75√2/4`"; row: runner 2, "clear at the spine `r = 3` of scale `δ`", instant `75√2/4` | Theorem 6.2(b), 382. The §6.1 cascade for runner 2 of `(1, 1 + √2/100, 3, …, 8)` makes 2 moves from `1/(8δ)` ≈ 8.8388 and fixes at `(62 + 1/8)/(7 − √2/100)` ≈ 8.89297, which is lonely (a brute-force check over all openings up to 9 gives the same earliest instant). So `75√2/4` ≈ 26.5165 is a lonely instant but not the cascade's. Runner 1's `71/8` does match the cascade | current | Call `75√2/4` "a lonely instant proved in Lean", not the construction's instant; or give the cascade instant `497/(8(7 − √2/100))` |
| 99 vs 173–176, 647 | "**Seven differences, one of which realises `d_min`, leave six readings to evaluate**" vs "in the way either of the baseline …" and "From order 6 the nearest runner itself can set a move" | The `d_min` runner (the baseline) can be in the way and can set a move, so it is evaluated too | current | "all seven readings are evaluated, the `d_min` reading included" |
| 301 | "the end runners' `d_min` grows to `1 + ε` with `d_max = 7 + ε`" | For `(1 − ε, 2, …, 7, 8 + ε)`, `d_max = (8 + ε) − (1 − ε) = 7 + 2ε`; exact check at `ε = 1/40` gives `141/20`. The conclusion (Thm 4.8 holds) survives, since `7 + 2ε ≤ 7(1 + ε)` | current | `d_max = 7 + 2ε` |
| 615 vs 613 | "The remaining five forms hold for every `n ≥ 1`." vs "`2σ` containment … needs `n > 3` (`two_sigma_zone_inside`)" | One of the five needs `n > 3`, and the overlap bound `(n+1)/(n−1)` is undefined at `n = 1` | current | State the range of each form |
| 652 vs 276, 772 | "The reach figures of §4.5" vs "These percentages are not the construction's reach" and the Appendix B entry "relabelled 'settled at once' rather than 'reach'" | "Reach" is used for the figures the manuscript says are not reach (counted under R7) | current | See R7 |
| 779 vs 806 | "the conjecture is named once, in §9" | 806 links to the conjecture a second time (counted under R5) | current | See R5 |
| 427–428 | "`m′_l` even and at most 8 is never in the way" | The rule on 426–427 applied to `m′ = 8`, `u = 1` (the `d_min` runner) at `n = 8` gives `8 mod 8 = 0`, strictly within 1 of 0: in the way. It holds only for odd `n` | current | "is never in the way at odd `n`" |
| 225 vs 258–259 | "Each row gives a class of runners whose first cascade step is already clear, so Existence holds for them." vs "(d) **Integral readings localise.** … lonely at some `u ∈ [1/8, 7/8]`" | (d) gives no class whose first step is clear; it assumes loneliness | current | Move (d) out of §4.5, or qualify the heading |
| 642 vs 441–443 | "Order 5 is open. … `R = d_min/D_final < 4`" | The open statement is defined as reaching a fixed point (counted under R1) | current | See R1 |
| 741–742 vs 170 | "6 clear intervals" of `s = 8` vs "the clear interval `[57/64, 63/64]`" of `σ = 8` | 170 uses an interval of reading 8 that 741–742 leaves out (counted under R1) | current | See R1 |
| 809–810, 818 vs 344, 349 | "`k·d_min`" vs "`D_final = 7/9`" | Counted under C1 | Appendix C | See C1 |

## Summary

Findings per rule or check. Pointers to another table are not counted twice.

- **R1:** 8. The most significant is 642–646, where order 5's open statement is given as `R < 4`.
- **R2:** 5.
- **R3:** 3.
- **R4:** 4.
- **R5:** 1 (line 806).
- **R6:** 2.
- **R7:** 4.
- **C1:** 11 (the lap row is counted under R4).
- **C2:** 4.
- **C3:** 2.
- **C4:** 4.
- **C5:** 6. The most significant is 53–55/498: the §6.8 irrational instant `75√2/4` is not the cascade's instant, which is ≈ 8.89297 after 2 moves.

Total: 54.

No rule or check came out entirely clean. What was checked and found clean within them:

- **R1:** 84–85, 175–176, 292–295, 456, 477–481, 502–511, 766, 785 and 810–811 mention the window only as labelled v7 or withdrawn history.
- **R4:** "blocked" appears only in Lean declaration names (`blocked_width`, `blocked_lands_on_threshold`, `unblocked_stays_clear`, `drift_blocked_iff_interval`); the prose uses "in the way". The pinned `v_8 ≤ 40` sweep carries its caveat (471–474). Zones are open and clear sets are closed at 61–62, 123, 155–156, 170, 330 and 383.
- **R5:** 9–12, 667 and the reference titles are the permitted uses.
- **R6:** 320, 802–804, Appendix A.1 and 781 use imported frames only as refutations.
- **C2:**
  - Figures that agree: 207,464 (464, 688); 124,488 (347, 688); 29,320 (390, 689); 40,000 (429, 583, 689); 4,800 (374, 477); 231,294 (737–738).
  - Lean artefacts: 85 and 135 theorems, 11 and 7 modules, and the module lists (29, 542, 600, 541, 679–683).
  - Axiom-check counts: 23 + 16 + 7, with 3 re-checks, gives 26. This matches `v8_axiom_check_v1.lean` and `.out` and `scripts/n8/gate.sh`.
  - Recomputed: 148,514,528 = 8 × 18,564,316. 18,564,316 and 77,400 match Möbius counts. 12,870 = `C(16,8)` and 24,310 = `C(17,8)`.
  - The §6.8 integer rows (moves, instants, `u`) and the `(1,…,6,8,9)` chain ending at `D_final = 7/9` reproduce in exact rationals.
  - The `Construction8` digest matches the current tree. The `Cascade` digest `9657ea89…`, 135 theorems and 7 modules match commit `21a7748`. The current `Cascade/` directory (9 modules, 161 theorems, digest `a1916b1e…`) postdates the manuscript (commits `a4a5d6c`, `e706d5d`). That is drift on disk, not an internal inconsistency.
- **C3:** The grades of Construction, Localisation and Existence agree across the abstract, §6, §9 and Appendix B. Prop 6.7 is graded DERIVED/VERIFIED in both 429 and 583.
