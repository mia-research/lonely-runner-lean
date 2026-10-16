# Order six, framework route — working log v1

Started 2026-10-15. Scope: order six (and lower orders where relevant). Order eight is a separate
project and is not worked on here.

## Owner rulings and corrections, verbatim (2026-10-15)

1. On the two tracks: *"So we have two tracks, classical proof, framework reproof. We got to 6 where we
   were seeing if there is a genuine native way or BHS reformulated. Reformulated was not taken off the
   table, we just wanted to see what happened if we looked. Then you have thought "what would a proof
   look like" instead of reasoning and reverted back to the mean/training data"*
2. On number theory: *"Primality isn't native but totients are."*
3. On drift: *"Woah, why are we using primality again? Counting and coverage also seemed to be used. I
   think we have drifed"*
4. On which framework-native test to run: approved restarting by running the cascade on the order-six
   residual sets and recording moves, setters and displacements, patterns only, no proof framing.
5. On scope: *"Yes we aren't working on n=8 here that is another project not for this session"*
6. Earlier the same day, on counting (superseded in effect by 3 and 1): approved trying "finite check for
   e <= 36, plus an argument that the openings meet the lonely set for larger e", with counting or
   sampling steps tagged provisional. The attempt drifted into rate and coverage statements; see below.

## Entries

**E1. Native steps (keep).** `SixCells_v1.lean`: `all_shifts_blocked_iff` (residue pinning from
no free flank) and `cell_criterion` (cell reduction at a flank e = 6E), both axiom-clean
(`SixCells_v1.out`). `six_crt_coprime_v1.out`: exact CRT form of the criterion at a flank coprime to 6
(110,964 openings, 0 mismatches). `cells_general_n_v1.out`: cell criterion at n = 6, 7, 8 with 0
mismatches, and the coarse blocking sets: n = 6 two patterns, n = 7 none, n = 8 one.

**E2. Drift (set aside as evidence of method only).** `six_named_*` (named multipliers, at chance per
`six_named_null_v1.out`), `six_tight_patterns_v1`, `six_window_mechanism_v1` parts (ii)–(iii),
`six_folded_coverage_v1`, `six_folded_failures_v1`: measure, density, sampling and covering statements.
`six_window_mechanism_v1` part (i), an exact identity (0 mismatches), stands. The relation
"#openings ≈ |L|·e" was already recorded in `docs/nN/HANDOVER_2026_09_21_v1.md` §2.6.

**E3. Restart: cascade observation.** `six_cascade_observe_v1.{py,out,tsv}`, `six_cascade_meeting_v1.{py,out}`
(17,135 primitive residual sets, [1,40]). Patterns only; recorded in the session report of 2026-10-15.

Feedback memory: `feedback_native_route_observe_not_proof_shape_2026_10_15.md` (auto-memory directory).

**E4. Setters observed and the exact parts formalised (2026-10-15).**
- `six_cascade_setters_v1.out`: setter sequences per BHK case. §8: only ranks 4, 5 set moves (ranks 2–3
  in 5 of 3,716 sets). §7: runner 3 the commonest first and final setter. §5: runner 2 in place of
  runner 3. Laps almost always 1; the slowest element ends in [1/6, 1/3) of its first lap in 97–99.8%
  of sets per case. Counts, not rules.
- `six_first_setter_v1.out`: first move = latest next opening among elements with |v/v1 − 6m| < 1;
  0 mismatches over 17,135 sets. In §8 only ranks 4, 5 are in the way at 1/(6 v1).
- `six_s6_sequences_v1.out`: §6 (v3 = cD, v2 = (c−1)D) sorts by c: final flank most often none (c = 2, 6),
  3 (c = 3), 4 (c = 4), 2 (c ≥ 8); runner 3 ends it 5 times of 403 at c = 6. Counts; not understood.
- `CascadeFirstMove_v1.lean` (`.out`): `first_move` (blocking test, opening formula, setter = latest
  opening) and `s8_slow_three_clear`, both [propext, Classical.choice, Quot.sound]. Packaged from
  `inWay_at_scale_iff`, `nextOpening_at_scale`, `move_eq_self_or_opening`, `nextOpening_le_move`,
  `Flanks.clear_at_bound_of_ratio`; no new mathematics.

**E5. §6 by c, and the later moves (2026-10-15).**
- `six_s6_by_c_v1.out`: with v2 = (c−1)D, v3 = cD, runner 2 is clear at runner 3's opening k < c exactly
  when 2c − 1 ≤ 6k (exact; residue 7c − 1 − 6k mod 6c). Counts: runner 3 ends the cascade 88 times at
  c = 3, 4–24 times at c = 2, 4, 5, 7, 5 times at c = 6 and at c ≥ 8. The link between the later first
  usable opening and the endpoint is an observation, not derived.
- `six_later_moves_v1.out`: at every later move (25,638), blocking is the residue criterion at the
  current flank opening (0 mismatches) and the next setter is the blocked element with the latest
  nearest-lap opening (0 mismatches). After a move, 0 or 1 elements are usually in the way.
- `CascadeResidueWalk_v1.lean` (`.out`): `later_move_blocking`, `s6_runner2_at_runner3`, both
  [propext, Classical.choice, Quot.sound].

**E6. Walk transitions and the early ending (2026-10-15).**
- `six_walk_transitions_v1.out`: state = (rank of flank, opening k), start (1, 0). §8: 32 transition
  types, 28 paths (dominant (1,0)→(5,1), (1,0)→(4,1), (1,0)→(5,1)→(4,1)). §5–§7: 168–287 types; 147 of
  327 types appear only in sets with max > 30; k up to 14. Not a finite pattern on this range.
- `six_walk_end_v1.out`: staircase exact (8,240 all-k=1 walks, setters strictly decreasing). Early
  (v1·T < 1/3): 16,530; late: 605 (436 need opening k ≥ 2; 68 end at k = 1 of a flank x < 3.5 v1;
  the rest on or near the boundary). Early ⇔ v1(6k+1) < 2x at the final state.
  Open: why the first lonely instant falls at a low opening (k ≤ 2) of a fast flank.
- `CascadeStaircase_v1.lean` (`.out`): `staircase`, `early_iff`, both [propext, Classical.choice, Quot.sound].

**E7. Late walks and the §8 pattern (2026-10-15).**
- `six_late_walks_v1.out`: of 605 late walks, 511 are forced to an opening k ≥ 2, almost always at a slow
  flank (rank 2 or 3, opening 1) blocked by runner 4 or 5; in 321 the setter is a return. The other 94
  end at opening 1 of runner 2 or 3. Lateness = the staircase descending to the slow flanks.
- `six_s8_reduction_v1.out`, `_v2.out`: in §8 the walk of S equals the walk of {v1, v4, v5} in 3,710 of
  3,716 sets ([1,40]); over [1,72], 267 exceptions in 63,346 sets, growing with the range, many with v3
  at or near 3 v1. Not a finite-exception statement.
- `six_s8_step_rule_v1.out`: (A) slow three clear at 7/(6 v5) when 5 v1 < v5 < 7 v1 (2,288 sets, 0 exceptions);
  (B) after (1,0)→(5,1) the walk moves to (4,1) iff 7 v4 > 5 v5 (1,741 walks, 0 mismatches).
- `CascadeSecEight_v1.lean` (`.out`): `s8_slow_clear_at_v5`, `s8_v4_steps_on`, both
  [propext, Classical.choice, Quot.sound].

**E8. §8 exceptions and returns (2026-10-15).**
- `six_s8_exceptions_v1.out` ([1,60]): 88 §8 sets with a slow runner ever in the way; 84 first at (4,1)
  with runner 3, 2 at (4,1) with runners 2 and 3, 2 at (5,3); 86 of 88 reached by (1,0)→(5,1)→(4,1).
  Rule "runner j (2, 3) blocks at (4,1) iff 5 v4 < 7 v_j": 8,954 visits, 0 mismatches.
- `six_returns_v1.out` ([1,40]): 923 sets with a return; 176 immediate (all satisfy the return lemma's
  4Q < 2P + 1; ladder (P,Q,P') = (2,1,3), (5,2,6), (7,3,8)); 1,012 delayed, commonest laps (1,1,1,2):
  fast x at lap 1, two staircase steps, x back at lap 2. The existing return lemma covers immediate
  returns only.
- `six_delayed_return_v1.out`: x@1→y@1→z@1→x@2 occurs with 11 z < 7 x < 13 z in 342 of 342.
- `CascadeSecEight_v2.lean` (`.out`; supersedes v1, kept): `opening_one_blocks_iff` with instances
  `s8_v4_steps_on`, `s8_slow_blocks_at_v4`; `CascadeOpeningOne_v1.lean` (`.out`): `opening_one_inWay_iff`
  (x in the way at 7/(6z) iff |7x − 6Nz| < z for some N). All [propext, Classical.choice, Quot.sound].

**E9. Delayed returns against the proved growth window (2026-10-15).**
- Correction to E8: delayed returns ARE covered as a necessary condition by `ChainBounds`
  (`LonelyRunner/LRC/Cascade/SmallOrders.lean`): `move_growth`, `return_growth`, `return_needs_moves`
  (a return after laps Q_1..Q_m needs prod (nQ_j+1)/(nQ_j-1) > (nP+n-1)/(nP+1)).
- `six_returns_growth_v1.out` ([1,40]): 1,188 returns, all inside the window L < t'/t < U; return lap
  P' = P + 1 in 1,100. Position in the window (fifths from L): 344, 424, 258, 101, 61; tightest 0.6% above L.
  Commonest shapes (P, laps between, P'): (1,(1,1),2) 342; (2,(1),3) 90; (1,(1,1,2),2) 49; (1,(1,2),2) 36.
- Reading: the growth window is used throughout, so a sharper growth bound is not what is missing; the
  converse (which runner returns, and when) is the opening reading step by step. "P' = P + 1" in 93% is the
  pattern to examine next. Observations only.

**E10. Return exceptions and outliers understood (2026-10-15).** Owner: "We need to look at the
exceptions, counter examples and outliers and understand why not accept then as narrowing."
- `six_return_exceptions_v1.out`: all 88 lap-skipping returns (P' ≥ P + 2) explained exactly: x returns
  at the integer nearest its reading (P + 1/6)g, and skips iff g > (6P + 11)/(6P + 1). The threshold falls
  towards 1 as P grows, so skips come from high P with one move ((5,(1),7)) or low P with many moves
  ((1,(1,1,1,2),3)). The 93% next-lap returns are the same rule below threshold; not a separate law.
- Outliers: position in the growth window is set by depths. Near U (61): mean setter depth 0.146 of the
  maximum 1/6 (setters caught at the edge). Near L (344): mean setter depth 0.066, x re-enters at depth
  mean 0.112 (just inside its zone). Same mechanism (opening readings) throughout; no new phenomenon.
- `CascadeReturnLap_v1.lean` (`.out`): `return_reading`, `lap_skip_iff`, `move_factor`, all
  [propext, Classical.choice, Quot.sound].

**E11. Earlier exceptions re-examined (2026-10-15).**
- `six_s8_exc_explain_v1.out` ([1,60]): 86 §8 exceptions on (1,0)→(5,1)→(4,1), all three step conditions
  hold, and v_j > 125 v1/49 (observed minimum 25/9). The other 2, (4,9,12,18,45) and (5,6,15,22,56), take
  (1,0)→(5,2)→(4,1)→(5,3): immediate return of v5 at lap 3, then runner 3 (v3 = 3 v1) reads just past 5/6.
- `six_late_explain_v1.out` ([1,40]): 605 late walks = 51 BOUNDARY (v1(6k+1) = 2x exactly; artefact of the
  cut-off) + 68 SLOW END (staircase to runner 2 or 3 in 3–5 moves, every step 5x < 7y < 7x) + 486 HIGH LAP
  (return 307, fresh setter near its lap 2 165, first move at lap 2 14).
- `six_largest_exc_explain_v1.out`: the 10 divisible-largest exceptions have E = e/6 in {1,2,3,5}; every fine
  cell vector is in the bad set (i = 0 gives (0,0,0,0), bad by no free flank). Most openings of e are
  blocked by exactly one element. The 3 non-divisible ones: (2,6,8,10,11) = 2·(1,3,4,5) + 11,
  (3,6,9,15,16) = 3·(1,2,3,5) + 16, (3,7,10,12,16); the first two are scalings of the two coarse
  blocking patterns. Whether the blocking transfers through the scaling: not established.

**E12. Scaled blocking patterns (2026-10-15).**
- `six_scaled_patterns_v1.out`: L(1,3,4,5) = {1/6} ∪ [13/30, 11/24] ∪ [13/24, 17/30] ∪ {5/6} (measure 1/20,
  components 1/40); L(1,2,3,5) = {1/6} ∪ [7/30, 5/18] ∪ [13/18, 23/30] ∪ {5/6} (measure 4/45, components 2/45).
  S = kP + {e} fails at its largest flank iff no opening t_j has k t_j in L(P); with gcd(k,e) = 1 the points
  k t_j mod 1 are the grid (i + k/6)/e (spacing 1/e, phase k/6). Among failures, the residual ones are exactly
  the four known exceptions (1,3,4,5,6), (1,3,4,5,12), (2,6,8,10,11), (3,6,9,15,16).
- Blocking does not transfer as a residue statement ({2,6,8,10} has residues {2,0,2,4}); what transfers is
  the lonely set (loneliness is invariant under scaling time). The coarse-blocking patterns have the
  smallest lonely sets: no right-neighbourhood of a sixth-point.
- Window bound: once e > 40k (resp. > 22.5k) an opening meets a component of L(kP) whatever the phase
  (`Flanks.exists_lonely_flankOpening_of_gap`). `six_scaled_patterns_v2.out`: exhaustive for k <= 20 up to
  the bound — failures only (1,6), (1,8), (1,9), (1,10), (1,12), (2,11), (3,16), (3,20), (3,22), (3,25),
  (3,29), (6,37) for (1,3,4,5) and (1,6), (1,10), (3,16) for (1,2,3,5). Finite for k <= 20; all k not
  established. Failing k are divisors of 6 (phase k/6): observed, not explained.

**E13. Why the failing scales divide n: phase classes (2026-10-15).** Purpose restated by the owner:
understanding how the cascade can prove n = 6, or how and why the BHK proof can be reformulated.
- `scaled_phase_v1.py`; `scaled_phase_n6_P1345_v1.out`, `scaled_phase_n6_P1235_v1.out`,
  `scaled_phase_n8_P13457_v1.out` (n = 8 used as a comparison only). For gcd(k,e) = 1 the scaled openings
  form the grid (i + r/n)/e, r = k mod n, so failure depends on (r, e). Classes r and n − r fail at the same
  e (L symmetric). Each class fails only at small e; actual sets need e > (max P) k. Failing k = small k
  plus the phase-0 and phase-1/2 classes, which fail longest: n = 6 → {1,2,3,6}; n = 8 → {1,4}. "Divides n"
  is a consequence of the phase classes, not divisibility as such.
- Closes the open part of E12: in a primitive kP + {e}, gcd(k,e) = 1 automatically; class lists are complete
  below the window bound (40 for (1,3,4,5), 23 for (1,2,3,5)); hence for (1,3,4,5) no k >= 8 fails and the
  12 listed (k, e) are ALL failures for every k; likewise the 3 for (1,2,3,5). One infinite family of
  potential largest-flank exceptions is settled exactly (finite check plus `exists_lonely_flankOpening_of_gap`).
- Relation to purpose: this settles one family on the cascade route; the general residual is not settled.

**E14. Correction of framing (2026-10-15).** Owner: *"The cascade never fails. If the cascade fails we have
a counter example to the conjecture. The largest flank is an explanation of the cascade"*
- E13 and earlier replies called the 13 sets and the scaled-family cases "failures of the largest-flank
  route". Corrected reading: the cascade stops at the earliest lonely instant (`lonely_iff_run_ends`,
  `first_isolation_of_fixed`) for every set. "The largest flank has a lonely opening" is an explanation
  of why the cascade stops when it does: it caps the run at the first lonely opening of the largest flank.
  Where that explanation does not apply (the 13 sets, the scaled-family cases), the cap comes from another
  flank (the second-largest in every case found).
- Related memory: `feedback_n8_cascade_is_the_oracle_2026_09_27.md` (the cascade is the oracle; the work is
  its mechanism), which applies at every order.

**E15. §5 against Proposition 11 (2026-10-15).** `six_s5_prop11_v1.{py,out}`; `SUMMARY_n6_cascade_v2.md`.
- Cascade endpoints in Proposition 11's half-lap windows: k = 1, 174 of 1,084 (16.1%) against 11.2% of
  all lonely openings; k = 2, 22 of 594 (3.7%) against 12.1%. Final flank for every k mostly runner 4 or 5,
  runner 2 in 22–31%, runner 3 almost never.
- Shared reduction: v3 = v1 + v2 gives x3 = x1 + x2 (mod 1). BHK pin runner 3 at a half lap; cascade
  endings at runner 2's openings pin x2 = 1/6, so runners 1–3 clear iff x1 ∈ [1/6, 2/3]. k = 2: x3 = x2 + x1/2
  (BHK's fictional runner). Route departs; reduction shared. Case 5.1 (k ≥ 3) not yet compared.

**E16. §5 Case 5.1 and endings at runners 4, 5 (2026-10-15).** `six_s5_case51_v1.{py,out}`; `SUMMARY_n6_cascade_v3.md`.
- k >= 3: 766 of 766 endpoints just after a 2–3 meeting (control 19.6%) — forced by early ending
  (D T = v1 T/k, v1 T < 1/2). The cascade lands in the first meeting window, Case 5.1's premise.
- Endings at runners 4, 5 (1,333): 123-gap >= 2/(3 v4) in 22.9% (control 33.8%); >= 1/(2 v3) in 14.0%
  (control 18.9%). About 77% of these lonely instants are not guaranteed by BHK's length lemmas.
- Reading: §8 reformulated; §5, §7 same regions, different instants. Next object: residue explanation of
  lonely openings at runners 4, 5 inside the first meeting window.

**E17. Lonely openings at runners 4, 5 in §5 (2026-10-15).** `six_s5_window_residues_v1.{py,out}`,
`CascadeMergedPair_v1.lean` (`.out`).
- Of 1,333 §5 endings at runner 4 or 5, 668 lie inside the first meeting window (D T <= 1/6); the k >= 3
  100% of E16 does not extend to k = 1, 2.
- Inside the window the lonely condition at opening N of flank x reduces exactly to three residue
  conditions (m = 6N+1, mod 6x): runner 1 in [x, 5x]; runners 2, 3 merged: x + D m <= v3 m mod 6x <= 5x;
  other fast runner in [x, 5x]. 4,708 in-window openings checked, 0 mismatches. `merged_pair_iff`
  [propext, Classical.choice, Quot.sound].
- Tightest condition at the endpoint: runner 1 in 843, merged pair 343, other fast runner 147. Openings
  N = 1 (602), 2 (372), falling to 11.
- Explains which openings are lonely, exactly; does not explain why one exists. Outside the window
  (665 endings) runners 2, 3 are not merged.

**E18. Runner 1's first clear lap, and the pair outside the window (2026-10-15).** `six_first_lap_v1.{py,out}`,
`six_first_lap_max_v1.out`.
- Every residual set in [1,40] ends inside runner 1's first clear lap (v1 T <= 5/6): 0 exceptions; max
  v1 T = 35/48 at (7,16,24,32,40) (§6, nine moves). Runner 1 binds because the cascade starts at its band edge.
- This is a stronger form of `DoorFirstLap` (tau = v1 T <= 1): REFUTED at n = 8 (2401/1872, 28 moves),
  UNDETERMINED at n = 5, 6, 7 (`docs/nN/SMALL_ORDER_DOORS_v3.md` §5); exhaustive max tau at n = 6 over all
  sets is 25/31 = 0.806 at [1,34] and still climbing; random search cannot find the known n = 8 witness, so
  no null is licensed. The [1,40] result here is a bounded observation, not evidence the statement holds.
- Outside the first meeting window (665 §5 endings at runners 4, 5): delta = frac(D T) mostly < 1/3 (591), then
  [1/3,1/2) 69, [1/2,2/3) 5. Pair (2,3) clear iff x3 in [1/6,5/6] ∩ ([1/6,5/6] + delta) mod 1: one interval
  [1/6+delta, 5/6] for delta <= 1/3, two for 1/3 < delta <= 2/3; 0 mismatches.

**E19. DoorFirstLap at order six: REFUTED (2026-10-15).** `dfl_search_v1.py`, `dfl_control_n8_v1.out`,
`dfl_search_n6_v1.out`, `dfl_verify_v1.py`, `dfl_verify_n6_v1.out`.
- Instrument: directed hill-climbing on tau = d_min·T with the exact cascade, seeded from an exhaustive range.
  tau computation reproduces the recorded n = 8 witness exactly (2401/1872, 28 moves). Positive control at
  n = 8 (unseeded): reaches tau = 55/42 > 1 at (44,107,148,194,245,273,349), 25 moves. (n = 8 used only as
  instrument control.)
- n = 6: tau = 103/72 = 1.43056 at (103, 246, 300, 395, 518), 13 moves. Independent check by enumerating
  every opening up to T: earliest lonely instant T = 1/72 (opening 4 of 300), agrees with the cascade.
  `DoorFirstLap` (tau <= 1) is false at n = 6; record `docs/nN/SMALL_ORDER_DOORS_v3.md` §5 had it UNDETERMINED.
- The witness is not in SixResidual (the rules settle it). The residual-only first-lap observation (E18) is
  open; a residual-restricted directed search is running (`dfl_search_v2.py`).
- Residual-only directed search (`dfl_search_v2.py`, `dfl_search_n6_residual_v2.out`): stalled at its seed
  (19/28), below the known residual maximum 35/48; no positive control for this variant. VOID, not a null.
  Residual-only first-lap question remains open. Summary v4 §5 item 1 and §6 updated.

**E20. The first-lap cap fails for residual sets too: resonant chains (2026-10-15).** Owner: continue towards
a native n = 6 proof; reformulating BHK remains allowed.
- Native proof shape tested: rules settle non-residual sets; residual sets stop inside runner 1's first clear
  lap, giving the cap 5/(6 v1) and existence by `exists_fixed_of_capped`.
- `six_tau_exhaustive_v1.c` (exact integer cascade; reproduces the [1,40] Python results: 17,135 sets,
  max 35/48). `six_tau_exhaustive_v1_150.out`: max tau climbs 0.62 → 0.82 up to 96; from [97,108] 11 residual
  sets exceed 5/6, all with tau > 1 (none in (5/6, 1]); max 903/660 at (21,53,64,84,110), 14 moves.
  `six_tau_over_v2.out` lists the 11; three verified by `dfl_verify_v1.py` (cascade = enumeration of openings,
  residual) in `six_tau_over_verify_v1.out`. The cap at runner 1's first lap is refuted for residual sets.
- The counterexample of E19 fails only `no_free_flank` (300 is a free flank).
- Mechanism (`six_resonant_chain_v1.out`): the four largest form a near-geometric chain, ratios ≈ 1.31; every
  consecutive pair meets the staircase step 5x < 7y and every pair two apart the lap-2 return 11z < 7x < 13z
  (window r in (1.2536, 1.3628)); the walk rotates through returns until runner 1 itself is caught at
  v1 t = 7/6. All 11 satisfy both conditions.
- `six_tau_chain_count_v3.out`: 81,402 residual sets in [1,150] meet the chain conditions; 81,391 stay in the
  first lap, 11 leave; none leaves without them. Necessary (observed), far from sufficient.

**E21. Forcing as grid displacement: first deformation observations (2026-10-15).** Owner: *"Cascade tell us how to
find the isolation but it doesn't tell us how it is forced, we need to find that out"*; approved the grid-
displacement frame (record: commit 73d736b E380; RULES existence frame 1–3) for n = 6, then translation to BHK.
- `six_deform_v1.py`, `six_deform_stats_v1.{py,out}`: start at the grid v1·(1,2,3,4,5) (isolated at 1/(6 v1), a
  single point: runner 5 on the band edge, so the grid isolation is displaced at once); move v5, v4, v3, v2 one at
  a time to S (N = 40 rational steps each); track the earliest lonely instant.
- Closures (old instant blocked): always by the moving runner alone — forced by construction (frozen runners keep
  their status), a method check. Relabelings (a new earlier lonely instant while the old stays lonely) are not
  closures.
- Ordinary sample (286 sets): 1,277 closures; new instant later in 1,273; reappears at the moving runner's own
  next opening in 965 (76%), elsewhere in 312. Resonant chains (11): 43 closures, all later; at the moving runner's
  opening 15, elsewhere 28.
- Two parts of forcing: single-step displacement (others clear at the moving runner's next opening) and
  multi-step displacement (the next opening is blocked; the isolation moves further). Next: the multi-step closures.
- `six_deform_paths_v1.out`: at each closure the cascade restarted from the closed instant reaches the new earliest
  instant (1,275 of 1,279; 82 of 82 chains); first setter always the moving runner (forced); 714 settle in one step;
  commonest longer pattern slower, slower, then the moving runner again (253, the delayed return); then one faster
  runner (232). Reading: tracking the earliest instant reduces displacement to the cascade again — it shows how,
  not why. Next object: the lonely intervals themselves (births, deaths and the runner pairs at each), in a fixed
  window, along the same deformations.

**E22. Lonely intervals along the deformations (2026-10-15).** `six_intervals_v1.py`, `six_intervals_v2.py`;
`six_intervals_v1.out`, `six_intervals_v2_N40.out`, `six_intervals_v2_N400_chains.out`.
- Window [0, 2/v1]; intervals exact (intersection of the five band families), labelled by edge runner and lap.
- The grid start has only isolated points (length 0). After the first step every path keeps at least 2 lonely
  intervals in the window (ordinary 286 paths: min 2 for 113, up to 7; chains: min 2 for all 11). No death left
  the window empty.
- Chains: births 163, deaths 126, unchanged from N = 40 to N = 400 (real events). Ordinary-sample counts at N = 40
  (59,256 / 56,147) are inflated by sampling; not to be read as event counts.
- Reading: a cap-type observation along these paths (two laps of runner 1), the same kind as DoorFirstLap; not a
  forcing mechanism. Next: exact birth mechanism — which runner pairs create new intervals as the moving runner
  sweeps, and whether every death is accompanied by a guaranteed birth.

**E23. Grid displacement, steps 1–3: lap boxes, degenerate configurations, the instant (2026-10-15).** Owner:
*"doesn't having a global isolation via ap or residue mean we already have proved existence and now we just prove
that arrangements deform the location"*; then *"Yes start an 1 and then do the rest"*.
- **Object.** A lap box is a lap vector `k` (runner `i` reads in `[k_i + 1/6, k_i + 5/6]`). It is alive iff every
  ordered pair has `(6k_i+1) d_j <= (6k_j+5) d_i`; its instant is the latest entry `max_i (6k_i+1)/(6d_i)`
  [L `lap_box_lonely`, `GridStart_v1.lean`]. A lonely interval of positive length is a box with every pair strict.
- **Step 1, the grid.** `c·(1,2,3,4,5)` has two degenerate boxes in each period: laps `(0,0,0,0,0)` at `1/(6c)`
  and `(0,1,2,3,4)` at `5/(6c)`. The first is alive iff `d_5 <= 5 d_1` globally (`lonely_six_of_spread`). For the
  second, every pair inequality is strict at the grid except `(5,1)` [L `grid_tight_pairs`], so near the grid it
  is alive iff `d_5 >= 5 d_1`. The two boxes are the two sides of one hyperplane `d_5 = 5 d_1`.
  `six_grid_start_v1.out`: 4,000 perturbations of all five speeds, 0 mismatches with the rule, exactly one of the
  two families opens every time. Residual sets have spread above 5, so their paths leave through the second box.
- **Step 2, along paths.** `six_boxes_v1.out`: paths as in E21 (every 8th residual set in [1,40], 2,142 sets,
  plus the 11 chains), each move exact in the moving speed (box intervals discovered until they cover the move).
  Interior degenerate points: **0** on every path; junctions between moves: 0 of 8,361
  (`six_boxes_control_v1.out`). Positive control fires: the grid point, and the path `d_5: 4c -> 6c` at
  `d_5 = 5c`. So on these paths every box death is overlapped by a box already open; the grid start is the only
  degenerate configuration met.
- **Degenerate configurations, searched directly.** `six_tight_v1.out`: all 5,302,911 primitive 5-sets in [1,60];
  tight (every lonely interval a point) = **(1,2,3,4,5) and (1,3,4,5,9)** only; no counterexample. Neither contains
  a multiple of 6. Matching against the literature on tight instances: not checked (citation-verifier owed if
  used).
- **(A) at both tight sets.** `six_tight_open_v1.out`: two lonely points per period, `t = 1/6` and `t = 5/6`, the
  mirror pair under `t -> 1 - t`; at each, runner `d_1` and the element `5 d_1` are on edges (one entering, one
  leaving), the rest strictly inside. Opening rule at each point: entry precedes exit; 3,000 perturbations per set,
  0 mismatches, never neither. Why: [L `mirror_opening`, `GridMirror_v1.lean`] at integer speeds the opening
  condition at `1 - p` is the reverse of that at `p` (`D_e d_l < D_l d_e` against `D_l d_e < D_e d_l`). So at any
  integer degenerate configuration whose lonely points are simple (one entering, one leaving), no small change of
  speeds destroys the lonely set; it is displaced to the side that opens.
- **Step 3, the instant.** `six_instant_bound_v1.out`: earliest lonely instant over all primitive sets in [1,60].
  Max `d_min·T` = 43/33 at (10,25,32,42,55), then 75/58 at (9,23,29,38,50); `d_min·T > 1` in these 2 sets only.
  By spread `floor(d_max/d_min)`: exactly 1/6 below 5 (the spread box); the maximum at spread 5, just across the
  face `d_max = 5 d_min`; then falling to about 0.36 by spread 30–60. Larger examples elsewhere: 103/72 (E19),
  903/660 (E20).
- **Logical shape, stated in these objects** [reading, not proved]. Let L be the configurations with a lonely
  instant. Positive-length boxes are open conditions; the grid is in L. If (A) every degenerate configuration has
  a neighbourhood in L, and (B) lonely instants stay bounded under limits (a bound `T <= C/d_min` would do), then L
  is open and closed in the connected space of speed vectors, hence everything. Data: (A) is proved at the only
  two integer tight sets to 60, by the mirror; (B): `C >= 103/72` is needed, DoorFirstLap's `C = 1` is false, no
  uniform `C` is proved. Open: degenerate configurations of real rank at least 2 (no mirror); whether integer tight
  sets are all simple.
- **Against BHK** [reading, not checked lemma by lemma]: BHK do not deform; each case places an instant in a named
  window (§8 openings of v4/v5; Proposition 11 half-laps of runner 3; Case 5.1 first meeting windows), which is
  existence and a (B)-type location together. Nothing in BHK plays the role of (A).

**E24. Degenerate configurations: integer tight sets to 200; real rank at least 2 (2026-10-15).** Owner: *"Look for
degenerate configurations of real rank at least 2 (no mirror available), and whether integer tight sets are always
simple."*
- **Integer tight sets.** `six_tight_v2.c`, `six_tight_v2.out` (H = 120), `six_tight_v2_200.out`: all
  2,450,913,356 primitive 5-sets in [1,200]. Tight: **(1,2,3,4,5) and (1,3,4,5,9) only**; no counterexample; both
  **simple** (each lonely point in a period, t = 1/6 and 5/6, has exactly one element at an entry and one at an
  exit, read off the residues b and 5b directly). Nonsimple: 0. So `mirror_opening` (E23) applies to every integer
  degenerate configuration with entries <= 200 [X].
- **Real rank r >= 2, the object.** The orbit closure of d is the subtorus T = V + Z^5 (V the rational span of d,
  dim r); the orbit is dense in T, so d has a positive-length lonely interval iff T meets the open cube
  C° = (1/6,5/6)^5 mod 1. Degenerate needs T to miss C°. Every all-nonzero vector w of the lattice V ∩ Z^5 has its
  orbit in T, so then every such w is not strictly lonely: tight, or a counterexample. With entries <= 200 that
  forces w to be a signed permutation of (1,2,3,4,5) or (1,3,4,5,9) [X, scope: lattices containing such a w]. Any
  rank >= 3 torus contains the 2-torus span(u, v) for u tight and each v in the lattice, so rank 2 decides.
- **Projection step** [argued; checked]. At the simple lonely point x of u (coordinate e = value 1 entering,
  l = value 5 leaving, others strictly inside), if (v_e, v_l) is not parallel to (u_e, u_l) = (1, 5), some
  y = αu + βv has y_e > 0 > y_l, and x + εy is in T ∩ C° for small ε. `six_rank2_v1.out` part 1: all 16,464 v in
  [-3,3]^5 with v_l ≠ 5 v_e have an exact rational witness, for both u. So a degenerate 2-torus through u lies in
  the hyperplane d_l = 5 d_e: the same face as E23 step 1, the one direction along which neither mirror point
  opens.
- **On the face.** Then T = {s u + t y} with y supported on the other three coordinates. Part 2: all 865
  primitive y with |y| <= 6 (up to sign) have a witness, for both u; **none without**. Controls
  (`six_rank2_control_v1.out`): v = u, 2u, 0 give no witness (the tight circle alone misses C°); non-tight
  (1,2,3,4,6) gives one.
- **Reading.** Up to these ranges there is no degenerate configuration of real rank >= 2: every 2-torus through a
  tight vector meets the open cube, so nearby lonely instants have positive length and (A) is not needed there.
  Support size 1 holds for every y: s can be chosen with the four fixed coordinates strictly inside (four runners,
  order five, threshold 1/5 > 1/6), then t is free. Open: support size 2 or 3 for all y (a shifted problem: fixed
  offsets alone can fail, e.g. speeds (1,1,1), offsets 0, 1/3, 2/3; the freedom in s is what the box search uses);
  lattices whose all-nonzero vectors all have entries above 200.

**E25. The face case, for every direction: residues modulo 11 (2026-10-15).** Owner: *"Try to prove the face case
for all y with support size 2 or 3: some (s,t) puts s*u + t*y in the open cube, using the freedom in s."*
- **Reduction.** Take s = i/Q, t = j/Q. Coordinate k reads (i u_k + j y_k)/Q mod 1, which depends only on
  y mod Q, so one modulus that works for every residue class settles every y. `six_face_mod_v1.{c,out}`: the
  first Q with no failing class (classes with gcd(r, Q) = 1, as forced by y primitive) is **Q = 11, for both
  tight vectors**; Q = 2..10 each leave classes. `six_torus_mod11_v1.{c,out}`: the same modulus works for a
  general second direction v in (Z/11)^5. The only classes without a witness are the 11 classes v ≡ λu, the
  tight circle itself. Strictly inside: residues {2,...,9}, since 2/11 > 1/6 and 9/11 < 5/6.
- **Lean** [L, `TorusModEleven_v3.lean`]: `check_grid` and `check_other` are kernel computations over
  (Z/11)^4. They use v_0 = 0, which is allowed because replacing v by v - v_0 u leaves the torus unchanged. Both
  print "does not depend on any axioms". `lift`, `torus_witness_grid` and `torus_witness_other` (axioms propext,
  Classical.choice, Quot.sound): for every integer v with no l making v ≡ l·u (mod 11), there are integers I, J
  with every coordinate of I·u + J·v in {2,...,9} mod 11. `witness_lonely`: such a coordinate z reads at
  distance > 1/6 from the integers at the instant 1/11. `TorusModEleven_v1.lean` (a check over all of
  (Z/11)^5) did not finish in 10 minutes and was stopped; v2 replaced it, and v1 gives no result.
- **From the lattice to the torus** [argued]. Let u be tight in the lattice L = V ∩ Z^5 of a configuration d of
  rank at least 2. Up to permuting coordinates and changing signs, which preserves the open cube, u is
  (1,2,3,4,5) or (1,3,4,5,9). Take v in L independent of u, let M be the saturation of span(u, v) in Z^5, and
  write M = Zu ⊕ Zw (u is primitive). If w ≡ λu mod 11, then (w - λu)/11 lies in M with w-coefficient 1/11,
  which is impossible. So `torus_witness_*` gives z = I·u + J·w in L, strictly inside at the instant 1/11. Then
  T meets the open cube, and the orbit of d (dense in T) enters it: d has a positive-length lonely interval and is
  not degenerate. This covers every v and every support size; the projection step of E24 is no longer needed.
  The density of the orbit in T (Kronecker) is standard and not formalised here.
- **Conclusion, with scope.** A degenerate configuration of real rank at least 2 has no tight vector of either
  class in its lattice. Its all-nonzero lattice vectors would all be tight sets with some entry above 200 (E24
  search), or counterexamples. Combined with E23–E24: every degenerate configuration found or excluded so far is
  an integer simple tight set, where `mirror_opening` gives (A). Remaining for (A): tight sets beyond 200, and
  (B).

**E26. (B): the instant across the spread-5 face; what (B) carries (2026-10-15).** Owner: *"Work on (B): lonely
instants bounded under limits, starting from the spread-5 face where d_min*T peaks."*
- **What (B) carries** [argued]. Configurations with no rational relation among the speeds are lonely: the orbit is
  dense in the whole torus (Kronecker), and the open cube is nonempty. So the lonely set L is dense, and L closed is
  equivalent to L being everything. In the open-and-closed argument of E23, (B) is the whole content and (A) adds
  nothing. In box terms: if near every configuration the lonely configurations have a lonely box with bounded laps,
  then finitely many closed boxes contain them, and the limit is lonely. A uniform form that would do it: **every
  configuration has a lonely box with the slowest runner's lap k_1 <= 1** (tau = d_min·T <= 11/6). Locally, near a
  hypothetical non-lonely integer d0 every box fails by an integer margin >= 1, and a perturbation of size δ moves
  that margin by about 6·T·|d0|·δ. So lonely instants near such a d0 sit at T of order 1/δ: (B) cannot come from
  local data. It is global.
- **Integer data** (`six_instant_bound_v2.{c,out}`, all 184,425,816 primitive sets in [1,120]): k_1 = 0 in all but
  68; k_1 = 1 in those 68; k_1 >= 2 never. All 68 have spread floor(d_max/d_min) in {5, 6}. Max tau = 575/408 at
  (23,54..56,68,89,117). `six_late_sets_v1.out`: earliest box (1,3,4,5,7) in 53 sets and (1,2,3,4,6) in 15; the box
  (1,3,4,5,7) is alive with positive slack in all 68. The second element is free over a range (54, 55, 56 give the
  same tau).
- **Real configurations** (`six_tau_climb_v1.out`, adversarial climb on ratio vectors, exact cascade): best
  tau = 1.43889 at ratios (1, 2.396, 2.896, 3.810, 5.001); the slowest runner's lap is never above 1. Of 670 late
  configurations evaluated, 18 lie outside box (1,3,4,5,7), all in box (1,3,4,5,6) (tau ≈ 1.231): the late region
  needs at least two boxes off the integers.
- **At the face** (`six_face_sup_v1.out`): with d_5/d_1 = 5 + ε fixed, the supremum found is 1.43652, 1.43911,
  1.43937 for ε = 10^-2, 10^-3, 10^-4, always box (1,3,4,5,7). The instant is runner 3's entry, 25/(6 r_3), with
  r_3 → 2.8947..., matching 55/19, so tau → 95/66 ≈ 1.43939 [candidate, not proved]. E19's 103/72 = 1.4306 and
  E20's 1.368 lie below it. Mechanism: at d_5 = 5 d_1 the spread box (all laps 0, instant 1/6) is alive; just
  across, it is dead, and the earliest instant jumps to up to about 95/66. The peak of d_min·T is that jump, the
  largest displacement seen anywhere.
- **Where this leaves the frame.** Grid + displacement reduces to one bound: lonely within the slowest runner's
  second lap. Over a bounded spread range, that is a statement about finitely many boxes, polyhedral cones in ratio
  space; large spread would go to lower orders through the fast runner. Checking it over a spread range is a finite
  exact computation, but it has the shape of the covering route set aside in E2: the boxes would be shown to fill a
  region of ratio space. Owner's decision before pursuing.

**E27. Return to E22: E23–E26 were driven by an imported proof shape (2026-10-15).** Owner: *"I wonder, did you at
some point think "what should a proof look like" and then start to go after that instead of actually reason?"*;
then *"So we need to go back to where you started trying to fit my framework into someone elses box instead of do
the actual thinking"*.
- **Where it began.** After E22, in discussion. (i) Births and deaths of lonely intervals were dismissed as
  "covering in disguise": a type objection to the object E22 had just named. (ii) The owner's frame (*"having a
  global isolation via ap or residue mean we already have proved existence and now we just prove that arrangements
  deform the location"*) was converted into a standard analysis template: the lonely set open and closed in a
  connected space, with ingredients (A) persistence at degenerate configurations and (B) no escape to infinity.
  E23–E26 worked those ingredients.
- **The template was vacuous, and a one-line check would have shown it** (found only in E26): configurations with
  no rational relation are lonely (Kronecker), so the lonely set is dense. (A) carries nothing, and (B) is
  existence restated. E26's uniform bound (tau <= 11/6) is a cap, the shape of the refuted DoorFirstLap, and the
  proposed finite check over ratio space is the covering route set aside in E2.
- **Kept as facts, with their template role withdrawn:** `lap_box_lonely`, `grid_tight_pairs` (the grid on the
  face d_5 = 5 d_1); tight sets to 200 are (1,2,3,4,5) and (1,3,4,5,9), both simple; `mirror_opening`;
  `torus_witness_grid/other` (mod 11); the jump of the earliest instant across the spread-5 face (E26), and the
  late-set lap vectors (1,3,4,5,7), (1,2,3,4,6), (1,3,4,5,6). Withdrawn: the E23 "logical shape" bullet, the E24–E25
  readings framed as (A), and E26's "what (B) carries" as a route.
- **The object passed over.** E23 step 2 (`six_boxes_v1.out`): along every path, each box death is overlapped by a
  box already open (0 interior points where none is open, 2,153 paths). Filed there as "no degenerate
  configuration met". In the owner's frame it is the displacement itself: when the box holding the isolation
  closes, another is open. **Restart point: what forces that box to be open, in framework objects (which runner
  closes the old box, which flank and opening the new box sits at, the residues there), observed at each death.**

**E28. Handovers at each death of the isolation box (2026-10-15).** Owner: *"Yes: observe each box death along the
deformations, recording the closing runner, the box that takes over (flank, opening, laps) and the residues there.
Observation only."*
- **Instrument.** `six_handover_v1.py` (paths as E21/E23; every 8th residual set in [1,40], 2,142 sets, plus the 11
  chains). For each death of the box A holding the isolation (A earliest alive at the death point x of the moving
  speed): A's closing pair, flank, laps; the takeover B = the earliest box alive just past x, with flank, laps and
  readings. Output `six_handover_v1.tsv` (7,326 deaths); summary `six_handover_read_v1.{py,out}`. **Control:** the
  cascade's earliest instant just past x equals B's instant in 7,326 of 7,326. No death without a takeover.
- **Closing.** The moving runner leaves its band at the instant A's flank enters (closing pairs 7,718 "mover
  leaves", partner = A's flank in 8,404 of 8,407; 686 further tight pairs not involving the mover coincide at the
  same x). Forced: a box dies when its earliest exit meets its latest entry, and only the mover changes.
- **The takeover is already open.** B was open before the death in 7,233 of 7,294 ordinary deaths and 32 of 32 chain
  deaths. So the isolation passes to a box that already exists, later in time; it does not need a birth.
- **Where B sits.** Two kinds:
  - At the mover's next entry (B's flank = the mover): 4,747 of 7,294. The instant moves exactly 1/3 of a mover lap
    (from its exit to its next entry): 3,060 of these change only the mover's lap (+1); 1,687 also advance faster
    runners' laps, which is the same instant read in later laps.
  - Later than the mover's next entry: 2,547. At that next entry someone is in the way: one faster runner in 2,075,
    two in 386, three in 23, a slower runner in 64. B's flank is that blocking runner in 2,049 of 2,548. Chains: the
    later kind dominates (B's flank faster in 22 of 32; displacement up to 1.33 mover laps).
- **The 61 takeovers born at the death point** (`six_handover_born_check_v1.{py,out}`): every one has one exact
  structure. The mover is on lap 0, and a faster runner p has d_p = 5·x. A closes when the mover's lap-0 exit meets
  p's lap-4 entry. B opens at the same point, when the mover's lap-1 entry meets p's lap-5 exit, and B's instant is
  the mover's next entry (1/3 mover lap later). This is the pair version of the grid face d_5 = 5 d_1 (E23 step 1),
  with the mover in the role of runner 1.
- **Readings** [observation; nothing proposed]. At each death the isolation goes to the mover's next entry unless a
  runner, almost always a faster one, is in the way there; it then sits at that runner's entry in 80% of those cases.
  The takeover box already exists except at the exact 1:5 ratio between the mover and a faster runner. Not yet
  observed: why the box at the mover's next entry, or at the blocker's entry, is open at the moment of death. That
  is the residues of the other runners at those instants, in each kind.

**E29. Readings of every runner at the takeover instant (2026-10-15).** Owner: *"Yes: observe the readings of every
runner at the takeover instant, for both kinds (mover's next entry, blocker's entry), at each death. Observation
only."* `six_takeover_readings_v1.{py,out}`, `six_takeover_flankrank_v1.{py,out}`, on `six_handover_v1.tsv`.
Roles: M mover; F the old box's flank (enters at the death, while M leaves); s, f slower, faster than M. All [C].
- **Kind 1, the isolation goes to M's next entry** (4,747 ordinary). F is runner 1 in 3,242 (the slowest; d_F/x in
  0.0–0.2), runner 5 in 1,017, runner 4 in 410, runner 3 in 78. When F is slow, it advances only d_F/(3x) of a lap
  (0.01–0.07) in the third of a mover lap from M's exit to M's next entry, so at the new instant F reads just past
  its own entry (0.18–0.23). F is the runner with least slack in 3,174 deaths, near the entry edge in 3,298.
  The new box's earliest exit (the runner that will close it next) is a slower runner in 3,420, faster in 904,
  F in 423. Second cluster: F faster than M (d_F/x ≈ 1.4, 1.7, 3.8, 7.4), F reads about 0.43–0.63 at the new instant.
- **Kind 2, someone in the way at M's next entry** (2,547 ordinary). The new instant is:
  - a faster runner's entry: 1,759;
  - F's own next entry, exactly a whole number of F-laps after the death: 1 lap 599, 2 laps 48, 3 laps 63, 4 laps 3;
    F faster than M in all of these;
  - a slower runner's entry: 75.

  At the new instant M has re-entered its band and sits just past the entry edge (readings 0.19–0.29). M is the
  least-slack runner in 1,051, near the entry edge in 1,390. Earliest exit of the new box: slower 1,517, faster
  638, F 315, M 77.
- **Chains** (32): kind 2 in 25. The commonest new instant is F's entry exactly 2 F-laps later (11), then a faster
  runner's entry (10).
- **Reading** [observation only]. The runner nearest an edge in the new box is the one that was at an edge at the
  death, now a little inside: F (just entered) in kind 1, M (just re-entered) in kind 2. When F is faster than M
  and something blocks M's next entry, the isolation often returns to F's own entry, a whole number of F-laps later.

**E30. The lineage of one isolation: redundancy and thin moments (2026-10-15).** Owner: *"So the cascade does not
guarantee the first or the only isolation, just an isolation. Are we trying to prove too much. If you look at
global isolation, there are 4 different isolation events, do we need to track which isolation event the cascade
points to for which deformations?"*; then approved the redundancy and thin-moment observations under that view.
- **Correction of record.** The cascade does return the first lonely instant (`first_isolation_of_fixed`; E28
  control). The owner's point stands: existence needs an isolation, not the first. Following the earliest
  instant (E21, E28) rebuilt the cascade's steps.
- **The four grid events** are two per period, mirror images under t -> 1/c - t, and E23 step 1 fixes which family
  survives a deformation by the sign of d_5 - 5 d_1. Residual sets (d_5 > 5 d_1) keep the 5/6 event: box
  (0,1,2,3,4).
- **Instrument.** `six_lineage_v1.py`: follow the 5/6 event's box L along the E21 paths. At each death of L, the
  takeover is the box alive just past the death whose instant is NEAREST to L's (not the earliest). Output
  `six_lineage_v1.tsv`; reader `six_lineage_read_v1.{py,out}`. **Control** (`six_lineage_ctl_r11.tsv`): at
  (x,2,3,4,11) with x moving through 1, box (0,1,2,3,9) dies exactly at x = 1 and its mirror (1,2,3,4,12) is born
  exactly at x = 1 (intervals [11/59, 1] and [1, 121/73]). This is the r = 11 double coincidence predicted from
  7b - 5b' = 3. The lineage's nearest takeover there is (0,1,2,3,8), already open: runner 5 one lap back.
- **Redundancy.** 24,310 deaths of the followed box on 2,116 paths (up to 72 on one path); chains 14. The takeover
  was already open in 23,450 (chains 14 of 14). The takeover is the dying box with one runner one lap on or back in
  8,800 (runner 5 -1: 3,458; runner 5 +1: 3,308; runner 4 +1: 1,058). Next commonest: three runners one lap
  back, (2,4,5) 3,468 and (3,4,5) 2,509. Jumps are small and go both ways (earlier 13,170, later 11,140): |jump|
  <= 0.6/d_min, at most 0.2/d_min in 24,070. Boxes alive just past a death in the window: at least 4, 10+ in
  22,840 (window-dependent; not a number to read).
- **Thin moments: none.** 860 takeovers were born at the death point (`six_lineage_born_v1.{py,out}`). In all 860
  another box was open on both sides of the death (0 thin). Every one sits at an exact speed ratio 5 between the
  mover and a partner (`six_lineage_born_ratio_v1.{py,out}`):
  - 810: partner = mover/5, the mover being the faster runner; the reversed-role form of the 1:5 mirror
    coincidence (mover lap 5 exit meets partner lap 1 entry; mover lap 4 entry meets partner lap 0 exit);
  - 31: partner = 5 times the mover;
  - 19: further pairs coincide too, including 1:5:25 triples (16).

  The reader's double-coincidence test checked only the mover-slower orientation and reported 41; the ratio
  script settles all 860. r = 11 and the other r ≡ 5 (mod 6) were not met on these paths; they exist (control).
- **Reading** [observation]. Followed as one isolation, the location moves in small steps among boxes standing at
  the same time: mostly the same box with one runner a lap on or back. Wherever two boxes meet at a single point
  (a birth at a death), it is a 1:5 coincidence between the mover and another runner. Other boxes are open across
  it every time, so on these paths no handover depends on that coincidence. Not yet observed: why boxes differing
  by one lap of a single runner stand together. That is the redundancy itself, in residue terms.

**E31. Why boxes one lap of a single runner apart stand together (2026-10-15).** Owner: *"Observe why boxes differing
by one lap of a single runner stand together: the readings and residues that keep both open at the same time.
Observation only."* `six_neighbours_v1.{py,out}`, `six_neighbours_v2.{py,out}`, `six_neighbours_static_v1.{py,out}`.
- **Forced first.** L and B = L ± e_r share the laps of the four runners other than r, so both lie in J, the common
  interval of those four. Both open means J contains a piece of r's band at lap k and at lap k ± 1, so J straddles
  r's blocked window between them (1/3 of an r-lap) and |J| > 1/(3 d_r). At the death the dying piece has length 0
  (`six_neighbours_v1.out`: "touching" in 8,800 of 8,800). Both are consequences of the definitions, not
  observations.
- **Just before the death** (mover 10^-6·x back; `six_neighbours_v2.out`): of 8,800 neighbour takeovers, L and B are
  both open in 8,345. The other 455 are mostly takeovers born at the death (E30). r's clear bands meet J exactly
  twice in 7,568, three times in 454, four or five in 330, once in 448. r is the fastest runner in 6,766 (rank 5;
  rank 4 in 1,649, rank 3 in 370, rank 2 in 15). J is bounded (latest entry, earliest exit) by slower runners or the
  mover in most cases: (slower, slower) 3,171, (slower, mover) 2,446, (faster, mover) 1,455, (faster, faster) 933.
  d_r over the faster of J's two bounding runners: 5 or more in 2,919; spread from 0.5 up.
- **At the residual sets themselves** (every 4th in [1,40], 4,284 sets, no deformation; open boxes in [0, 2/d_1]):
  9,364 one-lap neighbour pairs (r = 5: 5,955; 4: 2,949; 3: 440; 2: 20). 17,324 of 50,195 open boxes have such a
  neighbour. |J| for the pairs: 0.4–1.0 r-laps in 8,434, up to 2.6.
- **Reading** [observation]. The neighbours are the pieces of one stretch J, set by the slower runners (or the
  mover), that a faster runner, usually the fastest, cuts with its blocked window. Each clear band of r inside J
  is one box, and most often J holds two: r's band before and after one passage. When the mover shrinks one piece
  to nothing, the other piece is the takeover. So the redundancy E30 found is mostly the slower runners holding a
  common stretch longer than a third of the fast runner's lap. Not yet observed: why the slower runners' common
  stretch is that long at the places the lineage visits, in residue terms.

**E32. The neighbour cut, formalised (2026-10-15).** Owner: *"Can we formalise that?"* (of E31's summary).
`NeighbourCut_v1.lean` (`.out`; all [propext, Classical.choice, Quot.sound]). Objects: runner r at speed d > 0,
entry e_k = (6k+1)/(6d), exit x_k = (6k+5)/(6d); J = [J₀, J₁] the stretch on which the other runners are clear; the
piece of box "r on lap k" is [max J₀ e_k, min J₁ x_k].
- `neighbours_open_iff`: the lap-k and lap-(k+1) pieces both have positive length iff J₀ < x_k and e_{k+1} < J₁, so
  J straddles r's blocked window [x_k, e_{k+1}].
- `stretch_long`: then J₁ - J₀ > 1/(3d).
- `takeover_open`: if J₀ <= x_k (the lap-k piece may have shrunk to a point) and e_{k+1} < J₁, the lap-(k+1) piece has
  positive length.
- `band_clear`, `piece_lonely`: every instant of a piece is lonely for r and for the others, given the others are
  clear throughout J.
- **Scope.** This formalises the forced part of E31. The observed part is not a theorem: r is usually the
  fastest, J is usually set by slower runners, and J usually holds exactly two of r's bands. It stays [C]. What
  the lemmas do not supply is a reason why J reaches past e_{k+1} when the lap-k piece dies; that is E31's open
  question.

**E33. Why J reaches past r's next entry when a piece dies (2026-10-15).** Owner: *"Observe why the slower runners'
common stretch reaches past the fast runner's next entry when a piece dies, in residue terms. Observation only."*
`six_stretch_end_v1.{py,out}`, `six_stretch_end_v2.{py,out}`, on the 8,800 neighbour takeovers of
`six_lineage_v1.tsv`, speeds exactly at the death.
- **The condition in residue terms.** J = [J₀, J₁], with J₀ the latest entry (runner p, opening k_p) and J₁ the
  earliest exit (runner q). At p's opening, q reads ρ_q = (d_q(6k_p+1) mod 6d_p)/(6d_p), the framework residue
  at p's flank opening, so J's length is (5/6 - ρ_q)/d_q. Two orientations:
  - (+1) The dying piece ends where r's exit meets J's start (4,704 deaths). `takeover_open` then needs
    5/6 - ρ_q > d_q/(3 d_r): q's remaining clear time beats r's blocked window.
  - (-1) r's entry slides past J's end, and the takeover is r's previous lap (4,096 deaths). The condition is
    σ_p - 1/6 > d_p/(3 d_r), with σ_p p's reading at q's exit.
- **Outcome.** Strict in 4,691 (+1) and 3,700 (-1). Equality in 13 and 396: there the takeover's piece is a single
  point at the death and opens just past it. "Open" in E30 meant alive as a closed box, not positive length.
  Fails: 0.
- **Which side carries it.** (+1): q has at least 1/3 of a lap left in 1,337, enough even if d_r = d_q; in 3,367 it
  needs r faster than q. The binding runner (q, or p for -1) is slower than r in 3,407 (+1) and 3,576 (-1).
  Commonest exact values:
  - (+1): ρ_q = 7/9 with d_q/d_r = 14/87, 2/15, 14/123, ... (q 1/18 of a lap from its exit, r more than six times
    faster than q).
  - (-1): σ_p ≈ 0.18–0.20 with d_p/d_r = 1/40, 1/35, 1/36 (p just past its entry, r 35–40 times faster).
- **The path design shows through.** On these paths the runners below the mover are still at their grid values
  v₁·i while v_m moves. ρ_q = 7/9 is runner 2 read at runner 3's lap-1 entry, at grid speeds (2·7/18). So E31's
  "J set by the slower runners", and the commonest residues here, partly reflect that the slower runners are still
  on the grid, whose common stretches are long. The condition and its two-sided form do not depend on the design;
  the frequencies and the dominant residues do.
- **Reading** [observation]. At each death the takeover is open because the binding runner of J still has more of
  its clear band left than r's blocked window lasts. Mostly that is because r is much faster than the binding
  runner, not because the binding runner is far from its edge. To separate the mechanism from the path order:
  the same readout on paths that move all speeds together from the grid to S (not run).

**E34. Straight-line paths: what survives the change of path order (2026-10-15).** Owner: *"Yes: rerun the lineage
and the E31-E33 readouts on straight-line paths that move all speeds together from the grid to S, to separate the
mechanism from the path order."* `six_lineage_line_v1.{py}` → `six_lineage_line_v1.tsv`; readouts
`six_line_read_v1.{py,out}`. Paths d(l) = (1-l)·v₁(1..5) + l·S; every pair inequality is linear in l, so box
intervals in l are exact. Same sample (every 8th residual set in [1,40], plus the 11 chains); lineage of the 5/6
event, nearest takeover.
- **Controls** (`six_lineage_line_ctl.tsv`): 11,924 boxes found lonely at random l all lie in their computed
  intervals (0 misses). The line d₅: 4c -> 6c (others at the grid), following the 1/6 box, reports THIN at
  d₅ = 5c, with the mirror box (0,1,2,3,4) born there (jump 2/3 of 1/d_min).
- **Lineage, compared with the axis paths of E30**:

  | | axis paths (E30) | straight lines |
  |---|---|---|
  | deaths | 24,310 on 2,116 paths | 6,071 on 2,014 paths (chains 19) |
  | thin | 0 | 0 |
  | born at the death | 860 | 22 |
  | one runner ±1 | 36% | 41% |
  | \|jump\| | <= 0.6/d_min | <= 0.8/d_min (0.3 or more in 535) |
  | later / earlier | 11,140 / 13,170 | 4,013 / 2,058 |

  Born takeovers on lines: speed ratio 5 in the closing pair in 15 of 22 (13 with opening ratio 1/5). One is the
  r = 11 double coincidence (closing 11, opening 1/11), first met on a path; six others have ratios such as 23/19,
  41/7, 17/13. So on straight lines a birth at the death is not always the 1:5 or 1:11 mirror pair.
- **Neighbour structure (E31) survives.** 2,466 single-runner takeovers. Just before the death r's bands meet J
  exactly twice in 2,439 (three times in 27). r is the fastest in 1,649 (rank 4: 696; rank 3: 121). J's two ends are
  both set by runners slower than r in 1,733, mixed in 545, both faster in 188.
- **Takeover condition (E33) survives, but what carries it changes.** Strict in all 2,466 (no equalities). Carried
  by the binding runner having at least 1/3 of a lap left in 1,540 (62%), against 1,337 of 4,704 (28%) on axis
  paths. It needs r faster than the binding runner in 926 (38%), against 72%. No dominant residue: the 7/9 cluster
  is gone, the top exact values have 20–70 occurrences each.
- **Reading** [observation]. Path-independent: no thin moments; the takeover is already standing; neighbours are
  the two pieces of one stretch cut by a faster runner, usually the fastest; the stretch's binding runner outlasts
  the cutter's blocked window. Path-dependent: how often r's speed carries it (axis paths kept the slower runners
  on the grid and inflated this), the 7/9 residue, and the dominance of births at ratio 5. On straight lines the
  binding runner mostly just has a third of a lap or more left when the piece dies.

**E35. Summary v5; §5 endings in the cut-stretch language (2026-10-15).** Owner: *"Ok"* (to: write summary v5
through the compile-diff gate, then return to §5 starting from the cascade's ending instants in the cut-stretch
language).
- **Summary v5** (`SUMMARY_n6_cascade_v5.md`, supersedes v4, which is kept unchanged). Compile-diff gate: first pass
  NOT CLEAN (L1–L10: two widenings, the spread {5,6} and the tight-vector class restriction; dropped caveats E21,
  E22, E23 literature, E28, E29, E33 equalities and "alive" definition, E34 path dependence, sample scope). Second
  pass NOT CLEAN (N1 sample sizes of E21/E22, N2 kind-2 count, N3 an unsupported "largely kinematics"). Third pass
  CLEAN. The draft was edited in place while under the gate, before promotion; the gate flags that the versioning
  memory reads "ANY edit = new version" with no draft exception. Owner's call.
- **§5 readout** (`six_s5_cutstretch_v1.{py,out}`, all 2,444 §5 endings in [1,40]). In §5 runners 1–3 merge
  (v1 + v2 = v3), so the stretch is J123, where runners 1, 2, 3 are all clear around the ending instant T, and the
  cutters are runners 4 and 5. Exact arithmetic (a first run computed band ends in floating point and misplaced
  1,023 endings; fixed).
  - J123's left end is set by runner 1 (1,301) or runner 2 (1,126); its right end by runner 3 in 2,427 of 2,444.
  - |J123|: 0.2–0.8 of a runner-4 lap in 2,016; 0.3–1.0 of a runner-5 lap in 2,082. Bands meeting J123: runner 4
    one in 1,805, two in 516; runner 5 one in 1,565, two in 740.
  - Lonely pieces in J123 (4 and 5 both clear, positive length): one in 1,695, two in 529, three or more in 75,
    none in 145.
  - **The cascade ends at the left end of the first lonely piece of J123 in 2,279 of 2,444**; the other 165 end at
    a single-point box.
  - The ending piece starts at an entry of runner 2 (619), 4 (736), 5 (565) or 1 (314), and ends at an exit of
    runner 5 (685), 3 (668), 4 (638).
- **Reading** [observation]. In §5 the ending is mostly the only lonely piece of the 1–3 stretch: there is no
  redundancy to lean on, unlike the paths of E30–E34. The piece is where one band of runner 4 and one band of
  runner 5 overlap inside J123. So the native question in §5 is a two-runner window question: why runners 4 and 5
  have a common clear point inside J123, when J123 is often shorter than the length BHK's Lemma 4 guarantees
  (E16: about 77% of endings at runners 4, 5). That is the shape of BHK's two-flank window (Corollary 5), used
  in their §7, here with a shorter window and the phases of 4 and 5 at J123's start deciding.

**E36. Runners 4 and 5 inside J123 (§5): when they share a clear point (2026-10-15).** Owner: *"Observe exactly when
runners 4 and 5 have a common clear point inside J123: their readings at J123's start and J123's length, against the
§5 endings. Observation only."* `six_s5_window45_v1.{py,out,tsv}`, `six_s5_window45_read_v1.{py,out}`. All 2,444
§5 sets in [1,40]; every J123 window (runners 1–3 all clear, positive length) up to the ending, exact arithmetic.
- **Control.** The first window in which 4 and 5 share a clear point of positive length contains the cascade's
  ending in 2,299 of 2,444. The other 145 have no such window up to T, and all 145 end at a single-point box.
- **The ending is early among windows:** first J123 window in 1,851, second in 429, third in 16, fourth in 3. Only 566
  windows fail before an ending.
- **Failing windows, by kind:** runner 4 never clear in the window 277, runner 5 never clear 72, both clear but never
  together 217. Starting readings: in "both clear, never together", 165 start with 4 clear and 5 blocked. Some
  "never clear" windows start with the runner reading in band: it reads exactly at an edge, so a point, not a
  piece.
- **Length.** The longest failing window is 0.494 of a runner-4 lap (at (4,19,23,27,30)). The largest failing length
  falls as d5/d4 grows: below 1.5: 0.494; 1.5–2: 0.449; 2–3: 0.407; 3 or more: 0.25 (in runner-4 laps). Every window
  of 0.5 runner-4 laps or more in this sample has a shared point; BHK's Lemma 4 length (2/3 of a runner-4 lap) lies
  above all failures. Ending windows: 963 are shorter than 0.5 runner-4 laps, down to 0.027 (at (6,14,20,23,31)).
  Failing windows: 509 of the 566 are shorter than 0.4.
- **Kind of shared point at the ending:** 4 and 5 both clear at the window's start (the piece starts at J123's start,
  an entry of runner 1 or 2) 995; the piece starts later, at an entry of 4 or 5, 1,304.
- **Reading** [observation]. Two regimes. Long windows (about half a runner-4 lap or more, less when 5 is much faster
  than 4) never fail here; that is the regime BHK's length lemma covers, with room to spare. Short windows succeed
  or fail by the readings of 4 and 5 at the window's start, and about 960 §5 endings are in short windows, where no
  length alone decides. Not yet observed: the exact phase condition in short windows, in residue terms (a4, a5 at
  J123's start, against l4, l5), and why the cascade's first or second J123 window is a success.

**E37. Short J123 windows in §5: the race (2026-10-15).** Owner: *"Observe the exact phase condition for short J123
windows: runner 4 and 5 readings at the window start against the window length, in residue terms, for successes and
failures. Observation only."* `six_s5_race_v1.{py,out}` on `six_s5_window45_v1.tsv`, windows shorter than half a
runner-4 lap (1,682: 1,116 successes, 566 failures).
- **The condition.** In runner-4 laps from the window start, runner 4 reads a4 + u and runner 5 reads a5 + ρu
  (ρ = d5/d4) for u in [0, l4]. A shared clear point is an overlap of a clear piece of 4 with a clear piece of 5
  before the window ends, so success is decided by the order of four kinds of event: 4's entry and exit, 5's entry
  and exit, and the window's end (runner 3's exit). Each comparison is a pair inequality of the lap-box criterion,
  e.g. 5 enters before 4 leaves: (6k5+1)/d5 < (6k4+5)/d4. The readings are residues at the window's start,
  a = (d(6k+1) mod 6d_j)/(6d_j) with j = 1 or 2 the runner whose entry opens J123. The case logic reproduces the
  window file's shared flag in 1,682 of 1,682 (a first version listed only one clear piece of runner 4, which
  can leave and re-enter in a short window: 39 mismatches, fixed).
- **By start readings** (B = in band, X = not; runner 4 first):
  - BB: 341, all successes.
  - BX: 330 successes, 232 failures.
  - XB: 150 successes, 133 failures.
  - XX: 295 successes, 201 failures.
- **Failures, the event that decides:**
  - runner 4 still blocked when the window ends (runner 3 leaves first): 277 (XX 191, XB 86);
  - runner 5 enters only after runner 4 has left: 169 (BX);
  - runner 5 enters only after the window ends: 72;
  - runner 5 clear only while runner 4 is blocked: 48.
- **Successes, the binding race:** BX, 5's entry beats 4's exit 298, beats the window's end 32; XB, 5 still clear
  when 4 enters 126, 5 enters after 4 24.
- **Reading** [observation]. In short windows the outcome is a race among a few entries and exits, decided by one
  pair inequality, most often (runner 5 entering, runner 4 leaving) or (runner 4 entering, runner 3 leaving). This
  is the lap-box criterion restricted to these runners, so it names which pair decides but adds no new mechanism.
  When a window fails, the next J123 window is the next place to look: that is a step of the cascade's walk.
  So the §5 question "why does the first or second window succeed" is again the question why the cascade's walk
  stops within one or two windows. For native against reformulated, §5 at this level is the cascade itself
  (described exactly) without a forcing argument; BHK's Lemma 4 forces only the long-window regime.

**E38. §5 natively: the two-runner window lemma, and where one window is not enough (2026-10-15).** Owner: *"This is
a good idea"*, of: write §5's two steps natively (a window lemma in cut-stretch terms with the threshold as a
function of d5/d4, proved in Lean; then the merged-pair statement that a long enough stretch occurs).
- **Sharp threshold** (`six_window_L_v1.py`, `six_window_L_v2.{py,out}`). In runner-4 laps, ρ = d5/d4 >= 1, the
  longest a window can last before runners 4 and 5 are first clear together is
  L(ρ) = max(1/3 + 1/(3ρ), (m + 1/3)/ρ), m the largest integer below (ρ+1)/3. Derivation: a window with no common
  clear point holds at most one full runner-4 blocked stretch (1/3), with runner 5 blocked whenever runner 4 is
  clear on either side; the second term is the resonant case, where runner 5's blocked windows fall on both sides.
  Checks: on 237 ratios no starting pair exceeds L, and the search comes within 3.3e-4 of it (sharp); max over ρ is
  2/3, at ρ = 1. Resonance: L(5/2) = 8/15 > 1/3 + 2/15. E36 data: none of the 566 failing windows has l4 >= L(ρ),
  and all 833 windows with l4 >= L(ρ) succeed.
- **Lean** (`WindowTwoRunner_v1.lean`, `.out`; [propext, Classical.choice, Quot.sound]):
  - `window_two`: speeds 0 < a <= b. Any window [J₀, J₀ + ℓ] with ℓ >= 1/(3a) + 1/(3b), and ℓ >= (m + 1/3)/b for
    every integer m with 3ma < a + b, contains an instant at which both are clear. The proof is constructive,
    with four candidate instants.
  - `window_two_uniform`: ℓ >= 2/(3a) always suffices.
- **Source** (BHK 2001 §2, read from `bhk_2001.pdf`). Lemma 4: "If I is a 45-block then |I| < 2x4/3", x_i = 1/v_i;
  its proof is the same structure (at most one 4-block, then 5-blocks). So `window_two_uniform` is BHK's Lemma 4,
  and `window_two` is Lemma 4 sharpened by the speed ratio: a 45-block is shorter than L(ρ)·x4 [reading of the
  printed proof; citation-verifier owed before this is cited]. Corollary 5 uses Lemma 4 on a 3-gap that is also a
  123-gap (length 2x3/3). In BHK's §5 ({v1 t0} = 0), no such gap of length 2/3 exists, and Case 5.1 works with pairs
  of 123-gaps of length 1/2 ("triple configurations"); its premise (22) "Lemma 4 implies x4 > 3/4" is where the
  sharp L(ρ) would apply.
- **Step 2 as proposed is false** (`six_s5_longstretch_v1.{py,out}`). Over one period of each §5 set in [1,40], the
  longest J123 window:
  - reaches L(ρ) in 1,862 sets (1,416 of them also reach BHK's uniform 2/3; the sharp lemma adds 446);
  - reaches neither in 582, with the longest window 0.5–1.0 of L(ρ), e.g. (1,3,4,5,6): longest 0.347 against
    L = 0.611; (1,8,9,11,30): 0.484 against 0.489.

  So "a long enough J123 stretch occurs" does not hold across §5. One window and the window lemma close 1,862 sets;
  the other 582 need what BHK's Case 5.1 and Proposition 11 supply: two shorter 123-gaps near each other that
  runners 4 and 5 cannot both block.
- **Native against reformulated, §5, as it stands.** The window step is native and sharper than BHK's (Lean). The
  existence step is not a single statement: for 582 of 2,444 sets it needs a two-window argument, BHK's triple
  configuration in shape. Not yet done: that two-window statement in cut-stretch terms.

**E39. The two-window statement for the 582 sets (2026-10-15).** Owner: *"Work out the two-window statement for the 582
sets in cut-stretch terms: when two J123 windows near each other cannot both be blocked by runners 4 and 5, starting
from BHK's Case 5.1 triple configuration and Claims 9-10 (source first), then check it on the 582."*
- **Source** (BHK §5, read in full from `bhk_2001.pdf`; units v3 = 1, x_i = 1/v_i). Case 5.1 (t0 v1 = k ≥ 3): a
  triple configuration is I1 = [t, t+1/2], I3 = [t+1, t+3/2], both clear of runners 1–3, with I2 between.
  - Claims 9–10: if runners 4, 5 block I1 ∪ I3, no runner-4 block lies inside I2, I1 or I3; so one runner-4 gap
    straddles the middle and runner 5 covers the rest ((26)). This forces x4 > 9/10 ((27)); for l+1 windows,
    x4 > (6l+3)/(6l+4) ((30)).
  - The merged pair supplies the windows: near each 2–3 meeting runners 2, 3 stay within 1/6, so 23-gaps there
    are at least 1/2 long ((31)–(32)). The leftover sub-cases 5.1.1 and 5.1.2 are closed by explicit 1234-gaps.
  - Case 5.2 (k = 1, 2) is Proposition 11, not triple configurations.
- **Cut-stretch form.** Two J123 windows of lengths α and γ, a distance β apart (runner-4 laps), ρ = d5/d4. The
  geometry is SAFE when, for every pair of start readings (a4, a5), runners 4 and 5 share a clear point in at least
  one window. Per window the test is the first common clear time f from `window_two`'s four-candidate
  construction: SAFE iff no (a4, a5) has f(a4, a5) > α and f(shifted by α + β) > γ. This is BHK's argument with
  the phases quantified over and the windows taken from runners 1–3 as they are, not from the length-1/2 model.
- **Check** (`six_two_window_v1.py`, `six_two_window_v1_N200.out`, `six_two_window_v1_N600.out`). On the 582 §5 sets
  with no single long-enough window (E38), pairs of J123 windows within one period, up to three windows apart:
  - **Control:** at each set's own phases, the formula's first common time equals the exact one (closed bands) in
    3,478 of 3,478. A first control compared against positive-length band intersection and disagreed in 83:
    touching single-point overlaps, which are lonely instants.
  - **Covered by a SAFE pair: 576 of 582** (identical at grid N = 200 and N = 600), at window distance 1 (331),
    2 (117), 3 (128). Which pair is found first moves slightly with N (thin failing regions), so SAFE is a
    **numeric** verdict, not a proof [C, numeric].
  - By BHK's k = v1/(v3 − v2): 540 of the covered sets are k = 1 or 2, Proposition 11's case; 36 are k = 3, 4, 6, 7
    (Case 5.1).
  - **Not covered: 6, all k = 1 or 2:** (1,3,4,5,6), (2,6,8,10,11), (4,12,16,20,23), (4,12,16,20,25),
    (5,15,20,24,26), (7,21,28,36,40). They are near the pattern k·(1,3,4,5), the first four speeds of the tight set
    (1,3,4,5,9).
- **Reading** [observation]. Read in cut-stretch terms, BHK's triple-configuration idea (two windows that runners 4
  and 5 cannot both block, whatever their phases) covers, numerically, 576 of the 582 sets the single-window lemma
  misses. That includes most of Proposition 11's sets, which BHK treat by other means. What remains is six sets near
  the tight configuration, where a phase-free argument over window pairs is not enough.
- **Native against reformulated, §5, updated.** Single window (Lean, sharper than Lemma 4): 1,862 of 2,444. Two
  windows (numeric): 576 more. Remaining: 6 near the tight set. None of the existence-of-windows steps is proved;
  they are observed per set. Owed for a proof: (i) a proof of SAFE for the geometries used (exact, not a grid);
  (ii) a statement of which geometries the merged pair guarantees; (iii) the six sets.

**E40. The six uncovered sets are BHK's q = 4 case (Lemma 13) (2026-10-15).** Owner: *"Look at the six uncovered sets
near k(1,3,4,5): where their lonely instants are, in cut-stretch terms, and what BHK's Proposition 11 does with them
(source first). Observation only."* `six_q4_sets_v1.{py,out}`; BHK 2001 §5 Part 2 (read from `bhk_2001.pdf`).
- **Identification.** All six have v1/v3 = 1/4 (in BHK's units v3 = 1: v1 = 1/4, v2 = 3/4), i.e. Proposition 11 with
  q = 4. BHK separate exactly this case as **Lemma 13** ("If v1 = p/q, v2 = (q-p)/q and B0 = R+ then q ≥ 5"),
  because their equidistribution steps (Corollary 15, Lemma 18) need q ≥ 5. Ported in Lean as
  `OrderSixPropElevenN.lean` (BHK Lemma 13, explicit q = 4 gaps). In BHK's notation v4 = r/4, v5 = s/4: r = 5 in
  four of the six ((1,3,4,5,6), (2,6,8,10,11), (4,12,16,20,23), (4,12,16,20,25)); r = 24/5 and 36/7 in the other
  two, which are not integers.
- **BHK's argument for q = 4.**
  - Two explicit 123-gaps, I1 = [2/3, 5/6] and I2 = [13/6, 44/18].
  - Explicit inequalities show I2 is covered by neither runner 4 nor runner 5 alone, so Lemma 12 forces r, s to be
    integers. Lemma 12 is the denominator argument: positions of a runner at times u + iq are equidistributed, and
    at most (n+2)/3 of n such positions are blocked.
  - Lemma 4 on I2 (length 5/18) gives r ∈ {5,…,9}, each closed by an explicit 1234-gap. For r = 5:
    "[13/6, 68/30] is a 1234-gap of length 1/10".
- **The six in cut-stretch terms.**
  - With v1/v3 = 1/4 the J123 pattern is rigid: per period 4 (BHK time), four windows [2/3, 5/6], [14/9, 11/6],
    [13/6, 22/9], [19/6, 10/3] (mod 4), of lengths 1/6, 5/18, 5/18, 1/6. These are BHK's I1 and I2 and their mirror
    images under t -> 4 - t. All are shorter than L(ρ) (at most 0.357 runner-4 laps against L about 0.6), so
    neither one window nor a phase-free pair suffices: these sets are not covered for a structural reason.
  - **r = 5** (four sets): a lonely piece of length 1/10 in I2, [13/6, 34/15] = [13/6, 68/30], entered by runner 3
    and left by runner 4. This is BHK's r = 5 1234-gap exactly, with runner 5 clear there in (1,3,4,5,6) and
    (4,12,16,20,25). Its mirror is [26/15, 11/6] in the window [14/9, 11/6] (entered by 4, left by 3). Where runner 5
    blocks one of the two, the other survives: (2,6,8,10,11) keeps [26/15, 11/6]; (4,12,16,20,23) keeps
    [26/15, 11/6] and a shorter piece in I2, [152/69, 34/15], entered by 5. Single-point lonely instants also occur
    (entered by 4, left by 1, at 10/3, 14/3, …).
  - **r non-integer** ((5,15,20,24,26), (7,21,28,36,40)): 16 and 22 lonely pieces or points per period, longest 5/18
    (entered by 2 or 3, left by 3 or 2). In BHK's route these are settled before any r-casework: if no single
    runner covers I2, Lemma 12 forces integer r, s, and these sets do not have them.
- **Reading** [observation]. The six are where runners 1–3 have only short, rigid windows (q = 4), so existence
  depends on the exact value of runner 4's speed, not on phases. BHK's treatment there is by the speed's
  denominator (Lemma 12) and then r-by-r explicit gaps, and the cascade's lonely instants for r = 5 are BHK's own
  1234-gap and its mirror. Natively, this is a finite rigid case: runners 1–3 fixed at ratio (1,3,4), with runner
  4 bounding the lonely piece against runner 3. Lemma 12's equidistribution step is a residue count over the
  positions of a runner at times u + iq; it is not yet stated in framework objects.

**E41. The two-window step made exact (2026-10-15).** Owner: *"Replace the grid SAFE test with an exact one and recheck
the 576, so the two-window step is not numeric."* `six_safe_exact_v1.py` (`six_safe_exact_v1_control.out`),
`six_safe_recheck_v1.{py,out}`, `six_safe_witness_check_v1.out`.
- **Method.** A start (a4, a5) is the line of slope ρ at offset c = a5 - ρa4, plus a position s0 on it. Along each
  line, K(c), where runners 4 and 5 are both clear, is a union of closed intervals. Its ends are runner-4 ends
  (constants) and runner-5 ends (linear in c). Both windows fail iff [s0, s0+α] and [s0+δ, s0+δ+γ] lie in open
  gaps of K(c). For fixed c the good s0 form an exact union of open intervals. The combinatorics change only at
  critical c, where a runner-5 end minus a runner-4 end equals one of the window constants {0, ±α, ±γ, ±δ, ±(δ-α),
  ±(δ+γ), ±(δ+γ-α), ±(γ-α)}; 4-4 and 5-5 differences do not depend on c. The failing set is open, so the test
  decides at every critical c and the midpoint of every slab between them, in exact rational arithmetic.
  Completeness of the critical list is argued, not formalised [A].
- **Control.** With both windows equal (one window), the test is unsafe at L(ρ) - 1/1000 and safe at L(ρ), for all
  10 ratios tried (1, 11/10, 3/2, 2, 5/2, 3, 7/2, 4, 11/2, 7). This also confirms, exactly, that L(ρ) of E38 is sharp.
- **Recheck.** Same 582 sets, same window pairs (2,811 pairs tested): **576 covered exactly** and the same 6 not
  covered (the q = 4 sets of E40). Four pairs the grid had called SAFE are not: they have failing starts in thin
  slivers (s0-intervals about 5e-4 wide), e.g. (2,18,20,28,31) pair (0,1), c = 731/1680. Each such set is still
  covered by another pair. Two of the failing starts checked independently with the exact first-common-time
  formula: both windows fail, by margins down to 3e-4.
- **Status of §5, natively:**

  | step | sets | grade |
  |---|---|---|
  | one long window (`window_two`) | 1,862 | Lean |
  | two windows, phase-free | 576 more | exact decision per geometry [X], given the critical-list argument [A] |
  | q = 4 (BHK Lemma 13) | 6 | open natively |

  Still owed for a proof: that runners 1–3 produce the window geometries used (here they are read off each set,
  not derived from the merged pair), and the q = 4 case.

**E42. The shift budget at finer scales on SixResidual (2026-10-15).** Owner, on what forces order five natively:
*"Well if we think about what we are trying to set up here and overarching system for n=3 to 7. What forces it
natively for n=5?"*; then *"Yes: on SixResidual, at the divisible flank e = 6E where all coarse shifts are blocked,
observe the blocking at the finer cell scale (cell_criterion) and the order-five scale change, and whether some cell
is always free. Observation only."*
- **Order five's forcing, from the Lean module docs** (`OrderFiveN`, `OrderFiveResidualN`, `RealFiveN`).
  - The grid instant 1/5 when no disparity is a multiple of 5.
  - The descent: a cost budget passes the set to the cofactors of its multiples.
  - The divisible flank: at most three other runners against the four unit shifts of ℤ/5.
  - The last sub-case: the fastest runner's lap points K/F (units of ℤ/F), a change of scale, and shifts by k/5,
    four shifts with at most three blocked.
  - Real speeds: merge to a model with fewer runners and order four's margin.

  Orders 3, 4: the cascade from the bound terminates (`OrdersThreeFourN`). Order 7: budgets over units mod 7,
  "what does the work is φ(n) = n − 1" (`OrderSevenTotientN`). Order 6 (`OrderSixN`): the same rules, with the
  divisible flank's budget φ(6) = 2; what is left is `SixResidual`.
- **Cell scale** (`six_cells_budget_v1.{py,out}`; all 17,135 SixResidual sets in [1,40]; openings j = uE + i at a
  divisible flank e = 6E):
  - All coarse shifts (row i = 0) are blocked at every divisible flank: 20,744 of 20,744.
  - Finer rows: some cell free at 12,607 flanks, none at 8,137. The least free row is mostly i = 1 (for E ≤ 6:
    i = 1 in 10,946, i = 2 in 1,411, i = 3 in 231, i = 4 in 18).
  - Per row, each runner blocks exactly its descent cost. d mod 6 ∈ {1, 2, 4, 5} blocks 2 of 6 shifts in every
    row; d ≡ 3 blocks 3 or 0; another multiple of 6 blocks 6 or 0. The cost law repeats row by row.
  - Free rows: 29,501 free although the blocked total (with overlaps) is ≥ 6, freed by overlap of blocked shifts;
    3,648 free with blocked total < 6 (by budget). So at the finer scale the budget does not force a free cell;
    free cells come from coincidences of blocked shifts, decided by the phases a = ((d i + q) mod 6E)/E.
  - Sets: 12,401 have a lonely opening at some divisible flank; 4,734 have none. In those 4,734, lonely openings sit
    at non-divisible flanks (speed ranks (2,3,4,5) in 2,029, (1,3,4,5) in 1,191, …;
    `six_cells_budget_rest_v1.{py,out}`).
- **Order five's lap-point shift, carried to six** (`six_lapshift_v1.{py,out}`): instants K/F + k/6, F the fastest,
  K in [0, F), k = 1..5; enumerating every K includes every scale change K -> mK. Some such instant is lonely in
  13,502 of 17,135 residual sets, and in 4,700 of the 4,734 with no divisible-flank opening.
  - **Neither mechanism: 34 sets**, e.g. (1,2,6,8,10), (1,3,4,5,6), (1,3,4,5,12), (1,3,5,8,12), (1,4,5,9,12),
    (1,4,5,9,18), (1,4,12,16,20), (1,5,8,9,12): the q = 4 family (v1/v3 = 1/4) and sets containing 1, 4, 5, 9 (part
    of the tight set (1,3,4,5,9)).
  - Only whether a candidate instant is lonely was checked, not a per-runner budget for these shifts.
- **Reading** [observation].
  - At orders 5 and 7 the native forcing is a budget over unit shifts that closes because φ(n) = n − 1. At order 6
    the same budget, refined to cells, does not close: each row costs what the coarse row costs, and residual sets
    exceed 6 per row by definition (the descent's budget is spent).
  - Free cells and lonely lap-point shifts exist in all but 34 residual sets, but they come from residue
    alignment (overlap of blocked shifts), not from the count.
  - The leftover sets sit near the tight configurations, where lonely sets are thinnest.
  - The candidate-instant checks (do these discrete instants meet the lonely set, per set) are the form of E2's
    `six_folded_coverage_v1`, though per set, not phase-free. Owner's call whether that is inside the E2
    set-aside.

**E43. The alignment that frees cells: ℤ/6 = ℤ/2 × ℤ/3 (2026-10-15).** Owner: *"Observe the residue alignment that frees
cells at divisible flanks: which runners' blocked shifts coincide, in terms of the phases a = ((d i + q) mod 6E)/E.
Observation only."* `six_cells_align_v1.{py,out}`, `six_cells_crt_v1.{py,out}`; SixResidual in [1,40], every divisible
flank e = 6E, every row i.
- **Shapes.** At row i a runner with s = d mod 6 and phase a (the sixth its reading occupies at opening i) blocks
  shift u iff (a + s u) mod 6 ∈ {0, 5} (cell_criterion, s = 1..5). Control: 251,144 of 251,144 runner-rows agree
  with direct blocking. A first version applied the sixth-index rule to other multiples of 6 too and disagreed in
  148, all readings exactly 5/6, which is clear; for s = 0 the exact reading now decides. In CRT coordinates
  u <-> (u mod 2, u mod 3):
  - s = 3 removes a parity layer (three shifts, one value of u mod 2), or nothing;
  - s = 2, 4 removes a mod-3 column {c, c+3};
  - s = 1, 5 removes {c, c+1}: one point in each parity layer;
  - another multiple of 6 removes all six shifts or none.
- **The rule.** For each parity layer left open by the s = 3 runners, with R the columns removed by the s = 2, 4
  runners and P the points the unit runners remove there, the free shifts in that layer number 3 − |R| − |P \ R|.
  This reproduces FREE/FULL in every row (0 mismatches). 9,853 rows were skipped because another multiple of 6
  blocks every shift.
- **What frees a cell.** The alignment is a unit runner's point falling inside an even runner's column, the two
  runners blocking the same shift.
  - Commonest FREE row (8,203): |R| = 1, two unit points, one inside R: 3 − 1 − 1 = 1 free.
  - Its FULL twin (5,935): the same counts with neither point inside R: 3 − 1 − 2 = 0.
  - Next: |R| = 2 and one unit point inside R (FREE, 6,881) against outside R (FULL, 3,485).

  Coinciding unit points also free cells (e.g. 2,127 rows: two unit points, one distinct). FULL rows also arise when
  both parity layers are removed (2,742) or |R| = 3 (3,789).
- **In phase terms.** Whether a unit runner's point lies in an even runner's column is a congruence mod 3 between
  their phases (with s ≡ ±1 mod 3); which layer is open is a parity condition from the s = 3 runner's phase. So the
  alignment is the ℤ/3 component of the readings, sixths taken mod 3. These are the same coordinates as the coarse
  residue pinning ({1,2,3,5}, {1,3,4,5}) and the totient law: φ(6) = 2 = φ(2)·φ(3).
- **Reading** [observation]. At order six the shift grid is ℤ/2 × ℤ/3, and each runner removes a fixed shape: a
  parity layer, a mod-3 column, or one point per layer. The budget counts these shapes and is over; cells come free
  when shapes overlap, and the overlap that matters is a unit runner's point inside an even runner's column, a
  mod-3 coincidence of phases. This is a native, residue-level description of what frees a cell. It does not yet
  say why some row at some divisible flank always has that coincidence; in 4,734 residual sets none does, and the
  isolation is at a non-divisible flank (E42).

**E44. Global isolation at orders 3–7: how many events, and their patterns (2026-10-15).** Owner: *"Can we also look if
there is any relationship between how many global isolations and their patters so what does global isolation look
like for n=3...7"*. `global_isolation_v1.{py,out}`, `tight_general_v1.{c,out}`.
- **The framework's statement** (`LRC/ConstructionN/Instants.lean`). A primitive arrangement of n runners whose
  speeds are distinct mod n is in global isolation (all pairs at least 1/n apart) exactly at the φ(n) instants p/n
  with gcd(p, n) = 1 (`isolation_iff_coprime`, `card_coprime_eq_totient`), and at no instant off that grid
  (`isolation_forces_coprime_grid`).
- **Patterns, n = 3..7** (`global_isolation_v1.out`).
  - At p/n the residue r goes to position r·p mod n: the arrangement is multiplication by the unit p.
  - p and n − p are mirror images (t -> 1 − t).
  - The subject's two neighbours, at distance exactly 1/n, are the residues ±p⁻¹. For the AP 1..n−1, runner p⁻¹
    enters and runner n − p⁻¹ leaves at p/n.

  | n | φ(n) | instants p | mirror pairs | every nonzero residue a unit |
  |---|---|---|---|---|
  | 3 | 2 | 1, 2 | (1,2) | yes |
  | 4 | 2 | 1, 3 | (1,3) | no |
  | 5 | 4 | 1–4 | (1,4), (2,3) | yes |
  | 6 | 2 | 1, 5 | (1,5) | no |
  | 7 | 6 | 1–6 | (1,6), (2,5), (3,4) | yes |

  Cycle types of r -> p r: identity for p = 1; p = n − 1 pairs residues; at n = 5, p = 2, 3 are 4-cycles; at
  n = 7, p = 3, 5 are 6-cycles and p = 2, 4 are 3-cycles (the unit group of ℤ/7 is cyclic of order 6, of ℤ/5 of
  order 4; ℤ/4 and ℤ/6 have only ±1).
- **Tight configurations** (`tight_general_v1.out`; every lonely interval a point; primitive sets of n−1 speeds in
  [1,H]): n = 3, H = 300: (1,2) only. n = 4, H = 150: (1,2,3) only. n = 5, H = 80: (1,2,3,4) and **(1,3,4,7)**.
  n = 6, H = 60: (1,2,3,4,5) and (1,3,4,5,9) (E24 to H = 200). n = 7, H = 36: (1,…,6) only. No counterexample at
  any order in these ranges. Literature on tight instances not checked (citation-verifier owed if used).
- **The relationship** [X in these ranges].
  - Every tight set has exactly φ(n) lonely points per period, at the unit instants p/n, all simple (one entering,
    one leaving). At p/n the entering runner has residue p⁻¹ mod n and the leaving runner −p⁻¹; e.g. (1,3,4,7) at
    2/5: 3 enters (3·2 ≡ 1), 7 leaves (7·2 ≡ −1).
  - Any set with no multiple of n is lonely at every unit instant p/n: the readings are (d p mod n)/n with
    d p ≢ 0. This is R6. A tight set is one where these are the only lonely instants and each is a point.
  - For the points to be single points, the speeds' residues must contain ±p⁻¹ for every unit p, i.e. every unit
    mod n. At n = 7 that forces residues {1,…,6}; (1,3,4,7) has residues {1,3,4,2}, all units of ℤ/5;
    (1,3,4,5,9) contains 1 and 5, the units of ℤ/6.
- **Reading** [observation]. The number of global-isolation events is φ(n), and they are the unit grid
  instants, in mirror pairs. That number is also the capacity of the coarse shift budget at a divisible flank (R4:
  the units of ℤ/n are the available shifts). At the totient-full orders 3, 5, 7 every nonzero shift is an
  isolation event and the budget closes. At 4 and 6 there are only the two events ±1/n: order 4 still closes
  (three runners, the cascade terminates), while order 6, with five runners against two events, leaves
  SixResidual. So the count of global isolations and the native forcing are the same number.

**E45. The hunch checked: isolation events are the units, and blocking needs all of them (2026-10-15).** Owner: *"I
mean at n=8 there are 4 isolation events before a grand return and the pattern repeats. But how many global isolation
point are there for each of the others... Im asking out of a hunch"*, *"I thought there was a link there we were
missing"*, *"Lets check this idle fancy, its how we discovered global isolation in the first place and its not hard to
check"*. `units_blocking_v1.{py,out}`, `units_link_v1.{py,out}`. Order 8 appears as a comparison only.
- **Events per period** (E44): φ(n) at the unit instants p/n: n = 3: 2, 4: 2, 5: 4, 6: 2, 7: 6, 8: 4. The unit groups
  are cyclic for n = 3..7; for n = 8, ℤ/2 × ℤ/2 (every unit squares to 1).
- **Coarse shifts at a divisible flank** (u ∈ ℤ/n; a slower runner with residue r blocks u iff r u mod n ∈ {0, n−1},
  the n-ary form of SixCells.Blocks). Checked by enumeration for n = 3..8 [X]:
  1. a unit r blocks exactly {0, −r⁻¹}: shift 0 and one event shift. A non-unit r (g = gcd(r, n) > 1) blocks exactly
     the multiples of n/g, a subgroup of non-event shifts; r u ≡ −1 has no solution;
  2. so event shifts are blocked only by unit runners, one event each, and non-event shifts only by zero divisors;
  3. hence all n shifts are blocked iff the slower runners' residues contain **every unit** and their non-unit
     residues cover the non-event shifts.

  This reproduces `SixCells.all_shifts_blocked_iff` exactly (1, 3, 5 ∈ R and 2 or 4 ∈ R). With at most n − 2 slower
  runners, blocking is impossible at n = 3, 5, 7 (φ(n) = n − 1 units needed) and at n = 4 (units 1, 3 plus 2: three
  runners, two available); possible at n = 6 (minimal {1,2,3,5}, {1,3,4,5}) and n = 8 (minimal {1,3,4,5,7}).
- **The link to degenerate configurations** (`units_link_v1.out`).
  - Every tight set at n = 3..7 (E44) has residues containing every unit, which is what makes each event instant a
    single point.
  - At n = 6 both tight sets also contain a full minimal blocking pattern: (1,2,3,4,5) ⊇ {1,2,3,5};
    (1,3,4,5,9) has residues exactly {1,3,4,5}.
  - The E42 leftovers (no divisible-flank opening, no lap-point shift), 8 examples shown: 6 carry a full pattern
    ({1,3,4,5} or {1,2,3,5}), 2 have residues {1,2,4}.
- **But SixResidual is not characterised by it.**
  - Residues of the non-multiples contain a full pattern in 2,809 of 17,135 residual sets, both units in 6,301,
    neither in 10,834.
  - For all 364,955 primitive 5-sets in [1,40] with a multiple of 6: pattern in 24,690, both units in 103,535.
  - So the pattern is more frequent among residual sets but not required. Coarse blocking there also comes from
    runners faster than the flank (phase d/e ≠ 0) and from other multiples of 6, which the phase-0 rule does not
    cover.
- **Reading** [observation].
  - The global-isolation events are the units mod n, and the coarse budget at a divisible flank splits exactly along
    them: units block events one-for-one, zero divisors block subgroups of non-events.
  - Blocking every shift needs every event residue present. That is the same residue signature that makes the tight
    configurations degenerate; at order 6 the tight sets carry the full blocking pattern.
  - The hard cases sit where the configuration's residues contain all the isolation events (the degenerate
    signature), and order 6 (and 8) are the orders where the runner count allows that with zero divisors to spare.
  - Not yet: the same split for runners faster than the flank (non-zero phase), which is what SixResidual mostly
    uses. Statements (1)–(3) are elementary and could be a kernel `decide` per n; not formalised.

**E46. The split with phases: runners faster than the flank (2026-10-15).** Owner: *"Extend the unit / zero-divisor split
to runners faster than the flank (non-zero phase), to see whether it characterises SixResidual's coarse blocking.
Observation only."* `units_phase_v1.{py,out}`, `units_phase_tally_v1.{py,out}`; every divisible flank e = 6E of every
SixResidual set in [1,40], coarse shifts u (openings j = uE).
- **Phase rule.** A runner with s = d mod 6 and phase a = ⌊d/e⌋ mod 6 (0 when slower than the flank; FreeFlank's
  (d k + d/e) % 6) blocks u iff (s u + a) mod 6 ∈ {0, 5}; a reading exactly at 5/6 (d/e an integer) is clear.
  Control: 82,976 of 82,976 runner-flanks agree with direct blocking. All coarse shifts are blocked at all 20,744
  flanks (as E42).
- **E45's separation mostly fails.** "Events {1, 5} blocked only by units, non-events {2, 3, 4} only by zero
  divisors" holds at 1,560 of 20,744 flanks; at 1,525 of those no runner is faster than the flank, i.e. all phases
  are 0. Event shifts are blocked by units only 11,131 times, by zero divisors or multiples only 19,155, by both
  11,202.
- **How faster zero divisors reach the events.** With a ≠ 0 a zero-divisor runner blocks a translate (coset) of its
  subgroup instead of the subgroup:
  - s = 2, 4 (subgroup {0, 3}): the column {1, 4} or {2, 5}, each containing an event; e.g. (s, a) = (4, 1) ->
    {1, 4}: 4,185; (2, 1) -> {2, 5}: 4,134;
  - s = 3 (subgroup {0, 2, 4}): the odd layer {1, 3, 5}, containing both events; (3, 2): 2,968, (3, 3): 1,283.
- **What does characterise it.** The (s, a) rule is exact. In group terms, a unit blocks two points s⁻¹(−a),
  s⁻¹(−a − 1); a zero divisor blocks one coset of its subgroup, chosen by its phase; another multiple of 6 blocks
  everything or nothing. E45's clean split is the special case where every phase is 0: the flank is the fastest
  runner, the case R4 settles.
- **Reading** [observation].
  - The unit / zero-divisor split characterises coarse blocking only when nothing is faster than the flank. In
    SixResidual the divisible flanks almost always have faster runners, and those zero divisors block cosets
    that contain events. That is how SixResidual blocks the budget without carrying every unit in its residues
    (E45: only 2,809 of 17,135 carry a full pattern).
  - Order five's remaining case has the same shape: a multiple of 5 that is not the largest, i.e. a flank with a
    faster runner. Its native move goes to the fastest runner's lap points, where that runner is at phase 0.
    E42's lap-point instants K/F + k/6 are that move at order six and caught 4,700 of the 4,734 sets with no
    divisible-flank opening.
  - Not yet observed: the unit / coset structure at the fastest runner's lap points, i.e. whether the clean split
    returns there.

**E47. Two more facets: the split at lap points, and neighbours against bystanders (2026-10-15).** Owner: *"Interesting,
there is something here but we are only seeing one side of it, there are more facets"*; *"Yes you can look at spliat at
lap points. I also wonder if we should track the neighbour for each isolation or the bystanders"*.
`lap_split_v1.{py,out}`, `neighbours_bystanders_v1.{py,out}`; SixResidual in [1,40].
- **Split at the fastest runner's lap points** (instants K/F + k/6, k ∈ ℤ/6; phase of runner d = sixth of its reading
  at K/F; rule (s k + a) mod 6 ∈ {0, 5} with exact edges; control 3,005,550 of 3,005,550).
  - Lonely lap-point shifts exist in 13,502 sets (as E42); never at k = 0, where the fastest runner reads 0.
  - The lonely shifts are events (k = 1, 5) 183,432 times and non-events (k = 2, 3, 4) 188,108 times.
  - E45's separation holds at 23,162 of 601,110 frames (K), and at 22,704 of the 240,794 frames that have a lonely
    shift. At those frames most runners are off phase 0: one runner at phase 0 in 123,812, two in 98,278.

  The clean split does not return at lap points: the fastest runner is at phase 0 but the others are not.
- **Neighbours and bystanders** (at a lonely instant the neighbours are the runners nearest the subject, least
  reading = entry side, largest = exit side; the rest are bystanders; classified by d mod 6). Baseline over all
  runners of residual sets: unit 0.285, zero divisor 0.473, multiple 0.242.
  - Cascade ending T: entry neighbour zd 0.533, unit 0.307, mult 0.160; exit zd 0.531, unit 0.270, mult 0.199;
    bystanders zd 0.434, mult 0.284, unit 0.282. The entry neighbour sits exactly at 1/6 in all 17,135 (the flank
    whose opening is T); the exit neighbour exactly at 5/6 in 852. Commonest (entry, exit) residues: (4,2) 869,
    (3,0) 702, (4,3) 689, (4,4) 687, (5,1) 686.
  - First lonely lap-point instant: entry zd 0.421, unit 0.323, mult 0.256; exit zd 0.468, unit 0.288, mult 0.244;
    bystanders zd 0.543, unit 0.253, mult 0.205. Neighbours rarely on an edge (both on an edge: 26 of 13,502).
- **Reading** [observation].
  - In global isolation the neighbours are units (±p⁻¹) and the bystanders carry the rest (E44). In SixResidual's
    isolations, classified mod 6, the neighbours are close to the overall mix: zero divisors slightly over, multiples
    under at the cascade ending.
  - So the unit / zero-divisor facet of global isolation does not carry over to these isolations at modulus 6,
    and the clean split does not return at lap points.
  - A different modulus may be the right one for a non-grid isolation: at an opening (6k+1)/(6b) the natural
    residues are d(6k+1) mod 6b, with the flank b's units (the CRT/coprime form, E-early). Not yet observed.

**E48. Neighbours and bystanders by the flank's own modulus (2026-10-15).** Owner: *"Classify neighbours and bystanders at
each isolation by the flank's own modulus: units versus zero divisors of the flank speed b (gcd(d, b)), and the residues
d(6k+1) mod 6b. Observation only."* `flank_modulus_v1.{py,out}`; SixResidual in [1,40].
- **Instrument.** Isolations: every lonely opening (b, k), k < b, of every set (304,712), and the cascade's ending
  (17,135). The flank b reads exactly 1/6. For the other runners, R = d(6k+1) mod 6b. Neighbours: the exit neighbour
  (largest R) and the entry-side neighbour other than the flank (least R); the rest are bystanders. Classes by
  gcd(d, b) = 1 (unit of ℤ/b) or > 1.
- **All lonely openings:** unit mod b in all runners 0.551, exit neighbour 0.551, entry neighbour 0.542, bystanders
  0.555. No separation.
- **Cascade ending:** all runners 0.567, exit 0.547, entry neighbour 0.607, bystanders 0.556. A small excess of units
  on the entry side.
- **The extra factor gcd(d, 6b)/gcd(d, b)** (what the 6 adds) of (exit, entry) neighbours: (1,1) commonest
  (68,662 of 304,712 openings), then (1,2), (1,3), (2,1), (3,1), (2,2). Spread across all classes.
- **Edges.** Neighbours exactly on an edge (entry R = b, exit R = 5b): both 890 of 304,712 openings (97 of 17,135 at
  the ending); exit only 10,257; entry only 4,042. Typical positions: entry R/b about 1.1–1.6, exit 4.2–5.0.
- **Reading** [observation].
  - By the flank's modulus, as by 6 (E47), neighbours and bystanders have the same unit / zero-divisor mix: this
    facet of global isolation (neighbours = units ±p⁻¹) does not carry over to non-degenerate isolations.
  - In global isolation the neighbours are units because they sit exactly on the edges, at residues ±b·m⁻¹ in
    these terms. In SixResidual's isolations both neighbours are exactly on the edges in only 890 openings; the
    others are near the edges, and nearness does not pick a gcd class.
  - Where the unit structure does show is in which shifts are blocked (E45, E46), not in who neighbours an
    isolation.

**E49. The owner's examples (1..7, 16) and (1..5, 16, 64, 720) at threshold 1/8 (2026-10-15; order 8 as comparison
only).** Owner: *"1...7,16 and 1...5,16, 64, 720 both achieve global isolation"*; *"Did you check using boundary set
method or the cascade, also did you go and how many cycles did you run?"* `gi_examples_v1.py`,
`gi_examples_cascade_v1.{py,out}`.
- **All eight at once** (exact boundary sweep: every instant where some pair is exactly 1/8 or 7/8 apart, and midpoints,
  one full period (0, 1], differences of gcd 1). (1..7, 16), residues mod 8 a complete system: isolated at 1/8, 3/8,
  5/8, 7/8, the φ(8) events. (1..5, 16, 64, 720), residues 1..5, 0, 0, 0: never; 16, 64, 720 coincide at every p/8,
  and `isolation_forces_coprime_grid` excludes other instants.
- **Each runner as subject** (cascade from 1/(8 d_min), exact, with move counts; checked against an exhaustive scan of
  every opening (k + 1/8)/b, k < b; all agree).
  - (1..5, 16, 64, 720): subjects 1–5 at 1/8 (0 moves); 16 at 65/5632 (1 move); 64 at 1/384 and 720 at 1/5248
    (0 moves).
  - (1..7, 16): subjects 1–7 at 1/8 (0 moves); 16 at 1/72 (0 moves), and also at 1/8.
- **Correction.** A first reply reported per-subject times from a bounded residue search that stopped at the first
  certificate in scan order, without saying so (e.g. 9/16 for subject 3). Those were valid lonely instants but not
  the earliest; the table above replaces them.
- **Reading** [observation]. In the second set, the grid instant 1/8 isolates the whole AP block 1..5 at once: they sit
  at 1/8..5/8, the three fast runners are stacked at slot 0, and slots 6/8, 7/8 are empty. Each fast runner is
  isolated separately and much earlier, at its own first flank. So the set combines a grid (residue) isolation of
  the slow block with individual isolations of the stack.

**E50. (1,2,3,4,16,32,40,48) at threshold 1/8 (2026-10-15; comparison only).** Owner: *"Ok so 1,2,3,4,16,32,40,48 does
globally isolate though?"* `gi_example3_v1.out`.
- **All eight at once:** never (exact boundary sweep over one full period; differences of gcd 1). Residues mod 8 are
  1, 2, 3, 4, 0, 0, 0, 0, so 16, 32, 40, 48 coincide at every p/8 (`isolation_forces_coprime_grid`).
- **Each runner as subject** (cascade, agreeing with the exhaustive opening scan): 1–4 at 1/8 (0 moves); 16 at 1/96;
  32, 40, 48 at 1/64 (0 moves each).
- **Reading** [observation]. Two blocks on two grids. The slow block 1..4 is grid-isolated at p/8 (positions
  1/8..4/8, the fast block stacked at 0). The fast block is 8·(2,4,5,6), whose residues mod 8 are distinct, so at
  t = p/64 the fast runners sit at the grid slots (2/8, 4/8, 5/8, 6/8 for p = 1) while the slow block is bunched
  near 0. Each block is globally isolated among itself on its own grid, at scales differing by a factor of 8, never
  both at once. The same nesting reading applies to E49's (1..5, 16, 64, 720): its fast block is 16·(1, 4, 45).

**E51. BHK §7 natively: the window steps close every set; the 2D global isolation is already native (2026-10-15).**
Owner: *"Ok, now autonomously work on 7 in the same way seeing what we can push native including anything else we have
learnt for other orders"* (read as BHK §7 at order six, the generic case; order seven is already native in the
framework track). `s7_windows_v1.{py,out}`, `s7_meeting_v1.{py,out}`, `s7_exceptional_v1.{c}` with
`s7_exceptional_v1_80.out`, `s7_exc_exact_v1.{py,out}`, `s7_budget_v1.out`, `s7_relaxfail_profile_v1.out`.
- **Source** (BHK 2001 §2 generic argument; framework `OrderSixSecSevenN.lean`, `OrderSixSecSevenCasesN.lean`,
  `GlobalIsolationTwoN.lean`; dispatch `lonely6_of_lt`: §7 is 3v₁ < v₃ with D = v₃ − v₂ dividing neither v₁ nor
  v₃).
  - BHK look for a 3-gap that is also a 123-gap. At meeting times kt₀, t₀ = 1/D, runners 2 and 3 coincide, and the
    point ({kt₀}, {v₁kt₀}) must lie in their parallelogram P.
  - Lemma 4 (= `window_two_uniform`, E38) then defeats runners 4 and 5.
  - BHK's Main Lemma and Corollary 6 say the cyclic orbit G meets every box of area at least 1/n unless it has a
    short step. The framework re-proves this in whole numbers and residues as **global isolation in two
    dimensions** (`GlobalIsolationTwoN.lean`), documented there as "the same mechanism one dimension up" as R6:
    no area, no Minkowski, no measure.
  - BHK's exceptional orbits (short steps, the groups G₄ and G₇, small n) are casework in
    `OrderSixSecSevenCasesN.lean`.
- **Window steps on the §7 residual sets** (9,132 in [1,40]): a single J123 window long enough for `window_two`
  exists in all 9,132. In 9,054 it is a full 3-gap (BHK's route); 76 have a window of at least 2/(3v₄) but no full
  3-gap; 2 need the sharp L(ρ). No two-window step is needed.
- **At the meeting times** (`s7_meeting_v1.out`): BHK's main route (some meeting time in P) works in 9,054. It fails
  in 78, exactly the exceptional orbits: orbit size n = 4 (75, G₄) and n = 7 (3, G₇). In all 78, some meeting time
  has a J123 window ≥ L(ρ)/v₄ (the relaxed route: the window lemma without requiring a whole 3-gap).
- **All primitive §7 sets to 80** (10,585,393; `s7_exceptional_v1_80.out`; integer enumeration with a float window
  length, ties rechecked exactly):
  - BHK's main route fails in 29,480 (orbit n = 4: 22,813; n = 7: 6,667);
  - the relaxed meeting-time route works in 28,761 (n = 4: 22,145; n = 7: 6,616); tie-only successes: 0 after
    exact recheck;
  - of the other 719: 599 have a single long-enough J123 window off the meeting times, 120 are covered by an
    exactly SAFE two-window pair, 0 are left.

  The 719 all have v₄ within 15% of v₃ (L(ρ) near 2/3), and most have v₃/v₁ just above 3, by BHK's §8 boundary.
- **Budget mechanisms (E42) on §7 residual sets**: a divisible-flank opening or a lonely lap-point shift exists in
  9,114 of 9,132 (both 4,951; flank only 2,002; lap point only 2,161; neither 18). These are checks that such an
  instant exists, not forcing.
- **Reading** [observation].
  - §7 is the case where native and reformulated coincide most closely. The forcing step is the framework's own
    global isolation, one dimension up from R6's φ(n) grid instants (E44): the orbit of meeting times is a grid on
    the 2-torus, and it meets every large enough box unless it has a short step.
  - The window step is `window_two`. With the sharp threshold the 3-gap requirement can be dropped: at the
    exceptional orbits a single meeting-time window then suffices in 97.6% of sets to 80, and every set to 80
    is closed by one or two windows.
  - Owed for a proof that replaces BHK's G₄/G₇ casework: that the relaxed meeting-time window, or an off-meeting
    window or pair, always exists for those orbits. That is a statement about the orbit and runners 1–3, observed
    here, not derived. The two-window step is the form flagged against the E2 set-aside (owner's call, v6).

**E52. The window route in Lean (2026-10-15).** `WindowTwoRunner_v2.lean` (`.out`; [propext, Classical.choice,
Quot.sound]): v1 plus `lonely_of_window`. If runners v₁, v₂, v₃ are clear throughout [J₀, J₀ + ℓ] and ℓ meets
`window_two`'s thresholds for the fast runners a ≤ b, all five are clear at one instant of the window. This is
BHK's Corollary 5 with the sharp window in place of Lemma 4 and without requiring a whole 3-gap. It makes "window
found, therefore lonely" a proved native step; finding the window remains per set for the exceptional orbits.

**E53. BHK's exceptional orbits G₄ and G₇: an exact single-window criterion, the early window, and Lean (2026-10-15).**
Owner: *"Didn't I ask you to work autonomously? why are you coming back to me with this you could just do bothe"*
(both: commit E20–E52, done as `97075f1`; and derive the G₄/G₇ window). `s7_exceptional_v2.c`
(`s7_exceptional_v2_80.out`, `s7_exceptional_v2_120.out`), `s7_g4g7_v1.{py,out}`, `s7_g4g7_v1_120.{py,out}`,
`s7_g4g7_early_v1.{py,out}`, `s7_g4g7_early_v1_120.{py,out}`, `WindowTwoRunner_v3.lean` (`.out`).
- **Source** (BHK 2001 §7, Table 10 and the text after it).
  - G₄ = ⟨(1/2, 1/4)⟩: at the meeting time with {kt₀} = 1/2, {v₁kt₀} = 1/4 the interval I = [kt₀ − x₁/12, kt₀ + 1/3]
    is a 123-gap. If runners 4, 5 cover it, then 7/16 < x₅ < 1/2 and 7/8 < x₄ < 1, and then [2/3, 35/48] is left
    uncovered.
  - G₇ = ⟨(2/7, 1/7)⟩: J = [kt₀ − 5/14, kt₀ + 11/42] at {kt₀} = 4/7, {v₁kt₀} = 2/7, then [2/3, 65/84].
  - So BHK's treatment is one named window plus the early window after t = 0.
- **Exact checks, all primitive §7 sets to 80 and to 120** (88,278,879 sets to 120):
  - every set where BHK's main route fails is on the orbit G₄ or G₇ (to 120: 122,361 and 40,622; no other group);
  - the J123 window at BHK's named meeting time equals W₄ = 1/(3v₃) + 1/(12v₁) for G₄ and
    W₇ = 11/(42v₃) + min(17/(42v₃), 5/(42v₁)) for G₇, in every set;
  - **criterion**: a single meeting-time window closes the set by `window_two` iff W ≥ L(v₅/v₄)/v₄, with no
    exception in either direction, and no other meeting time ever does better. To 120 it holds in 118,720 (G₄) and
    40,263 (G₇) and fails in 3,641 and 359;
  - **in all 4,000 failures**, the first J123 window after t = 0 (every runner starting at 0, no free phase)
    contains a lonely instant, and that window contains BHK's early window ([2/3, 35/48]/v₃ or [2/3, 65/84]/v₃).
    It starts at 0.50–0.64 in units of 1/v₃, i.e. at runner 1's first entry 1/(6v₁).
- **Lean** (`WindowTwoRunner_v3.lean`, all [propext, Classical.choice, Quot.sound]; one unused-hypothesis warning in
  `g7_window`):
  - `g4_window`: if runners 2, 3 read 1/2 and runner 1 reads 1/4 at t, with v₁ < v₂ < v₃ < 4v₁, runners 1–3 are
    clear on [t − 1/(12v₁), t + 1/(3v₃)];
  - `g7_window`: readings 4/7, 4/7, 2/7, with v₁ < v₂ < v₃; clear on [t − l, t + 11/(42v₃)] for l ≤ 17/(42v₃),
    l ≤ 5/(42v₁);
  - `g4_lonely`, `g7_lonely`: composed with `lonely_of_window`, the orbit is lonely whenever that window length
    meets `window_two`'s thresholds.
- **Reading** [observation and proof, as marked].
  - BHK's exceptional orbits are handled natively by one stated inequality on the speeds: W₄ or W₇ against L(ρ)/v₄
    (proved, given that the named meeting time exists). Where it fails, the first window after the start does it
    (observed to 120, not derived).
  - Not yet: (i) the orbit's named point exists at some meeting time (the orbit-membership step; BHK's group
    computation, ported in `OrderSixSecSevenCasesN.lean`); (ii) the early window as a theorem in the failure region
    W < L(ρ)/v₄, which forces v₄ < (8/7)v₃ and ρ close to 1 or to 2 (the 719 profile of E51).

**E54. G₄ and G₇ closed natively, end to end, in Lean (2026-10-16).** Owner: *"We better look into that then"* (the two
owed items of E53: the early window as a theorem, and orbit membership). `s7_g4g7_failbranch_v1.{py,out}`,
`s7_g4g7_box01_v1.out`, `s7_g4g7_closed_v1.{py,out}`, `s7_g4g7_hyp_v1.out`, `WindowTwoRunner_v4.lean`,
`WindowTwoRunner_v5.lean` (`.out`).
- **Source** (port `OrderSixSecSevenCasesN.lean`). `bhk_s7_g4_hard` constructs BHK's named meeting time
  (k ∈ {1, 3}, τ = k/(4g)) and proves its readings. `bhk_s7_named` finishes with t* = 1/(6v₁) when v₅ ≤ 5v₁, otherwise
  with a window rule.
- **What closes the 4,000 short-window sets** (to 120): v₅ ≤ 5v₁ in 3,816, closed by the spread instant 1/(6v₁)
  (`lonely_six_of_spread`; the grid instant of E23). The other 184 sit at the resonance v₅ ≈ 2v₄ with v₄ just above v₃.
  All 184 have the lap box with runner 5 on its second lap alive (v₄ ≤ 5v₁, 7v₄ ≤ 5v₅, v₅ ≤ 11v₁), lonely at
  max(1/(6v₁), 7/(6v₅)).
- **Three-way closure, without the formula for L(ρ)**:
  - (i) v₅ ≤ 5v₁: spread instant;
  - (ii) v₄ ≤ 5v₁, 7v₄ ≤ 5v₅, v₅ ≤ 11v₁: runner 5's second-lap box;
  - (iii) otherwise: `window_two`'s thresholds hold for the named window. The base threshold needs only v₄ > v₃ and
    v₅ > 5v₁. Each resonant threshold m ≥ 1 forces v₅ > 2v₄, then ¬(ii) gives v₅ ≥ 8v₁, which is what the
    threshold needs (G₇ needs v₅ ≥ 7v₁ and uses v₃ > 3v₁).

  Checked on every exceptional set to 120 (G₄: (i) 29,463, (ii) 20,280, (iii) 72,618; G₇: 14,707, 7,868, 18,047; 0
  failures).
- **Lean** (all [propext, Classical.choice, Quot.sound]):
  - `WindowTwoRunner_v4.lean`: `spread_clear`, `box01_slow`, `box01_fast`, `res_of_room`; **`g4_closed`**,
    **`g7_closed`**: real speeds 0 < v₁ < v₂ < v₃ < v₄ < v₅ with 3v₁ < v₃ (and v₃ < 4v₁ for G₄), and a meeting time
    at BHK's named point, imply a lonely instant.
  - `WindowTwoRunner_v5.lean`: **`g4_nat`**, **`g7_nat`**, the orbit-membership link. For whole-number speeds with
    v₃ − v₂ = 4g (7g), v₃ = g c₃, v₁ = g c₁, c₃ ≡ 2 and c₁ ≡ ±1 (mod 4) for G₄, c₁ ≢ 0 and c₃ ≡ 2c₁ (mod 7)
    for G₇, the meeting time k/(4g) (k/(7g)) is constructed and the closure applies.
  - Every exceptional §7 set to 120 satisfies these hypotheses (`s7_g4g7_hyp_v1.out`: 122,361 and 40,622).
- **Reading.** BHK's exceptional orbits in §7 are now closed natively and proved. The steps are the named meeting
  time (the orbit point), the window lemma, and two lap boxes: the spread box (all runners on their first lap, the
  grid instant) and runner 5's second-lap box. Every step is in framework objects, with no case tables. That every
  §7 set with a failing main route is G₄ or G₇ is BHK's Corollary 6 analysis (ported); here it is checked to 120,
  not re-derived.

**E55. "The main route fails only on G₄ and G₇" re-derived and proved for every order (2026-10-16).** Owner, of the
step E54 left to BHK: *"Lets explore that one step"*. `s7_orbit_R_v1.{py,out}`, `s7_orbit_R_v2.c`
(`s7_orbit_R_v2_400.out`), `s7_shortstep_bounds_v1.out`, `S7Orbits_v1.lean` (`.out`), `S7Orbits_v2.lean` (`.out`),
`S7Orbits_v3.lean` (`.out`).
- **One number per orbit.** At a meeting time the point (x, y) = ({kc₃/n}, {kc₁/n}) lies in BHK's P for the
  ratio ρ = v₁/v₃ iff 1/6 ≤ x ≤ 5/6 and ρ ≤ min((y − 1/6)/(x − 1/6), (5/6 − y)/(5/6 − x)): both conditions are
  upper bounds on ρ. So the orbit meets P iff ρ ≤ R(G), the best point's bound. The main route fails exactly when
  ρ > R(G), and since §7 has ρ < 1/3, only orbits with R(G) < 1/3 can fail, i.e. orbits with no point in
  P_{1/3}.
  - R predicts the meeting-time data exactly (10,357 checks, 0 mismatches).
  - Orbits off the axes up to order 400 (121,057, counting unit multiples once): exactly two have R < 1/3, G₄
    (R = 1/4, failing for v₃ < 4v₁) and G₇ (R = 5/17, failing for 17v₁ > 5v₃).
- **For every order** (the derivation):
  - n ≥ 36: the framework's `orbit_isolation_two_bhk` gives a point in BHK's box [1/6, 5/6] × [7/18, 11/18],
    which lies inside P_{1/3}, or a minimal short step (i, j), 0 ≤ i ≤ 4, |6j| < 9 + 2i, with
    2/9·i + 2/3·|j| − 2/n·i|j| < 1.
  - Both i, j nonzero except (1, ±1): that inequality forces n < 36 (largest bound from (2, ±1)).
  - (0, ±1) and (1, 0): force c₃ ≡ 0 or c₁ ≡ 0, excluded in §7 (an axis).
  - (1, ±1): the orbit contains (m, ±m); m = ⌊n/2⌋ lies in P_{1/3}.
  - (i, 0), i = 2, 3, 4: Bézout on c₁ gives an orbit point at height in [n/3, 2n/3], where P_{1/3} contains
    every x in [n/3, 2n/3]. Stepping by the (i, 0) meeting time changes x by i and keeps the height, so the walk
    lands there. Minimality is not needed.
  - n ≤ 35: a finite check.
- **Lean** (`S7Orbits_v3.lean`; `check_orbits`, `g4_misses`, `g7_misses` use no axioms; `orbit_hits_or_exc`:
  propext, Quot.sound; the rest propext, Classical.choice, Quot.sound; zero `sorry`):
  - `check_orbits`: kernel computation, every order 2 ≤ n ≤ 35;
  - `short_step_bounded`;
  - `axis_step_c3`, `axis_step_c1`, `diag_step_hits`, `walk`, `horiz_step_hits`, all on the framework's
    `meetingOrbit` via `mem_meetingOrbit_iff`;
  - **`s7_main_route`**: for every n ≥ 2, c₃, c₁ ≢ 0 (mod n), gcd(n, c₃, c₁) = 1, not G₄ or G₇ (as residues), some
    meeting time k < n has its point in P_{1/3}, in the whole-number form n ≤ 6x ≤ 5n,
    6x + 2n ≤ 18y ≤ 10n + 6x.
- **§7 natively, now**: main route by `s7_main_route` (framework's 2D global isolation plus the short-step lemmas);
  exceptional orbits by `g4_nat`, `g7_nat` (E54). Not yet composed into one theorem from speeds to a lonely
  instant: the step "point in P ⇒ full 3-gap that is a 123-gap at that meeting time ⇒ lonely" exists in the
  port (`lonely_of_meeting`, `bhk_s7_witness`) and in `window_two_uniform`, but is not joined here.

## E56 — §7 joined: whole-number speeds to a lonely instant (`s7_lonely`)

**Map:** BHK §7 (meeting times `k/D`, `D = v₃ − v₂`), closing the composition gap stated at the end of E55.

**Artifact:** `S7Complete_v1.lean` (bodies of `WindowTwoRunner_v5` and `S7Orbits_v3` under one header, plus two
new declarations), output `S7Complete_v1.out`: 0 errors, no `sorry`/`native_decide`/`admit`.
`#print axioms` for `main_route_lonely`, `s7_main_route`, `g4_nat`, `g7_nat`, `s7_lonely`:
`[propext, Classical.choice, Quot.sound]` each. [PROVED]

- `main_route_lonely` (reals): at an instant `t` where runners 2 and 3 share the reading `x ∈ [1/6, 5/6]` and
  runner 1 reads `y` with `1/6 ≤ y − v₁(x−1/6)/v₃` and `y + v₁(5/6−x)/v₃ ≤ 5/6`, some instant is lonely for all
  five. Proof: `window_two_uniform` on the window of length `2/(3v₃)` opened at `t − (x−1/6)/v₃`, runners 1–3
  kept clear across it by `clear_shift`.
- `s7_lonely` (whole numbers): `0 < v₁ < v₂ < v₃ < v₄ < v₅`, `3v₁ < v₃`, `D ∤ v₁`, `D ∤ v₃` ⇒ `∃ s, Lonely5`.
  With `g = gcd(D, v₃, v₁)`, `n = D/g`, `c₃ = v₃/g`, `c₁ = v₁/g` (coprimality of `n, c₃, c₁` proved from `g`):
  - off `G₄`/`G₇`: `s7_main_route` gives `k < n` with `(c₃k mod n, c₁k mod n) ∈ P_{1/3}`; at `t = k/D` the
    integer inequalities become the two real ones above (using `3v₁ < v₃`), and `main_route_lonely` closes;
  - `G₄` with `v₃ < 4v₁`: `g4_nat`; `G₄` with `v₃ ≥ 4v₁`: the orbit point `(1/2, 1/4)` (`k = 1` or `3`) passes
    the same test, since `v₁/(3v₃) ≤ 1/12`, so the main route closes it too;
  - `G₇`: `g7_nat`.
- Consequence: §7 is closed natively end to end in Lean on whole-number speeds. What it does not include: the
  reduction of BHK's real-speed statement to these hypotheses (the §7 case split itself), which lives in the
  BHK port, not in this file.

## E57 — Does the cascade split the sets the way BHK do? Orbit shape and rate against the walk (2026-10-16)

**Map:** BHK's dispatch `lonely6_of_lt` (§8: v₃ ≤ 3v₁; §5: D ∣ v₁; §6: D ∣ v₃; §7: otherwise), reread as the shape of
the meeting-time orbit ⟨(c₃, c₁)⟩ ⊂ (ℤ/n)² (axis1 = n ∣ c₁, axis3 = n ∣ c₃, open, G₄, G₇) plus one rate (v₃ ≤ 3v₁).
Owner: *"Ok lets check it"* (after E56). Observation only.

**Artifacts:** `six_orbit_shape_v1.{py,out}`, `six_orbit_shape_v2.{py,out}`; primitive SixResidual, max ≤ 40 (17,135
sets, from `six_cascade_observe_v1.tsv`), exact Fractions.

- The relabelling is exact: orbit shape plus rate reproduces BHK's labels with 0 mismatches. This holds by definition
  (n ∣ c₁ ⇔ D ∣ v₁), so it is a restatement and not a finding.
- **The cascade does not visit BHK's instants.** Its final instant is a 2–3 meeting time (a multiple of 1/D) in
  12 of 17,135 sets. In all 12 the cascade makes no move: 1/(6v₁) is itself a multiple of 1/D
  ((3,12,30,·,·) with D = 18; (5,6,36,·,·) with D = 30). The orbit shape describes BHK's instant family k/D. On this
  range the cascade does not use that family, so the orbit-shape split is a split of BHK's instants and not of the walk.
- **The rate: the cascade's exact line is 5v₁, not 3v₁.** First setter in {2, 3} occurs only when v₃ ≥ 5v₁
  (0 exceptions across all bands). This is forced: at 1/(6v₁) a runner with v₁ < v < 5v₁ reads v/(6v₁) ∈ (1/6, 5/6),
  so it is clear (`first_move`, E4). Below 3v₁ and in (3v₁, 5v₁) the first move is the same kind (setter 4 or 5, or
  none). The line 3v₁ shows only in later setters: some setter in {2, 3} in 6 of 3,716 sets with v₃ ≤ 3v₁
  (the E4 exceptions) against 1,827 of 5,328 with 3v₁ < v₃ < 5v₁. So 3v₁ is sharp in counts but not exact for the walk.
- **One trace of orbit shape in the walk (counts, not understood):** final flank = runner 3 in 15 of 2,444 axis1 sets
  (D ∣ v₁), 176 of 1,843 axis3, 3,257 of 8,724 open, 91 of 295 G₄, 37 of 113 G₇. Why the walk rarely ends at runner 3
  when runner 1 is at a whole lap at 1/D is not explained.
- **Consequence:** on this range, BHK's case split is a property of the instants BHK chose to inspect, and the cascade
  does not inspect them. Reading the split as orbit shape is correct for BHK's route but is not a native split of the
  cascade. A native division of the order-six sets, if one exists, has to come from the walk's own objects (the 5v₁
  start line, setters, final flank), not from D.

## E58 — Native §7 wired into the order-six proof (2026-10-16)

Owner: *"Ok yes do that now"*. `LonelyRunner/LRC/Spec/OrderSixSecSevenNativeN.lean` (namespace `LRC.S7Native`) carries
`S7Complete_v1.lean` into the tree, plus `lonely_7_native`: the hypotheses and conclusion of `S7.lonely_7`, proved from
`s7_lonely` by adding whole laps to make the instant positive (readings unchanged). `lonely6_of_lt` (`OrderSixWholeN.lean`)
now calls `lonely_7_native`. `S7.lonely_7` is kept and still compiles. `S7Native_wiring_v1.out`: build of the order 3–7
targets (8,332 jobs), axioms `[propext, Classical.choice, Quot.sound]` for `lonely_7_native`, `lonely6_of_lt`,
`lonelyRunnerAtN_six`, `lonelyRunnerAtN_seven`; the dispatch's proof term references `lonely_7_native` and not
`S7.lonely_7`. [PROVED] Nested repo commit in `LonelyRunner/`; not pushed.
- **Consequence:** the order-six proof of record now takes §7 (and BHK §2) by the native route. §5, §6, §8 and the
  dispatch remain BHK's form.

## E59 — Prior work: three citation-verifier checks (2026-10-16)

Owner: *"Run citation-verifier on the three prior-work questions"*. Three isolated `citation-verifier` runs; key quotes
spot-checked against the BHK text (`bhk_2001.pdf` via pdftotext) and repository dates via `gh api`.

1. **BHK §2 and §7 against `s7_lonely`.** SUPPORTS-WITH-CAVEAT. §2 (v₁ ≤ 1/4 normalised, i.e. v₃ ≥ 4v₁; {t₀} ≠ 0,
   {v₁t₀} ≠ 0, i.e. D ∤ v₃, D ∤ v₁) lies inside the hypotheses. §7's heading reads 3 ≤ x₁ < 4, its overview 1/4 < v₁ < 1/3
   (strict); the point v₃ = 3v₁ (e.g. 3, 5, 9, D = 4) is outside `h13` and goes to §8 in both BHK and `lonely6_of_lt`,
   so the proof has no gap. Correct wording: "§2 and §7 for 3 < x₁ < 4". BHK give an uncovered interval; the Lean
   statement gives an instant. §2 has no tables; §7 uses Tables 9, 10 and reuses §2 for (2,0), (1,±1), (2,±2).
2. **Real-to-integer reduction.** WEAKER. BHK 2001 Lemma 8 (text l.633; Kronecker l.658) already has induction via
   order n − 1, the proportional / non-proportional split, the rational merge to ≤ n − 2 readings and the margin
   1/n < δ < 1/(n − 1). Henze–Malikiosis 2017 Lemma 5.3 removes the n − 1 dependence. Both return to a real time by
   Kronecker. Our `SteppingN.exists_step_near` is a pigeonhole (Dirichlet-returns) proof of the same Kronecker
   statement: measure-free, not Kronecker-free, and classical. The reduction is not a contribution; cite BHK Lemma 8
   and Henze–Malikiosis. Do not cite Wills or Cusick (unread; BHK dispute the Wills attribution).
3. **Prior formalisations.** DOES-NOT-SUPPORT a priority claim. Public Lean 4 repositories (dates confirmed by `gh api`):
   `chlciallo/lean4-lonely-runner` (created 2026-09-17, release v1.0.0 2026-09-20, README: n = 3, 5, 6, 7 real
   speeds, n = 4 integer/rational, via BHK Lemma 8, Barajas–Serra, Renault; Zenodo 10.5281/zenodo.22851977) and
   `Cheeks2184/lonely-runner-formalization` (n = 4 real speeds, 2026-09-06). Neither built here; scope is the authors'
   README. Our `mia-research/lonely-runner-lean` is private (created 2026-09-24). Computer proofs for n ≥ 8
   (Rosenfeld; Trakulthongchai; Sungkawichai–Trakulthongchai; Allikvere) cite C++ or other code, no proof assistant
   seen.
- **Consequence:** a paper cannot claim the reduction or the first formalisation of orders 3–7. What remains
  candidate-new and unchecked against literature: the native §7 route (global isolation in two dimensions; exceptional
  orbits only G₄, G₇ at every order; G₄/G₇ closed by explicit boxes; a sharper two-runner window lemma than BHK
  Lemma 4), and the order-five core's framework mechanisms. Owed: a citation check on the sharpened Lemma 4 and on
  whether the G₄/G₇-only statement or the box closures appear after 2001.

## E60 — The two prior Lean formalisations read for what helps us (2026-10-16)

Owner: *"We need to look at their work to see if what might help us move any of our investigations forward. Also the
idea of the paper was we had a reformation of the proof under one framework"*. Shallow clones (read only, not built) in
the session scratchpad: `chlciallo/lean4-lonely-runner` at `e790d70` (63 files, 53,219 lines), `Cheeks2184/
lonely-runner-formalization` at `3459046` (231 files). Statements below are from their READMEs and module docstrings.

**Chen (n = 3–7).** One classical proof per order, no shared framework:
- n = 3: Wills-style covering. n = 4 integer: Renault 2004 Appendix A (extremal safe time on a finite set of
  quarter-boundary times, re-entry by a half shift); n = 4 real is not claimed (rational only).
- n = 5 integer: Barajas–Serra prime filtering at p = 5 (base-5 digits, multipliers 1 + k·5^{m−j}).
- **n = 6 integer: Renault 2004** (*View-obstruction: a shorter proof for 6 lonely runners*, Discrete Math. 287,
  93–101), not BHK. Dispatch by residues: number of multiples of 3 (3 → Lemma 2.3, 2 → Prop 3.1, 1 → the multiple
  of 6, then the count of ±2-residue speeds → Props 5.4, 6.6, 4.1). Lemma 2.1 caps multiples of 2 or 3 at three
  by solving the subset at order five and shifting by 1/l. Contradictions come from improving moves
  s = λ·τ + α/6 (scale λ ≤ 5, sixth shift α) applied to an extremal time.
- n = 7 integer: Barajas–Serra 2008. Real speeds n = 5, 6, 7: BHK Lemma 8, Kronecker by ergodicity and Fourier
  (`flow_orbit_dense`); a pigeonhole simultaneous-Dirichlet module also present.

**Cheeks (n = 4 real, and a general-n programme).** `fourRunners` (2026-09-06) via BHK Lemma 8 and an orbit-closure
helper (Kronecker by characters / averaging). Also: a finite height cutoff choose(N,2)^(N−2) (Tao-type, integer to
bounded integer); "mixed margins" (fastest runner at 1/(N−1), others at 1/N); a deletion-gcd lemma (a deletion gcd D
above the full gcd G gives a time with all norms ≥ 1/(N−1); orbit size D/G); the AP family (a, 2a, 3a) witnessed at
1/(4a). Unrestricted LRC open in their own words.

**What this means for our lines of work:**
- **Renault's order six is a residue proof in the framework's objects.** The dispatch is ℤ/6 = ℤ/2 × ℤ/3 (E43); the
  moves are a change of scale λ and a shift by α/6, the two mechanisms of our order-five core (`OrderFiveResidualN`:
  change of scale, shift budget); Lemma 2.1 is the divisible-flank shift (E45: a shift by 1/l leaves multiples of l
  fixed) with order five inside order six. BHK's geometry (parallelograms, 45-blocks, covering lengths) is what the
  native work has been fighting in §5, §6, §8. Renault's route is a candidate order-six core with the same shape as
  order five. Not yet checked: Renault's text (not on disk; source-first rule applies before any comparison), and
  whether its extremal-time step can be replaced by the cascade (the cascade constructs the instant; Renault takes a
  maximiser over a finite candidate set).
- **Real speeds:** both use Kronecker by analysis (ergodic/Fourier, characters); ours is pigeonhole only
  (`SteppingN`). A difference in proof, not in the result (E59).
- **Cheeks' deletion-gcd and mixed-margin results** sit next to our global isolation (instants p/n, orbit size) and
  the AP-as-global-isolation observation (E49–E50). Order eight is a separate project; recorded as a comparison only.
- **The paper.** Neither repository presents one framework: Chen uses five different classical arguments for five
  orders, Cheeks targets n = 4 and general n. A paper whose claim is *one framework reformulating orders 3–7* is not
  pre-empted by either. It must cite both as prior Lean proofs, and cite BHK Lemma 8 for the reduction (E59).

## E61 — Renault 2004: source not yet obtained; statement shapes from Chen's Lean (2026-10-16)

Owner: *"locate Renault 2004 (Discrete Math 287, 93-101), read its argument first, then compare"*. Observation only.
- **Source:** DOI 10.1016/j.disc.2004.06.008, Elsevier open archive (Crossref licence: open access from 2013-08-22;
  OpenAlex `is_oa` true). Every automated route failed: ScienceDirect returned 403 to curl and an error page in the
  built-in browser; Elsevier API needs a key; the Dauphine repository (basepub 123456789/6201) is unreachable, and its
  Wayback snapshot has no file link; CiteSeerX returned 404/429; web searches found citations only. **The paper has
  not been read.** By the source-first rule, the comparison waits for it.
- **Secondary, kernel-checked statements (Chen, `Research07/LRC6`, not Renault's wording):** `hfail D` = every time
  has an unsafe runner. Dispatch by the number of multiples of 3 (3: `lemma2_3`; 2: `prop3_1`; 1: the multiple of 6,
  then by the ±2 residues). `prop5_4` and `prop6_6`: a runner `v₁ ≡ 0 (mod 6)`, four guards with residues ±1 mod 6
  (or one ±2), a seed time where the four guards are lonely at **1/5** (order five), and the hypothesis that every
  guard-safe time keeps `v₁` within 1/6 of a lap point give a contradiction. `prop4_1`: residues (0, ±2, ±2, ±1, ±1).
- **Shape match (secondary, to be checked against the paper):** the hard case is one runner divisible by the order
  with the rest solved one order down, which is the shape of our order-five residual (`OrderFiveResidualN`: exactly one
  disparity divisible by 5). The residues used are units and zero divisors of ℤ/6 (E45). The moves are a change of
  scale λ ≤ 5 and sixth shifts α/6 applied to an extremal guard-safe time (`Driver.lean`).

## E62 — Renault's order six (from Chen's Lean) against our order-five core and the cascade (2026-10-16)

Owner: *"Give me the link and I will get it while you use chen's lean"*. **Grade of every Renault statement here:
[SECONDARY — Chen's Lean `Research07/LRC6` docstrings and theorem statements; Renault 2004 not yet read].** Observation
only. Artifacts: `six_renault_classes_v1.{py,out}` (primitive SixResidual, max ≤ 40, 17,135 sets, exact Fractions).

**Renault's argument as Chen formalised it.** Under `hfail` (no lonely time):
- §2: Lemma 2.1, every l ∈ {2,…,6} divides some speed (at t = 1/l a non-multiple of l is safe); with gcd 1, at most
  three multiples of 2 and of 3 (solve four of them at order five, margin 1/5, then shift by 1/l, which leaves the
  multiples fixed). Lemma 2.2: each speed i has some j with i < 5j. Lemma 2.3: three multiples of 3 → shift by thirds;
  each non-multiple is bad for at most one of the three shifts. Claim 2.4: every x ∈ (1/6, 5/6) leaves the band under
  some λ ∈ {2,…,5}.
- Dispatch by the number of multiples of 3: 2 → Prop 3.1 (third shifts; extremal time on a discrete set; 6w divides a
  multiple of 3; finish at 1/(6v₁)); 1 → that one is the multiple of 6, the anchor, and the four others are guards with
  residues ±1 or ±2 mod 6: no ±2 → Prop 5.4, one → Prop 6.6, two → Prop 4.1.
- Props 5.4, 6.6, 4.1: seed = the four guards lonely at 1/5 (order five); take the guard-safe time maximising the
  anchor's distance from a lap point; a move s = λ·t + α/6 (λ ≤ 5) leaves the anchor's reading multiplied by λ and
  shifts each guard by its residue times α/6. Lemmas 5.1, 6.1, 6.4 (interval-covering over three readings) give a (λ, α)
  keeping every guard safe, which improves the anchor: contradiction.

**Against our order-five core (`OrderFiveN`, `OrderFiveResidualN`).**
| Renault, order six | Ours, order five |
|---|---|
| Lemma 2.1 (≥ 1): t = 1/l, non-multiples safe | M = 0: the instant 1/5 is lonely (R6) |
| Lemma 2.1 (≤ 3), Lemma 2.3: multiples fixed under 1/l or 1/3 shifts, each non-multiple bad for ≤ 1 shift | M ≥ 2: descent with cost max(2, gcd(e,5)) per non-multiple, total ≤ 4 < 5 |
| the single multiple of 6 (anchor), four guards solved one order down | the single multiple e of 5, not the largest (the residual) |
| move α/6: anchor fixed, guards shift by residue·α/6 | `exists_fifth_shift`: e fixed, others shift by k/5, budget |
| move λ: anchor scaled (Claim 2.4: λ ≤ 5 pushes it out) | `exists_time_coprime`: change of scale m until e is clear |
| starting time: extremal (maximiser over a finite candidate set) | starting time: a lap point α/F of the fastest runner, α ≡ v₃⁻¹ (units of ℤ/F) |
Same objects (the divisible runner, shifts by 1/n that fix it, scalings that move it, the shift budget), one difference:
Renault picks the starting time by maximisation, ours by a unit of ℤ/F.

**Our SixResidual already contains part of Renault §2.** `six_residual_v1.py` (field by field from `OrderSixN.SixResidual`)
requires a multiple of 4, of 5 and of 6 (Lemma 2.1's ≥ 1 direction for l = 4, 5, 6), and every V ≤ 5s for some
other s (Lemma 2.2, non-strict). It does not impose the ≤ 3 directions: 974 sets have four multiples of 3 and 1,928 have
four even speeds.

**Against the cascade (counts, not rules).** Classes on SixResidual: P3.1 8,709; L2.3 2,568; P4.1 1,853; four evens
1,928; P6.6 998; four multiples of 3 974; P5.4 105.
- The cascade's instant is not Renault's seed: the four guards are clear at 1/5 at T in 22–422 sets per class (≤ 6%);
  at some T + a/6 in 33–50%.
- Lonely instants come in sixth-shift families: T + a/6 (a = 1…5) is also lonely in 77% of P3.1, 76% of P4.1, 59% of
  P6.6, 44% of P5.4. Scalings λT (λ = 2…5) are lonely in 61–69%.
- P5.4 (all guards ±1): final flank a unit in 100 of 105; the other classes mix.
- **Consequence:** Renault's order six has the order-five mechanism one order up (divisible anchor, shifts fixing it,
  scaling, budget). The cascade's instants do not follow Renault's seed-and-move order, as they did not follow BHK's
  (E57). Not checked: Renault's own text; whether a unit of ℤ/v₅-style starting time can replace the extremal time in
  Props 5.4/6.6/4.1 (that is the step that would make order six run on the order-five core).

## E63 — Correction to E62: placed back in this session's purpose (2026-10-16)

Owner: *"That answers the prompt but not the context of this session"*. E62's consequence line ("a candidate order-six
core"; "the open step is the starting time … would make order six run on the order-five core") has the same fault as
E27: it takes a classical proof's shape (Renault's) as the target and asks what framework parts fill it. Placed back in
the session's two tracks:
- **Reformulated track (and the one-framework paper):** Renault is a second classical order-six proof to carry into
  the framework, alongside BHK. Its objects (residues mod 6, shifts fixing multiples, scaling, an order-five
  instance inside) are ones the framework already uses at order five, so the carried-over proof would share
  machinery with order five. That is a choice about the reformulated track, and it is the owner's.
- **Native track:** Renault does not answer the native question. It argues by contradiction from a maximising time and
  never names an instant, while the native question is what forces the cascade's isolation. What E62 does carry
  for the native track: Renault's dispatch is by the zero-divisor content of ℤ/6 (multiples of 2, 3, 6), the
  structure seen independently in E43 (ℤ/6 = ℤ/2 × ℤ/3 alignment) and E45–E46 (isolation events are the units; blocking
  splits along units and zero divisors). The cascade-side counts (sixth-shift and scaling families of lonely instants)
  are observations of the cascade, not of Renault.

## E64 — The units / zero-divisor structure of ℤ/6 along the cascade's walk (2026-10-16)

Owner: *"Native track: observe what the units / zero-divisor structure of Z/6 (E43-E46, and Renault's dispatch) does in
the cascade on SixResidual. Observation only, no Renault proof shape."* `z6_walk_v1.{py,out}`, `z6_walk_v2.{py,out}`;
primitive SixResidual, max ≤ 40 (17,135 sets), exact Fractions. Classes by d mod 6: U (1, 5), E (2, 4), T (3), M (0).
Instrument: at every walk instant t_i (start 1/(6v₁), each move, the lonely end T), the six sixth shifts t_i + u/6.

- **The action.** A sixth shift u moves runner d by d·u/6, so d is unmoved exactly when 6 ∣ d·u (checked 428,375 of
  428,375): M by every u, E by u = 3, T by u = 2, 4, U by none. The zero divisors are the runners some nonzero shift
  leaves in place, and the stabilisers are the subgroups {0, 3} (for E) and {0, 2, 4} (for T). Renault's dispatch
  coordinates (multiples of 2, of 3) are the sizes of these two fixed sets.
- **Lonely instants spread along the stabiliser of the zero divisors** [C]. Share of sets with T + u/6 also lonely,
  by class counts: three E runners → u = 3 lonely in 0.65–0.69 of sets (u = 1, 2, 4, 5: 0.08–0.32); one E → u = 3 in
  0.26–0.30. Two T → u = 2, 4 in 0.36–0.65; no T → 0.10–0.14. The shift that moves fewest runners is the one most often
  lonely; this is what the identity above predicts, with the moved runners' readings deciding.
- **E45's clean split does not appear in the walk.** Of 14,984 walk frames with no lonely sixth shift, events (u = 1, 5)
  were blocked only by units and non-events only by zero divisors in 23. Events are blocked by M (which blocks every
  shift when blocked at all), by E and T cosets (E46), and by units, in every combination.
- **Setters by class, per runner present:** U 0.289, E 0.306, T 0.243, M 0.338 (in the way: 0.394, 0.413, 0.309, 0.445).
  Class mod 6 does not pick the setter beyond a mild excess for M and deficit for T.
- **Where runners sit when the walk stops**, in twelfths: 0.38–0.46 of each class in [1/6, 1/4), the rest spread,
  almost none in [5/6, 11/12). The same profile for all four classes.
- **Earlier frames already hold a lonely instant** in 7,538 of 17,135 sets: some t_i + u/6 with i < end is lonely (it
  is later in time than T, since T is the first lonely instant).
- **Reading** [observation]. In the cascade, ℤ/6's structure shows as the stabilisers of the zero divisors: once the
  walk stops, the shifts that leave the zero divisors in place carry the isolation to further instants, in proportion
  to how many runners they fix. It does not show in who sets moves, in where the runners sit at T, or as E45's
  unit / zero-divisor split of blocking. The cascade's own stopping is not explained by this structure: what it
  describes is how one isolation propagates to its sixth-shift family, not why the first one exists.

## E65 — Slots and flanks from the ideal; is residue isolation a deformation of the AP? (2026-10-16)

Owner: *"I wonder if even trying to use divisors and class is importing too much. From the global isolation ideal, get
slots, from its neighbours we get flanks … shouldn't we really think in those terms?"* and *"Ok lets really explore this,
spin up agents … Is the residue isolation deformation of the AP"*. Two general-purpose agents, observation only, exact
Fractions; their artifacts checked here (type counts at T recomputed independently, same top three; label identity below
recomputed, 32,000 of 32,000). Coordinates: slot of a runner = round(n·reading); entry / exit flank = least / greatest
reading; no residue classes.

**A. AP (1,2,3,4,5) → each SixResidual set, straight line** (`slot_deform_v1.{py,out}`, all 17,135 sets; events solved
exactly in s; controls 649,467 of 649,467 direct checks, 1,298,934 of 1,298,934 between-root checks, cascade T
17,135 of 17,135).
- Followed isolation = one lap vector m held while its interval I_m = [max (m_i+1/6)/v_i, min (m_i+5/6)/v_i] is
  non-empty (the lap box); instant = its left endpoint.
- **Forced first move:** the AP's lonely set is the point 1/6, and every SixResidual set has d₅ > 5d₁ (part of its
  definition), so the lap-0 isolation dies at s = 0 on every path and the isolation restarts at the mirror 5/6 with
  laps (0,1,2,3,4), slots reversed [5,4,3,2,1]. This is the known face d₅ = 5d₁ (`grid_tight_pairs`), not new.
- Types at the cascade instant T: 2,794 distinct; 13 at the ideal type; 148 one runner per slot (30 orderings);
  runners off their ideal slot: 3 in 4,910 sets, 4 in 6,428. Entry flank rank 4 or 5 in 9,205; exit flank rank 1
  in 13.
- Along the paths: after the forced death, 1,105 paths keep one lap vector to the end; others die 1–11 more times.
  Events: slot change 221,514, shared slot on/off 104,114 / 89,123, entry / exit handover 27,240 / 26,910, deaths
  49,054. 31,118 distinct type transitions. The followed isolation ends at the cascade's own type in 14,210 of 17,135.

**B. Residue isolation as AP plus windings, orders 3–7** (`residue_fold_v1.{py,out}`; d_i = a_i + n·m_i, a the AP runner
with the same slot at p/n; 72,522 (arrangement, p) pairs; controls all agree, listed in the .out; one mislabelled
histogram bin noted by the agent: "bin 0" is [0, 1/10), exact zeros are on the separate line).
- **The lap vector is the label of an isolation, and it is constant on a continuous family.** At a lonely (v, t) each
  unwrapped reading v_i·t sits in one block [k_i + 1/n, k_i + 1 − 1/n]; blocks are 2/n apart, so different K are
  disjoint closed sets. For fixed K the condition is (n k_i + 1) v_j ≤ (n k_j + n − 1) v_i for all i ≠ j: homogeneous
  linear in the speeds, so each K-cell is a polyhedral cone in speed space (the lap box, `lap_box_lonely`).
- **The residue isolation sits on a different sheet.** At (d, p/n) the label is K₀ + p·m, with K₀ = ⌊a_i p/n⌋ the AP's
  label (identity recomputed: 32,000 of 32,000). Any continuous deformation keeping a lonely instant keeps K, along
  any path, so the AP's isolation at p/n never deforms into the residue arrangement's isolation at p/n
  (0 of 72,522 on the straight line; the one-winding-at-a-time paths reach nothing more, which the agent shows is forced
  by the label).
- What the AP's label does reach: the straight line keeps the K₀-cell to s = 1 in 179 / 916 / 1,795 / 6,204 / 1,614
  pairs (n = 3..7), almost always at an instant off the unit grid; it dies before s = 1 in the rest, at s = 0 exactly
  in 272 / 1,893 / 7,298 / 13,716 / 11,316 (the AP's lonely set at p/n is one point). Asymmetric in p: at n = 6, p = 1
  reaches in 6,203, p = 5 in 1.
- Worked: (1,2,3,4,11) and (1,2,3,4,35) at n = 6, p = 5 die at the same point t = 19/24 with the same slots
  (5,4,2,1,5), at s = 7/38 and 7/190: five windings give the same end picture five times sooner in s.
- **Reading** [observation]. In the ideal's own coordinates, an isolation is a lap vector K, and the arrangements with
  that isolation form a cone C_K in speed space. The AP is a tight point of C_{K₀}; a residue isolation is the same slot
  picture on the sheet C_{K₀+p·m}, reached from the AP only through deaths. "Folding" is the passage between sheets:
  each extra winding adds p laps to that runner's label. The cascade's moves and the deformation deaths are both changes
  of K. Not yet observed: how the cones C_K meet (which K-cells share faces, and whether the type transitions in A are
  the face crossings); the statement "the cones cover the positive orthant" is existence itself, i.e. the covering
  framing the owner set aside in E2.

## E66 — The "scatter" as folding, and deaths as relocation (2026-10-16)

Owner: *"Are we seeing a scatter (unlikely) we are seeing how the origami and folding of the ideal is working"*; and of
E65's deaths, *"Or is relocated to the next global isolation incident?"*. Observation only.

**Folding** (`fold_grid_v1.{py,out}`, `fold_lift_v1.{py,out}`; primitive SixResidual ≤ 40).
- Write the cascade instant as T = c/q in lowest terms. Every reading is (d·c mod q)/q, with c a unit of ℤ/q, and
  q = 6b/g, c = (6k+1)/g, where b is the final flank, k its opening and g = gcd(6k+1, b) (17,135 of 17,135 each). This
  is an identity for rational instants; its content is that the cascade chooses the modulus and the fold through its
  flank and opening.
- So each isolation is the ideal of ℤ/q (one slot per residue) folded by multiplication by the unit c, with the five
  runners at their residues d mod q, all landing in the middle band. Global isolation is the case q = n. Read at
  modulus 6 the pictures look scattered (E65: 2,794 types); at their own modulus they are unit foldings. Readings
  pairwise distinct in 15,623 of 17,135 (in the others two runners are congruent mod q).
- c mod 6, i.e. which order-6 ideal event the fold lies over: 1 in 16,870, 5 in 265. Largely set by the instrument:
  cascade instants are entry openings (6k+1)/(6b), so c ≡ g⁻¹ (mod 6).

**Relocation** (`death_relocate_v1.{py,out}`; every 4th path of `slot_deform_v1`, 7,988 deaths after s = 0).
- At every death, the next lonely instant after the dying one already has its lap vector alive at the death's s:
  7,988 of 7,988. The isolation can be carried forward to the next isolation with no gap. (Same as E28's "no death
  without a takeover", there on axis paths; here on the AP → set lines.)
- slot_deform_v1's restart rule (earliest lonely instant) jumped back to an earlier instant in 4,552 of these deaths;
  so E65's "restart in another lap pattern" was the instrument's choice, not the geometry's.
- Lap change to the next isolation: commonest +1 on the fastest runner (1,098), then +1 on the two fastest (791),
  three fastest (748), four (555).
- **Reading** [observation]. On these paths a death is a relocation forward to the next isolation, which is present at
  the moment of death; in fold terms the next isolation is the next lift (next unit fold at its own modulus), not a
  return to the order-6 ideal's other event. Not established: why the next isolation is always already alive (E28 and
  summary v6 §4 note this is the handover question, equivalent to existence).

## E67 — "Only 15 types of result": search, and relocation kinds by flank roles (2026-10-16)

Owner: *"When we were mapping the cascade results against types of arrangement we only saw (from memory) 15 different
types of result. Maybe this is the native classes, arrangements of speed only deform the isolation in these types of
manners"*.
- **Search.** No 15-type result found in this log, summary v6, this session's transcript or `experiments/`. Nearest:
  E64's 15 groups (counts of multiples of 3 and of 2), which are input classes fixed by construction; and order-8
  E398 (`docs/n8/RUNNING_LOG_order8_v1.md`, "the .out lists 15 types" of walker (q, p mod 8)), a separate project.
- **Test of the idea at order 6** (`relocation_kinds_v1.{py,out}`; every 4th AP → SixResidual path, 7,812 deaths with
  single flanks, 176 ties skipped). A relocation described only by roles (I = dying entry flank, J = dying exit flank,
  O = others; which is faster; the new entry and exit flank's roles; which roles gain laps and by how much): 425
  distinct kinds; the top 10 cover 0.49, the top 40 cover 0.75. Commonest (1,405, 0.18): J faster, J gains one lap and
  becomes the new entry flank (the exit runner wraps once and re-enters). Without lap gains the role description has
  at most 18 values by construction, so a short list there would not be evidence.
- **Reading** [observation]. At this description, relocations do not reduce to about 15 kinds. Owed: the source of the
  owner's 15, to test the same description.

## E68 — Deaths as knots: displacement along a chain (2026-10-16)

Owner: *"Its not a handover but displacement. by tying a knot to remove the isolation point you push it along to the
next isolation point because the knot in one place is an opening in an other. To have two knots you will need to break
the conjecture by have the same speed"*. Observation only. `knot_displace_v1.{py,out}`, `knot_chain_v1.{py,out}`;
every 4th AP → SixResidual path, 7,812 deaths with single flanks (176 tied skipped); speeds pairwise distinct at every
death (7,812).
- **The knot.** The dying box m is one point: runner I reads exactly 1/6 (entry flank) and J exactly 5/6 (exit flank),
  (6m_I+1) v_J = (6m_J+5) v_I. Its two sides: forward, J re-enters on its next lap (box m + e_J); backward, I steps back
  to its previous exit (box m − e_I).
- **One step.** m + e_J alive at the death: 1,711 (0.22); m − e_I alive: 1,187; both dead: 5,073 (0.65). Within
  m + e_J the pair (I, J) itself holds in 6,687. Where the forward side is closed, the failing pair is (J, O): J's new
  entry falls after another runner O's exit — a second knot, with all speeds distinct.
- **The chain.** Push forward: from m + e_J, while a pair (i, j) has i entering after j exits, give j one more lap
  (each step a further knot; this is the cascade's move restarted at the dying instant). Further knots per death:
  0: 1,711; 1: 2,061; 2: 1,592; 3: 1,210; 4: 620; 5: 388; 6–10: 230. Every chain ended (7,812 of 7,812), at the next
  isolation's lap vector N in 7,799 (13 differ, where several runners took a lap in one round).
- **Reading** [observation]. On these paths a death is a displacement: the knot that closes the isolation opens J's
  next lap, and when that opening is itself knotted the push continues, knot by knot, to the next isolation. The
  claim "a second knot needs equal speeds" does not hold for the one-step opening (second knots with distinct speeds in
  6,101 deaths); what held is that the chain of knots always ends. Why it always ends is the cascade's termination at
  order six.

## E69 — Does the runner count bound the knots? (2026-10-16)

Owner: *"the more you try and tie a knot to prevent isolation it pushes it along till at some point you run out ability
to maintain a knot … It can't go on for ever as you only have finite runners"*. Observation only.
`knot_budget_v1.{py,out}`; the 7,812 deaths of E68, forward chain rule as there.
- Knots held by one runner in a single push: 1 in 4,563 deaths, 2 in 1,697, 3 in 1,184, 4 in 296, 5 in 64, 6 in 7,
  7 in 1. Total knots per push 1 to 19. Runners holding more than one knot are mostly the fastest: (rank 5, 2 knots)
  1,686, (4, 2) 1,478, (5, 3) 1,166. Example: (1,2,5,15,24) at s = 12/19, extra laps (0,0,1,2,3) — the faster the
  runner, the more knots it holds, in proportion to how far in time the push travels.
- **Reading** [observation]. A runner can re-tie: the number of knots is not capped by the number of runners. What
  finiteness gives exactly: at rational speeds the motion is periodic, a period holds finitely many openings, and the
  push only moves forward, so it either ends or passes a whole period and then repeats for ever. "It cannot go on for
  ever" is the exclusion of that endless periodic loop, and that exclusion is the existence statement itself
  (`lonely_iff_run_ends`). The runner count makes the dichotomy; what rules out the loop is still to be found.

## E70 — "More isolation points than runners can cover": the count, exactly (2026-10-16)

Owner: *"There are more possible isolation points than runners can possibly cover"*. Observation only.
`cover_count_v1.{py,out}`; primitive SixResidual ≤ 40. Isolation points: each flank b's b openings (6k+1)/(6b) in one
period; runner d blocks opening k iff d(6k+1) mod 6b lies outside [b, 5b].
- By count the runners can cover: the sum of the four other runners' block counts is at least b at 80,748 of 85,675
  flanks; the ratio sum/b is mostly 1.2–1.4 (each runner blocks about a third of a flank's openings, four runners about
  4/3).
- They do not cover: at 64,953 of those 80,748 flanks an opening is still free, because blocks coincide (example
  (1,2,3,5,12), flank 12: blocks 4, 4, 3, 4, sum 15, union 10, two openings free). 15,795 flanks are fully covered
  (dead). Every set has some flank with a free opening (17,135 of 17,135), as existence requires.
- **Reading** [observation]. The count of isolation points against runners does not exceed what the runners could block;
  at order six the runners have about a third more blocks than a flank has openings. What leaves openings free is that
  blocks fall on the same openings. A forcing argument along this line needs a reason the blocks must coincide (E43's
  alignment is one such description at divisible flanks). This is the covering framing E2 set aside; the owner raised it
  here.

## E71 — Correction to E70: counting the global-isolation opportunities, grid by grid (2026-10-16)

Owner: *"What are you talking about global isolation has multiple instances and deformation (like residue)
opportunities"*. E70 counted one flank's openings in one period. Those are the fine opportunities, where each runner
blocks about a third. The owner's opportunities are the unit-grid instants c/q (gcd(c, q) = 1), the global-isolation
instances and their residue foldings (E66: every lonely instant is one). At c/q runner d reads (d c mod q)/q.
Observation only. `grid_opportunities_v1.{py,out}`, `_v2`, `_v3`.
- **q* = the least q with a lonely unit instant.** Exhaustive, every primitive 5-set: [1, 40] (641,166 sets) max q* 27,
  at (10,13,23,33,36); [1, 60] (5,302,911 sets) max q* 28, at (11,23,26,34,60). q* ≤ 11 for 5,107,054 of the 5,302,911.
  Random samples: primitive 5-sets ≤ 1000 (19,232) max 23; SixResidual sets with entries ≤ 80, 160, 320 (400 each)
  max 17 each. SixResidual ≤ 40: q* from 7 to 21, with 2 to 8 lonely unit instants at q* (mirror pairs).
- So the lonely instant is found among a small number of coarse opportunities: before q* in SixResidual ≤ 40 there are
  10–50 blocked grid instants in most sets (Σ φ(q), q < q*). Blocked opportunities are blocked by 1 runner (169,204),
  2 (128,617), 3 (53,855), 4 (15,837), 5 (1,206).
- q* is not the cascade's modulus: T's denominator equals q* in 4 of 17,135. The cascade finds the earliest isolation
  in time; the grid count finds the coarsest fold.
- **Reading** [observation]. Counted over the coarse grid instants, five runners run out of blocks quickly: across
  5.3 million sets an isolation appears by q = 28. The largest q* rose from 27 to 28 between [1, 40] and [1, 60], so a
  uniform bound is not established by these ranges. A statement "every primitive 5-set has a lonely c/q with q ≤ Q₀"
  depends only on the speeds mod lcm(1..Q₀): a finite residue statement. Literature on lonely instants with small
  denominators not checked (citation-verifier owed if used).

## E72 — Grid opportunities: range pushed to 120, and how the grids get blocked (2026-10-16)

Owner: *"continue the search then continue to push the range and how the grid gets blocked"*. Observation only.
`grid_qstar_v1.{c,out}` (C, exhaustive; agrees with `grid_opportunities_v3` at H = 60), `grid_blocking_v1.{py,out}`.
A citation-verifier run on bounded denominators is in progress (the first run was stopped at the owner's question and
relaunched on the owner's instruction); its result goes in a later entry.
- **Range.** Every primitive 5-subset of [1, H]: H = 80 (23,312,716 sets), 100 (72,918,416), 120 (184,425,816): max q*
  = 28 at each, attained by (11,23,26,34,60) and, at 120, also (18,23,41,64,105). The maximum has not moved since
  H = 60; the tail at q* ≥ 24 grows with H (counts in the .out).
- **How the grids before q* are blocked.** A runner blocks the unit instant c/q when its reading (d c mod q)/q is
  within 1/6 of the subject: ON the subject (q | d; it then blocks every instant of that grid) or NEAR it (entry side
  just past, exit side just before).
  - SixResidual ≤ 40: 107,817 grids blocked by a runner on the subject, 11,943 by near runners only. Commonest
    on-subject kills: q = 2 (any rank), q = 3, q = 4 by the fastest, q = 5 by the fastest, q = 6 by rank 2.
  - Near-only grids: each unit instant blocked by 1 runner (38,578), 2 (20,848), 3 (5,132), 4 (2); entry and exit
    sides equal (47,839 each; the mirror c ↔ q − c); spread evenly over speed ranks.
  - All primitive 5-sets ≤ 30 (139,246): the same split, 526,469 on the subject against 35,255 near-only.
- **Reading** [observation]. Grids are mostly killed wholesale by a runner sitting on the subject at every instant of
  the grid, i.e. a runner divisible by the grid; a runner can do that only for the grids that divide it. The grids no
  runner divides are killed instant by instant, with one to three runners near the subject on each. With five runners
  the grids run out by q = 28 on every set to H = 120.

## E73 — The uniform grid bound is false; correction to E71–E72 (2026-10-16)

citation-verifier (relaunched on the owner's instruction): no source states a uniform denominator bound, and the
statement is false. `grid_qstar_unbounded_v1.{py,out}` reproduces the refutation exactly: D = (1, 2, 3, 4, L), with
L = lcm(1..Q₀), has the fastest runner on the subject at every c/q with q ≤ Q₀, so the least lonely grid exceeds Q₀:
Q₀ = 6 → q* = 16; 12 → 16; 20 → 23; 28 → 29; 40 → 41; 60 → 61.
- E71–E72's "q* ≤ 28" is a property of the search box [1, 120]: no speed there is divisible by every q ≤ 28. Kept as
  an observation tied to that box. E71's "a uniform bound is not established" stands; any reading of E72 as "runners
  run out of grids by 28" in general is withdrawn.
- In E72's terms the refutation is the on-subject kill taken to its limit: one runner divisible by every grid up to Q₀
  kills them all wholesale. What survives is the conditional form: an isolation appears at the first grid that no
  runner kills on the subject, unless near blocks kill it instant by instant (precedent: Rosenfeld 2025, Lemma 4 —
  lcm(2..k+1) divides the product of the speeds of any set without the property — and Lemma 6, as reported by the
  verifier; not read here).
- Other reported sources, all with speed-dependent denominators: Perarnau–Serra survey (2024) eq. (4) t₀ = ℓ/(vᵢ+vⱼ);
  Rifford's timely conjecture bounds laps of the slowest runner (a different quantity); Barajas–Serra N = 7^{m+1};
  Tao 2018 bounds speed size.

## E74 — The counterexample family is beaten by the AP's window (2026-10-16)

Owner: *"But we have ap and residue"*. Check (inline, exact): the four-runner AP (1,2,3,4) at threshold 1/6 is lonely on
whole windows, not points: [1/6, 5/24] and [19/24, 5/6] (length 1/24), [7/18, 5/12] and [7/12, 11/18] (length 1/36),
per lap. The lonely instants found for (1,2,3,4,lcm(1..Q₀)) — 3/16, 4/23, 5/29, 7/41, 24/61 — all lie in these windows.
- **Reading** [observation]. E73's family kills every small grid but not the AP's window: four runners at threshold
  1/6 have slack (they are an order-five arrangement, isolated with room at 1/5), so their isolation is an interval,
  and the fifth runner, whatever its residue, is folded through that interval. A runner of speed X sweeps X/24 laps
  across a window of length 1/24, so for X ≥ 8 it cannot stay inside its blocked third for the whole window. The grid
  bound fails because the instant's denominator follows the fifth runner; the AP-plus-residue mechanism does not.
  This is the lower-order slack that the merge-and-stepping reduction and Renault's order-five seed also use.

## E75 — Where the cascade puts the isolation, against the lower-order window (2026-10-16)

Owner: *"Compare your result to where the cascade points the isolation point is"*. Observation only.
`cascade_vs_window_v1.{py,out}`.
- **Family (1,2,3,4,L), L = lcm(1..Q₀).** The cascade instant is T = (L+1)/(6L) = 1/6 + 1/(6L) for Q₀ = 6, 12, 20, 28, 40:
  the fast runner's first entry after the AP window [1/6, 5/24] opens, with L as the final flank. The cascade picks the
  earliest point of the same AP window that E74's grid instants (3/16, 4/23, 5/29, …) sit inside; T − 1/6 shrinks like
  1/(6L).
- **SixResidual ≤ 40.** At T the final flank b reads exactly 1/6 and the other four are lonely on a window W containing
  T: T inside W in 16,647, at W's left end in 488. The other four are also lonely at 1/5 somewhere in W (order-five slack)
  in 14,146 of 17,135; not in 2,989. b is the fastest runner in 4,275. W's length × d_min mostly 0.01–0.08.
- **Reading** [observation]. On the family the cascade does exactly the window-and-fold: it enters the lower-order
  window at its start and stops at the fold runner's first opening inside it. On SixResidual the same picture holds
  as a shape (the cascade's instant is the final flank's entry into the other four's window), with order-five slack in
  that window in 83% of sets; in 17% the four's window at T has no 1/5 instant, so there the window is not order-five
  slack, and what supplies it is not yet described.

## E76 — The 2,989 sets: the same window-and-fold one order down (2026-10-16)

Owner: *"what you are describing is classes of arrangement, so yes look at those 2989 sets but all they will be doing is
supplying or corroborating the arrangement cascade outcome type we have previously looked into"*. Observation only.
`noslack_types_v1.{py,out}`, `noslack_lower_v1.{py,out}`.
- **Against earlier outcome types.** BHK §7 is 0.66 of the 2,989 (0.51 of the rest); one-move walks 0.54 (0.40); final
  flank fastest 0.39 (0.22); early ending 0.996 (0.958). The final flank's opening is often on a high lap: (rank 5,
  lap 7) 258, (5, 6) 160, (4, 6) 149, against laps 0–2 dominating the rest.
- **One order down.** At the cascade instant, a triple of runners has its 1/6-window around T with a 1/4 instant
  (order-four slack, two runners folding through) in 2,911 of the 2,989; in 77 only a pair has a 1/3 instant (three
  folding); in 1 neither: (2, 9, 13, 36, 40), T = 7/78, final flank 13. Commonest triples: ranks (2,3,5) 1,782,
  (2,3,4) 1,641, (2,4,5) 1,532.
- **Reading** [observation]. The other source is the same mechanism at the next level: a lower-order arrangement
  isolated with room supplies a window, and the remaining runners fold through it. By depth: four-runner slack 14,146,
  three-runner slack 2,911, two-runner slack 77, none found 1. The three-runner level is the shape of the §7 native route
  (E51–E56: runners 1–3 supply the window, `window_two` folds runners 4 and 5) and of §5's two steps (E38), now seen with
  any triple. The single remaining set is the next thing to look at.

## E77 — The finite outcome taxonomy from the order-8 corpus, carried to order 6 (2026-10-16)

Owner: *"check the corpus for the large amount of work that was done on the finite arrangement outcome set we did"*.
Source found: order-8 E325 (`docs/n8/RUNNING_LOG_order8_v1.md`; `LonelyRunner/experiments/nN/redo/
taxo_outcome_classes_v1.md`): 14 mutually exclusive outcome classes by number of moves (0 / 1 / ≥ 2), window width zero,
closer = the opener's own reading, opener lap (1 / ≥ 2), opener a strip reading; 12 realised on 52,000 order-8
arrangements, K2a empty by argument, K2s1 empty (proved later, E333). Related: `docs/n8/FINITE_ARRANGEMENT_REVIEW_
2026_10_03.md` (43 of 49 ordered opener/closer pairs; finite outcome classes are not yet a finite mechanism cover).
Order eight read only, as a comparison. `taxo6_v1.{py,out}`: the same definitions with 8 → 6 (readings ρ = d/d₁,
R = 6 d₁ t, zone 6j − 1 < Rρ < 6j + 1).
- **Order 6, primitive SixResidual ≤ 40 (17,135):** 12 classes realised — K0 2,387, K0z 621, K1a 5,539, K1b 1,232,
  K1s1 251, K1s2 101, K1z 76, K2b 716, K2c 2,447, K2d 3,361, K2s2 249, K2z 155 — and the same two empty, K2a and K2s1.
  All primitive 5-sets ≤ 30 (139,246): the same 12 classes, the same two empty.
- **(2, 9, 13, 36, 40)** is K1a: one move, the opener 13 a strip reading on lap 1 (ρ = 13/2 ∈ (5, 7)), closer another
  reading. An ordinary outcome class; E76's "none" was a property of the slack-depth test, not a new outcome type.
- **Slack depth against class (E76):** depth four spans all 12 classes; depth three is mostly K1a 935, K2d 1,059,
  K1b 598, K0z 209; depth two K2d 38, K1b 22, K0z 10, K1a 6, K0 1.
- **Reading** [observation]. The outcome set found at order 8 is the same finite set at order 6: twelve realised
  classes, the same two empty, on every set tested. Slack depth is a different cut across those classes, not a new
  class. Whether each class carries one uniform mechanism (the open item of the finite-arrangement review) is the same
  question at order 6.

## E78 — Digression: the outcome taxonomy at orders 3–7 (2026-10-16)

Owner: *"lets map the arrangement outcomes via cascade in lower orders and see how they develop"*. Observation only.
`taxo_orders_v1.{py,out}`: E325's classes with 8 → n, exhaustive over primitive (n−1)-subsets of [1, H_n]
(H = 200, 90, 50, 30, 22 for n = 3..7; ranges differ, so counts are not comparable across orders, class sets are).
- **n = 3** (12,231 sets): 5 classes — K0 7,392, K0z 67, K1a 1,225, K1s1 1,833, K1s2 1,714. At most one move
  (as `FewDifferences.two_diffs_stop_within_one_move` proves), so no K2 class; no K1b or K1z: with two runners the
  one-move landing's closer is the opener itself in 3,547 of 4,772 moving sets.
- **n = 4** (98,689): all 12 classes, K2a and K2s1 empty; at most 3 moves.
- **n = 5** (215,659), **n = 6** (139,246), **n = 7** (74,144): the same 12 classes, the same two empty. Order 8
  (E325, a different sample): the same.
- What grows: (opener rank, closer rank) pairs among moving cascades 2, 4, 7, 14, 21 of (n−1)² for n = 3..7; most moves
  1, 3, 12, 11, 16; largest landing R* 1.99, 2.97, 3.27, 4.63, 4.13 (all on these ranges).
- **Reading** [observation]. The class set is complete from order 4 on: order 3 has five classes because a two-runner
  cascade stops within one move; from order 4 the twelve classes are all present, with the same two empty through
  order 8. What complicates with the order is inside the classes: more opener/closer pairs, longer paths, later
  landings. The class structure itself does not grow.

## E79 — What drives the most moves (2026-10-16)

Owner: *"What drives the most moves?"*. Observation only. `long_cascades_v1.{py,out}` (longest cascades, same exhaustive
ranges as E78), `long_cluster_v1.{py,out}`, `long_cluster_v2.{py,out}` (families).
- **The longest cascades** are one slow runner plus a run of consecutive or near-consecutive fast speeds ending exactly
  on a multiple of n times the slow speed: n = 7: (1,17,18,19,20,21) 16 moves (21 = 3·7), (1,10,…,14) 12 (14 = 2·7);
  n = 6: (1,9,10,11,12) 9 (12 = 2·6); n = 5: (1,23,25,48) 12 (25 = 5·5). The setters go round the run in order, each
  one lap higher than its previous knot ((6,3),(5,3),(4,3),(3,3),(2,3),(6,4),…), with one runner in the way at almost
  every move.
- **Families** (1, nj−k+1, …, nj), k = n − 2, j = 1..40:
  - ending on nj: n = 7 moves 8, 12, 16 for j = 1, 2, 3, then 5 for every j ≥ 4; n = 6: 5, 9, then 4; n = 5: 4, then 3.
  - ending on nj − 1: 0 moves for every j (the run's residues are all nonzero mod n, so 1/(n d₁) is a global-isolation
    instant).
  - ending on nj + 1: n = 7: 5, 10, then 4; n = 6: 5, then 3; n = 5: 2.
  - A tight cluster away from a multiple of n does not give long cascades (cluster of 4 at n = 6: 3 moves at w = 100,
    0 at w = 200).
- **Reading** [observation]. Length is driven by an AP-like run of fast runners whose residues mod n include 0: a
  global-isolation arrangement with one runner on the subject. The knot passes down the run residue by residue, one lap
  per runner per round. The number of rounds is largest when the multiple is small (j ≤ 3 here) and settles at one
  round for larger j. Moving the run one below the multiple removes the 0 residue and the cascade makes no move at all.

## E80 — Formalised: the AP plus one runner at every order, and the knot's other side (2026-10-16)

Owner: *"Can we formalise any of this?"*. `APFold_v1.lean` (`.out`: 0 errors; no `sorry`/`native_decide`/`admit`).
`#print axioms`: `[propext, Classical.choice, Quot.sound]` for both. [PROVED]
- **`ap_plus_one`** (every order n ≥ 3): the runners 1, …, n − 2 and any X > n − 2 are lonely at threshold 1/n. Two
  instants: X not a multiple of n → the global-isolation instant 1/n (`ap_plus_one_unit`); X = nq → X sits on the
  subject at 1/n, and 1/n + 1/(nX), where X re-enters, is lonely (`ap_plus_one_fold`; the small runners stay clear
  because (n − 2)(X + 1) ≤ (n − 1)X). This is E73's family (n = 6, X = lcm(1..Q₀)) with the cascade's own instant (E75),
  and E79's "run ending on nj − 1 makes no move" in its simplest case.
- **`knot_other_side`** (every order): when a lap box dies at the knot (n a + 1) v_J = (n b + n − 1) v_I (I on lap a
  entering as J on lap b exits), in the box where J takes one more lap the knotted pair's first condition always holds
  and the second holds exactly when 2a ≤ (n − 2) b + n − 3. Checked against E68's deaths (`knot_lemma_check_v1.{py,out}`):
  the pair's status in m + e_J agrees with 2m_I ≤ 4m_J + 3 in 7,812 of 7,812.
- Not formalised: the chain of further knots (that is the cascade and its termination); the outcome taxonomy's empty
  classes K2a, K2s1 at every order (E78; order-8 proofs by hand, E325/E333) — candidates.

## E81 — The two empty outcome classes in Lean; rethinking the order-six formal proof (2026-10-16)

Owner: *"Yes k2a and k2s1 then back to order six. Also lets rethink about our proof formalisation and think if any of
this can supersede any of it"*.
- `TaxoEmpty_v1.lean` (every order; axioms `[propext, Classical.choice, Quot.sound]` for all three) [PROVED]:
  `k2a_empty` (with two or more jumps a lap-1 opener is never a strip reading; uses the run's monotonicity R* > R₂ ≥ 1 as
  hypotheses), `closer_same_forces_fastest` (a faster reading clear at R* re-enters before the opener does, n > 2),
  `fastest_lap_one_first_jump` (a fastest lap-1 opener is below every slower reading's exit, so it is reached by the
  first jump). Together: K2a and K2s1 are empty at every order. Data check `taxo_empty_check_v1.{py,out}`: closer =
  opener ⇒ opener fastest in 11,522 / 8,557 / 1,738 / 303 sets (n = 4..7), K2a/K2s1 occurrences 0.
- `FORMAL_RETHINK_v1.md`: the proof of record by part. §7 and §2 are native in the dispatch (E58); none of today's
  results replaces §5, §6 or §8 as it stands. Candidates: (1) §8 by the slow-block window [1/(6v₁), 5/(6v₃)] plus
  `window_two_uniform` (E7: runners 2, 3 inert in 3,710 of 3,716 §8 walks); (2) §5/§6 natively via shifted meeting
  instants (untested); (3) Renault's core in framework form (Chen's Lean is Apache-2.0) — reformulated track, owner's
  decision.

## E82 — §8 by slow-block windows: tested, and the first-window statements proved (2026-10-16)

Owner: *"Start candidate 1: test on the §8 sets which window and lap closes each (slow-block window plus
window_two_uniform), then prove what holds."*
- **Test** (`s8_window_v1..v3.{py,out}`; every primitive 5-set ≤ 40 with v₃ ≤ 3v₁: 293,922). Block of runners 1–3,
  window W(m₁,m₂,m₃) where all three are clear; runners 4, 5 by `window_two_uniform` (|W| ≥ 2/(3v₄)) or `window_two`.
  First window [1/(6v₁), 5/(6v₃)] passes the uniform test in 136,938, the sharp test in 179,122; a later window (t ≤ 3/v₁;
  commonest laps (1,2,3), (0,1,1), (0,0,1)) in most of the rest; 42,558 have no passing three-block window. Of those, a
  block of runners 1–4 with runner 5 folded alone (v₅|W| ≥ 1/3) closes 42,262 (first window 39,907); the spread box closes
  226 and the runner-5 second-lap box 33; 37 remain, all of the shape (k, 2k, 3k, 4k or 5k, X) with 5k < X < 8k, landing
  on lap vectors (0,0,0,1,1) (27), (0,0,1,1,2) (8), (0,1,2,3,4) (2).
- **Proved** (`S8Windows_v1.lean`, `.out`: 0 errors; axioms `[propext, Classical.choice, Quot.sound]`) [PROVED]:
  `block_clear`, `fold_one` (a runner sweeping a third of a lap across a window meets the band there),
  `s8_block3_window` (4v₁v₃ ≤ v₄(5v₁ − v₃) ⇒ lonely, via `window_two_uniform`), `s8_block4_fold`
  (2v₁v₄ ≤ v₅(5v₁ − v₄) ⇒ lonely). Real speeds, ordered, no §8 hypothesis needed beyond the inequality.
- **Coverage of the proved first-window statements plus the two proved boxes** (`s8_coverage_v1.{py,out}`): H = 40:
  288,210 of 293,922 (T1 136,938, T3 126,310, spread 21,269, second-lap 3,693), 5,712 left; H = 60: 2,363,415 of
  2,405,392, 41,977 left (1.7%).
- **Consequence.** §8 is not yet replaced: the remaining 1.7–1.9% needs later windows (each is the same proof with
  shifted laps) and, on these ranges, three lap boxes for the (k, 2k, 3k, ·, ·) family. Turning that into a statement
  about all of §8 means showing the listed windows and boxes cover the remaining region of ratios, which is a covering
  statement (E2's framing; the owner's call). BHK's `lonely_8` stays in the dispatch.

## E83 — §8: later windows and lap boxes proved; the open region of ratios (2026-10-16)

Owner: *"Prove the later-window versions (laps (1,2,3), (0,1,1), (0,0,1)) and the three lap boxes, then check what region
of ratios is still open."*
- **Proved** (`S8Windows_v2.lean`, versioned successor of v1; `.out` 0 errors; axioms `[propext, Classical.choice,
  Quot.sound]`) [PROVED]: `block3_window_laps` (runners 1–3 on any laps clear on [L, U], runners 4, 5 by
  `lonely_of_window`, i.e. `window_two`'s base and residue conditions); `block4_fold_laps` (runners 1–4 on any laps,
  runner 5 folded when v₅(U − L) ≥ 1/3); `box5` (the five-runner lap box). The requested laps are instances: windows
  (1,2,3), (0,1,1), (0,0,1); boxes (0,0,0,1,1), (0,0,1,1,2), (0,1,2,3,4) (and the spread / second-lap boxes are
  (0,0,0,0,0), (0,0,0,0,1)).
- **Coverage by this finite list** (`s8_coverage_v2.{py,out}`; primitive §8 sets): H = 40: 293,850 of 293,922 closed,
  72 open; H = 60: 2,404,883 of 2,405,392, 509 open (0.02%). Contributions at H = 60: window (0,0,0) 1,478,383;
  four-block fold (0,0,0,0) 531,407; windows (1,2,3) 109,383, (0,1,1) 105,790, (0,0,1) 97,457; boxes 69,455 / 7,135 /
  4,944 / 660 / 269.
- **The open region** (ratios to v₁, H = 60): v₂ ∈ [5/3, 23/9], v₃ ∈ [8/3, 3], v₄ ∈ [11/3, 29/5], v₅ ∈ [56/11, 59/5];
  at H = 40 the ranges are inside these. A bounded region at the edge v₃ ≈ 3v₁ of §8; examples (2,4,6,9,23),
  (3,5,9,13,34), (3,5,9,16,35). Four-block folds on laps (1,2,3,4), (0,1,2,3), (0,1,1,1), (0,0,1,1) close 198 of the 509.
- **Consequence.** The finite list closes every §8 set on these ranges outside one bounded region of ratios, and the
  open count grows with H as a region of positive size does. Closing that region needs more windows or boxes and a
  statement that they cover it (a covering statement over a bounded polytope; E2's framing, the owner's call).
  BHK's `lonely_8` stays in the dispatch.

## E84 — The open §8 region mapped; six lap boxes cover it on every point tested (2026-10-16)

Owner: *"Map the open region exactly: its defining inequalities, which lap boxes or windows close its points, and
whether a short finite list covers it. Observation first."* `s8_region_v1.py` with `s8_region_v1.out` (v₁ ≤ 14, cover
tested to 20) and `s8_region_v2.out` (v₁ ≤ 20, tested to 24); `s8_region_boxes_v1.out`.
- **Definition.** In ratios xᵢ = vᵢ/v₁ (all statements are homogeneous), the open region is the part of §8
  (1 < x₂ < x₃ ≤ 3 < … , x₃ < x₄ < x₅) where every statement of E83's finite list fails: each of the windows W3 on laps
  (0,0,0), (1,2,3), (0,1,1), (0,0,1) is empty or fails `window_two`'s base or residue condition; the four-block fold on
  (0,0,0,0) fails (v₅|W| < 1/3 or W empty); each of the five boxes has a violated pair (6kᵢ+1)xⱼ > (6kⱼ+5)xᵢ.
- **Extent** (dense enumeration inside the H = 60 bounding box, all primitive points with v₁ ≤ 24: 147,114 open points):
  x₂ ∈ [37/24, 18/7], x₃ ∈ [60/23, 3], x₄ ∈ [83/23, 143/24], x₅ ∈ [121/24, 287/24]. Every open point has a lonely lap
  vector with t ≤ 3/v₁ (0 exceptions).
- **Cover.** Greedy cover of the 65,356 open points with v₁ ≤ 20 by lap boxes: six boxes — (0,0,0,1,2) 44,923,
  (0,1,2,3,8) 14,646, (1,3,4,5,7) 5,170, (1,2,3,4,6) 514, (0,1,1,2,2) 68, (1,3,4,6,8) 35. Tested on all 147,114 open
  points with v₁ ≤ 24: 0 uncovered. (The cover built at v₁ ≤ 14 had (1,4,5,7,9) in place of (0,1,1,2,2) and missed 6
  points at v₁ ≤ 20, all near x₅ ≈ 5, x₃ = 3, e.g. (15,34,45,62,76); the v₁ ≤ 20 cover closes them.) Each box is the
  cone of its 20 pair conditions (ratio bounds listed in `s8_region_boxes_v1.out`), and each is an instance of `box5`.
- **Consequence** [observation]. On every point tested, §8 is closed by a finite list: five windows or folds, five boxes
  (E83) and these six boxes, all instances of proved lemmas. What is not shown is that the six cones cover the whole
  continuous open region: points of the region at finer rational spacing could fall in thin gaps between cones (the
  v₁ ≤ 14 cover missed such slivers). An exact certificate would subdivide the bounded region and check, cell by cell,
  that one statement holds throughout (linear for boxes: check the cell's vertices); that is a covering certificate,
  E2's framing, the owner's decision.

## E85 — §8: an exact cell certificate closes the whole region (2026-10-16)

Owner: *"Yes: build an exact cell-subdivision certificate that the finite list covers the whole bounded open region of
section 8, then decide how to put it in Lean."* Scripts `s8_cert_v1..v5.py` (outputs `.out`), leaves
`s8_cert_v5_leaves.txt`; Lean `S8Cert_v1.lean` (`window_two_simple`, axioms `[propext, Classical.choice, Quot.sound]`).
- **Domain.** Ratios xᵢ = vᵢ/v₁: 1 ≤ x₂ ≤ x₃ ≤ 3, x₃ ≤ x₄ ≤ x₅. The part x₄ ≥ 6 is closed by `s8_block3_window` (proved,
  E82). The rest is x₂, x₃ ∈ [1, 3], x₄ ∈ [1, 6], x₅ ∈ [1, 30] or [30, ∞), started on the unit grid (so the tight AP point
  (1,2,3,4,5) is a corner) and bisected on the widest side; cells clipped by the ordering.
- **Test per cell (exact, worst corner; every condition is monotone in each variable):** three-block windows in
  `window_two`'s own form (base and residue conditions; for x₅ ∈ [30, ∞) the closed form 1/(3a) + 2/(3b), proved as
  `window_two_simple`), the four-block fold, and lap boxes (the 20 pair inequalities).
- **History.** v1–v2 used the closed form for every window and left large failing regions (v2: 2.87 million failing
  cells at depth 24); v3 with the exact window_two test left 273 failing cells near x₃ = 3, x₅ ≈ 11.86; v4 added, from the
  failing cells' centres, five boxes and three windows; then 0 failing cells.
- **Result (v5)** [certificate computed; independent re-check owed]: 1,226 certified leaves, depth ≤ 22, largest
  endpoint denominator 32. Final list: windows (0,0,0), (1,2,3), (0,1,1), (0,0,1), (0,1,2), (2,6,7), (1,3,4); fold
  (0,0,0,0); boxes (0,0,0,0,0), (0,0,0,0,1), (0,0,0,1,1), (0,0,1,1,2), (0,1,2,3,4), (0,0,0,1,2), (0,1,2,3,8),
  (1,3,4,5,7), (1,2,3,4,6), (0,1,1,2,2), (1,3,4,6,8), (0,1,2,3,9), (2,6,7,10,14), (1,3,4,6,17), (1,3,4,6,18),
  (0,1,1,2,6). Every statement is an instance of `block3_window_laps`, `block4_fold_laps` or `box5` (E83).
- **Lean plan (decided, not started).** (1) An integer checker: each leaf's inequalities cross-multiplied to ℕ/ℤ, so the
  kernel's accelerated Nat arithmetic evaluates them under plain `decide` (no `native_decide`). (2) Soundness lemmas: a
  leaf whose check passes satisfies the real hypotheses of its statement at every point of the cell (monotonicity).
  (3) Tree soundness: the bisection tree covers its start cell (induction on the tree). (4) `lonely_8_native` on whole
  numbers with v₃ ≤ 3v₁, then rewire `lonely6_of_lt` as was done for §7 (E58). Owed first: an independent re-check of the
  leaves (random rational points located in a leaf and tested exactly).

## E86 — §8 natively in the order-six proof: the certificate in Lean, kernel-checked (2026-10-16)

Owner: *"lets continue on"* (after E85's Lean plan).
- **Core** (`S8CertCore_v1.lean`): cells of ratio bounds (`hi 3 = 0` = unbounded), statements (three-block window with
  endpoints L, U in units of 1/v₀; four-block fold; five-runner lap box), a rational checker (`stmtOK`) and its soundness
  (`band_sound`, `w3_sound`, `f4_sound`, `box_sound`, `stmt_sound`); clipping by the §8 order (`clip_sound`), empty cells
  (`empty_sound`), the bisection tree and `tree_sound` (induction on the tree).
- **Certificate** (`s8_cert_lean_gen_v1.py` builds it with the Lean semantics exactly; `S8CertFull_v1.lean`): root
  ratios x₂, x₃ ∈ [1, 3], x₄ ∈ [1, 6], x₅ ∈ [1, ∞); 760 leaves, 759 splits, depth ≤ 32, the E85 list of statements.
  `cert_ok : checkTree certTree root = true` by `decide +kernel` (no `native_decide`; about 45 s). `lonely_8_box`
  (x₄ ≤ 6), `lonely_8_far` (x₄ ≥ 6, first window), `lonely_8_real` (every ordered real arrangement with v₂ ≤ 3v₀),
  `lonely_8_native` (whole numbers, the dispatch's form; lap shift for t > 0).
- **In the tree** (nested repo commit, not pushed): `LonelyRunner/LRC/Spec/OrderSixEightNativeN.lean` (namespace
  `LRC.S8Native`); `lonely6_of_lt` now calls `lonely_8_native`; BHK's `lonely_8` kept. `S8Native_wiring_v1.out`: build of
  the order 3–7 targets (8,333 jobs); axioms `[propext, Classical.choice, Quot.sound]` for `lonely_8_native`,
  `lonely6_of_lt` and `lonelyRunnerAtN_3..7`; the dispatch's proof term references `lonely_8_native` and
  `lonely_7_native` and not `lonely_8`. [PROVED]
- The independent Python re-check of E85's leaves was stopped unfinished; its output was buffered to the end, so it
  reported nothing either way. The kernel check of the Lean tree supersedes it (it checks the tree Lean uses, not E85's
  leaf file).
- **Consequence:** the order-six proof of record now takes §7, §2 and §8 by native routes. §5 and §6 remain BHK's form.
  The §8 route is a covering certificate over a bounded region of ratios (E2's framing; the owner asked for it, E85).

## E87 — §5/§6 tested for windows, folds and boxes; §8 "symbolically" (2026-10-16)

Owner: *"Yes test para5 and 6. And also see if para8 can be resolved symbolically and perhaps it can also use only the
standard axioms"*. Observation only. `s56_window_v1.{py,out}`, `s56_failures_boxes_v1.out`, `s8_cert_small_v1/v2.{py,out}`.
- **§5/§6** (primitive 5-sets ≤ 24 with 3v₁ < v₃ and D ∣ v₁ (§5, 4,646) or D ∣ v₃, D ∤ v₁ (§6, 3,354)). Allowing any block
  (three runners + `window_two` on the other two, or four runners + the fifth folded), laps with t ≤ 3/v₁: 7,984 of 8,000
  closed. A greedy list needs 72 (statement, block, laps) types at H = 24, led by block {1,2,3} on laps (0,1,1) 2,467 and
  (0,1,2) 1,927; laps grow with v₂/v₁ ((0,3,4), (0,5,6), (0,7,8), …): in §5/§6 the ratios are unbounded, so no finite
  list of fixed laps can close the region; a §8-style certificate needs a parametric lemma for large ratios.
- **The 16 unclosed sets** all have lonely sets of width 0 (isolated instants): the tight set (1,3,4,5,9), (1,4,5,6,·),
  (2,5,7,9,15), and the run family (1, 3k+2, …, 3k+5) — e.g. (1,8,9,10,11) is lonely exactly at 1/6 with every runner on a
  slot: residues 1,2,3,4,5 mod 6, a residue-isolation arrangement (E65–E66). These are corners where only degenerate
  boxes meet (like the AP in §8, `grid_tight_pairs`), and there are infinitely many of them, one per k: a finite cell
  certificate cannot have them all as corners. What would close them uniformly is a parametric lemma for neighbourhoods
  of residue-isolation points (the two boxes K₀(p=1)+…, K₀(p=5)+… on either side, E65's sheets), not yet stated.
- **§8 axioms.** `lonely_8_native` already depends only on `[propext, Classical.choice, Quot.sound]` (E86):
  `decide +kernel` adds no axiom (unlike `native_decide`).
- **§8 symbolically.** The first four statements are closed-form case conditions: x₄(5 − x₃) ≥ 4x₃ (first window),
  x₄ < 5 ∧ x₅(5 − x₄) ≥ 2x₄ (four-block fold), x₅ ≤ 5 (spread box), x₄ ≤ 5 ∧ 7x₄ ≤ 5x₅ ∧ x₅ ≤ 11 (second-lap box);
  they close 98.3% of §8 sets by count (E82). The remaining bounded region needs the later windows and boxes on cells.
  Two attempts to shrink the 760-leaf tree with free split points failed at the AP corner (1,2,3,4,5): x₂ = 2, x₃ = 3,
  x₄ = 4, x₅ = 5 must be cell boundaries, because only the two degenerate boxes (0,0,0,0,0) and (0,1,2,3,4) meet there.
  A hand-symbolic §8 would be the four closed-form cases plus a hand cover of the bounded remainder; not attempted.

## E88 — What the 0.2% of §5/§6 is, why it occurs, and what it changes (2026-10-16)

Owner: *"first we need to understand what this 0.2% is and why it occurs and does why it happens mean we should adjust
how we got there."* `s56_failures_v2.{py,out}`, `s56_cluster_box_v1.{py,out}`.
- **Correction to E87.** "All 16 have lonely sets of width 0" is wrong: E87's readout listed only the first three lap
  vectors found (the tight points 1/6, 5/6). Over a full period (exact) only (1,3,4,5,9) is tight (isolated points,
  agreeing with E24); the other 15 have positive-width lonely intervals, all narrow.
- **What they are.** Two kinds:
  1. the tight set (1,3,4,5,9) (lonely only at 1/6 and 5/6);
  2. one slow runner plus a cluster of near-equal fast speeds: the run family (1, 3k+2, 3k+3, 3k+4, 3k+5) (E79's
     long-cascade family), (1,4,5,6,X) and (2,5,7,9,15). Their widest lonely intervals shrink with the cluster's speed:
     width × v₁ = 5/252, 5/528, 11/936, 11/1428, 17/2052, 17/2760 for k = 1..6.
- **Why.** Window and fold statements treat runners one or two at a time, with fixed length thresholds (≥ 2/(3a),
  ≥ 1/(3b)). A cluster of near-equal speeds blocks almost every instant collectively: its readings stay together only
  while their spread (3t for a run of four) is under 2/3, so with the slow runner needing t ≥ 1/6 the lonely instants
  sit in short intervals near t ≈ 1/6–2/9. No individual threshold is met there.
- **The collective statement exists as a parametric lap box.** For the run family, laps (0, m, m, m, m), m = ⌈k/2⌉:
  the box reduces to v₅ ≤ 6m + 5, 6m + 1 ≤ 5v₂ and v₅/v₂ ≤ (6m+5)/(6m+1) (the cluster's spread). Exact check: holds for
  k = 2..2,000 (1,999 of 1,999); k = 1 by the box (0,2,2,3,3).
- **What it changes** [reading]. The finite fixed list (E83–E86) works on a bounded region of ratios. For unbounded
  directions (§5/§6, where v₂/v₁ is unbounded) the list must contain families indexed by an integer m — a box or window
  whose laps scale with m, covering a corridor to infinity — rather than more fixed boxes. The cluster box is the first
  such family; the residue-isolation corners (E87, e.g. (1,8,9,10,11)) sit inside this family's corridor. The route
  stands; the statement list needs parametric members.

## E89 — Is §5/§6 at 100%? The corner lemma; hand-symbolic §8 (2026-10-16)

Owner: *"So is that full coverage? We now have a 100%? then move on to corner lemma and hand symbolic"*.
- **Coverage.** On the 8,000 §5/§6 sets ≤ 24, every set is closed by some statement: windows/folds 7,984; the 16 by lap
  boxes (the cluster box family, (0,2,2,3,3), and the boxes at their lonely instants). That is 100% of the tested sets,
  but not a proof: a lap box exists for every lonely set by definition, so coverage only means something for a fixed or
  parametric list, and the §5/§6 region of ratios is unbounded. No such list is established yet.
- **Corner lemma** (`corner_lemma_v1.{py,out}`, `_400.out`; `CornerLemma_v1.lean`) [observation + PROVED]. At a
  residue-isolation arrangement d (residues 1..5 mod 6, one each) the boxes K = ⌊d/6⌋ and K' = ⌊5d/6⌋ each have exactly
  one equality pair at d (entry runner e of residue 1 against exit runner x of residue 5) and all other pairs strict;
  the two equalities are the two sides of one hyperplane d_e v_x = d_x v_e (because 5d_x = 6K'_x + 1, 5d_e = 6K'_e + 5).
  Checked on seven such d (including (1,2,3,4,5), (1,8,9,10,11), (5,7,10,15,20)): 2,000 of 2,000 perturbations in K or K'
  at relative size slack/400 (at slack/40, 1,983 and 1,997 of 2,000 for two of them, so the neighbourhood is smaller
  there). `corner_two_boxes` [axioms `propext, Classical.choice, Quot.sound`]: if box K holds except for the pair (e, x),
  box K' except for (x, e), and (6K_e+1)(6K'_x+1) = (6K_x+5)(6K'_e+5), then one box holds and the arrangement is lonely.
  This generalises E23's `mirror_opening` from the pair to the whole box, for every residue-isolation corner (and every
  simple degenerate point, e.g. (1,3,4,5,9)). In a cell certificate it is a split along that hyperplane, which is
  axis-aligned (x_x = c) when the residue-1 runner is runner 1.
- **Hand-symbolic §8** (`s8_symbolic_v1.{py,out}`). Of the 760 certificate leaves, 131 lie wholly inside the four
  closed-form cases (A first window 23, B four-block fold 23, C spread box 10, D second-lap box 75; worst-corner test);
  629 lie in the remainder and use 18 statements. Merging neighbouring leaves with the same statement leaves 261 boxes.
  With the present statements a hand proof of the remainder would be 261 cases, so the remainder stays as the
  kernel-checked certificate (already only the standard axioms, E86). A shorter hand proof needs stronger lemmas that
  cover larger regions, not more case splitting.

## E90 — Stronger §8 statements: folds on later laps; certificate 760 → 322 leaves (2026-10-16)

Owner: *"Look for stronger lemmas that cover larger regions of §8, to shorten a hand proof."*
`s8_stronger_v1.py` (`_v1.out`, `_v2.out`), `s8_cert_lean_gen_v2.py`/`_v3.py` (`.out`), `s8_symbolic_v2/v3.{py,out}`,
`S8CertTree_v3.txt`, `S8Native_wiring_v2.out`.
- **Wide search on the remainder R** (outside cases A–D): random rational points (denominator 97, x₅ ≤ 13), every
  three-block window and four-block fold on any laps (t ≤ 3/v₁) and the boxes at each point's lonely instants; greedy
  list. Samples of 3,000 (two seeds): seven statements each, led by the **four-block fold on laps (0,0,0,1)** (runner 4
  on its second lap, runner 5 folded) with 2,151 / 2,186, the **box (0,0,0,1,1)** 638 / 613, and the four-block fold on
  laps (0,1,1,2) 158 / 142; fresh samples of 3,000 not closed: 9 and 0.
- **Certificate rebuilt** with folds on laps (0,0,0,0), (0,0,0,1), (0,1,1,2) and boxes (0,0,0,1,3), (0,1,1,2,3) added:
  322 leaves (was 760), depth ≤ 27. Of these, 90 lie wholly in cases A–D; the remainder's 232 leaves merge into 89
  same-statement boxes (was 261) when folds and boxes are tried before windows.
- **In the tree** (nested commit `da8d4c1`, not pushed): `OrderSixEightNativeN.certTree` replaced by the 322-leaf tree;
  build of the order 3–7 targets passes; axioms `[propext, Classical.choice, Quot.sound]`; the dispatch still uses
  `lonely_8_native` and `lonely_7_native`.
- **Reading.** The stronger statements are folds of runner 5 through a four-runner window with runner 4 on a later lap:
  the four-runner block still has room when runner 4 is a lap ahead. Together with the box (0,0,0,1,1) they close about
  93% of R in the samples. A hand proof is now the four closed-form cases plus 89 boxes; shorter still would need the
  fold-(0,0,0,1) and box-(0,0,0,1,1) regions written as explicit inequalities and their union shown to cover most of R.

## E91 — Parametric families for §5/§6 (2026-10-16)

Owner: *"Leave §8 here and build the parametric statement families for §5/§6."* Observation only.
`s56_slices_v1.{py,out}`, `s56_families_v1.{py,out}`, `s56_rest_v1.{py,out}`, `s56_rest_corners_v1.out`.
- **§5/§6 are integer-indexed slices.** §6: v₃ = cD, v₂ = (c−1)D, so x₂ = x₃(c−1)/c, one slice per c ≥ 2. §5: v₁ = c′D, so
  x₃ − x₂ = 1/c′, one slice per c′ ≥ 1. By slice (sets ≤ 26), the closing three-block windows follow the index: in §6
  slice c, block {1,2,3} on laps (0, c−1, c) and (0, c−2, c−1) (c = 4: (0,3,4), (0,2,3); c = 7: (0,6,7), (0,5,6)); in §5,
  runners 2 and 3 on the same lap (0, j, j).
- **The two families.**
  - **M6 (meeting windows):** at each meeting time k/D runners 2 and 3 are both on the subject (laps k(c−1), kc). They
    are clear together just after it on J⁺ₖ = [k/D + 1/(6v₂), k/D + 5/(6v₃)], of length (4c−5)/(6c(c−1)D) > 0, and just
    before it on the mirror J⁻ₖ. Runner 1 must be clear on a sub-window (its position there is k v₁ mod D, an orbit point),
    and runners 4, 5 are folded by `window_two`.
  - **M5 (pair windows):** runners 2 and 3 (within D ≤ v₁ of each other) on one lap j, clear on
    [(j + 1/6)/v₂, (j + 5/6)/v₃]; runner 1 on a sub-window; runners 4, 5 by `window_two`.
- **Coverage.** Primitive §5/§6 ≤ 26 (11,861 sets): family 8,381, else four-block fold 3,447, else cluster box 6, rest 27.
  Random §5/§6 sets ≤ 400 (1,500): family 1,339, fold 161, rest 0.
- **The 27 left** are all at small ratios (x₄ ≤ 6, x₅ ≤ 13): patterns (1,3,4,5,X) for X = 8..13, (1,4,5,6,X),
  (1,5,6,7,8), (1,8,9,10,16/18), (1,9,10,11,18), (1,10,11,12,17), and multiples (2,6,8,10,X), (3,9,12,15,X),
  (2,5,7,9,14/15), (2,8,10,12,23/25). Each pattern has finitely many X in [.., 300]. They sit near the tight set
  (1,3,4,5,9) and near clusters; the second-lap box (0,0,0,0,1) closes ten of them and other small boxes most of the
  rest (`s56_rest_corners_v1.out`).
- **Reading** [observation]. A native §5/§6 route has three parts: (1) the families M6 and M5 (windows next to the
  meeting times or with runners 2 and 3 on one lap, runner 1 placed by its orbit residue k v₁ mod D, runners 4, 5 folded),
  parametric in k or j; (2) the four-block fold; (3) a bounded region of small ratios near the tight set and clusters,
  where a cell certificate with boxes applies, as in §8, with the corner lemma at the tight point. Owed for a proof:
  that (1) or (2) applies to every set outside the bounded region — a statement about choosing k (or j) by the orbit of
  v₁ mod D — and the bounded certificate.

## E92 — The §5/§6 window lemmas in Lean; which k (or j) works (2026-10-16)

Owner: *"Prove the M6 and M5 window lemmas in Lean and work on the coverage argument: which k (or j) works, from the
orbit of v1 mod D, outside the bounded region."* `S6Meeting_v1.lean` (`.out`; axioms `[propext, Classical.choice,
Quot.sound]` for all three) [PROVED]; `s6_coverage_v1.{py,out}`, `s5_coverage_v1.{py,out}`.
- **`orbit_residue`**: if D ∤ v₁ there is k with k v₁ mod D ∈ [D/6, 5D/9]. Proof: g = gcd(v₁, D) < D; Bézout gives m with
  v₁ m ≡ g; if 18g ≤ 7D take k = q m with q = ⌊D/(6g)⌋ + 1 (then qg ∈ (D/6, D/6 + g] ⊆ [D/6, 5D/9]); otherwise g | D forces
  g = D/2 and k = m gives D/2.
- **`s6_meeting_uniform`** (M6, whole numbers): v₂ = cD, v₃ = (c+1)D, D ∤ v₁, 3v₁ < v₃ and 4v₂v₃ ≤ v₄(5v₂ − v₃) ⇒ lonely.
  At k from `orbit_residue`, the window [k/D + 1/(6v₂), k/D + 5/(6v₃)] has runners 2, 3 on laps ck, (c+1)k (clear), runner 1
  reading r/D + v₁s with r/D ∈ [1/6, 5/9] and v₁s ≤ 5/18 (from 3v₁ < v₃), and runners 4, 5 by `window_two_uniform`.
  Which k: the one whose orbit residue k v₁ mod D lands in [D/6, 5D/9] — the global-isolation orbit of v₁ mod D.
- **`s5_pair_window`** (M5): runners 2, 3 on lap j ≥ 0 clear on [(j+1/6)/v₂, (j+5/6)/v₃]; runner 1 on lap m clear on a
  sub-window [a, b] of length ≥ 2/(3v₄) ⇒ lonely.
- **§6 coverage** (all primitive §6 sets ≤ 34: 18,463; random §6 ≤ 1000: 2,000): `s6_meeting_uniform` closes 14,157 and
  1,810; the meeting window with `window_two`'s sharp conditions 2,247 and 107; a four-block fold 2,059 and 83; rest 0.
  Where the uniform condition fails, runner 4 is close to runner 3: (v₄ − v₃)/D ≤ 0.7 in every case listed.
- **§5 coverage** (primitive §5 ≤ 30: 13,647; random ≤ 1000: 2,000): uniform pair window with the explicit lap
  j₀ = ⌊v₂/(2v₁)⌋ (runner 1 near 1/2) 3,258 and 1,353; with another j 2,800 and 225; sharp 2,243 and 167; four-block fold
  5,310 and 255; cluster box 7 and 0; rest 29 (the bounded small-ratio set of E91) and 0.
- **Which j for §5** [argued, not formalised]: in runner 1's first band [1/(6v₁), 5/(6v₁)] take j = ⌈v₂/(6v₁) − 1/6⌉; the
  pair window then lies inside the band when v₂ ≥ (5/2)v₁, with length at least (1/2 − D/v₂)/v₃. The regime
  2v₁ < v₂ < (5/2)v₁ and short windows go to the sharp conditions or the fold.
- **Owed:** a proved existence statement for the cases the uniform conditions miss (runner 4 within 0.7D of runner 3 in §6;
  short pair windows in §5), and the bounded small-ratio certificate.

## E93 — The near-runner case: §6 by a meeting-window fold (a 2D orbit); §5 short windows (2026-10-16)

Owner: *"Yes"* (to "the near-runner case or the bounded certificate"; taken as the recommended option, near-runner first).
Observation only. `s6_near_v1.{py,out}`, `s6_near_v2.{py,out}`, `s5_short_v1.{py,out}`.
- **§6, runner 4 near runner 3** (the 4,306 primitive §6 sets ≤ 34 where `s6_meeting_uniform`'s condition fails): all
  4,306 are closed by a **meeting-window four-block fold**: for some k ≤ 2D, on the window just after (or before) k/D,
  runners 2, 3 are clear (laps ck, (c+1)k), runners 1 and 4 are clear on a common sub-window, runner 5 is folded alone.
- **As a 2D orbit.** At k/D runner 1's phase is p₁ = (k v₁ mod D)/D and runner 4's is p₄ = (k δ mod D)/D, δ = v₄ − v₃.
  The fold works when (p₁, p₄) lies in a region fixed by the ratios (runner 1 sweeps less than 5/18 across the window,
  runner 4 about (4c−1)/(6c) of a lap). Successful k by sixths of (p₁, p₄): (1,1) 564, (3,1) 476, (2,1) 336, (2,2) 312,
  … — spread over many cells. A product box [1/6, 5/9] × [0, b] is not the region: the orbit misses it for small D
  (e.g. (1,2,4,5,X), D = 2) and the fold fails at some of its points (b = 1/4: 972 of 4,054). So the proof is the §7 shape:
  the orbit k ↦ (k v₁, k δ) mod D must meet a ratio-dependent region, as in `s7_main_route` (2D global isolation) — owed.
- **§5 short pair windows** (7,589 primitive §5 sets ≤ 30 not closed by the uniform pair window): a pair-window four-block
  fold (runners 2, 3 on one lap j; runners 1 and 4, or 1 and 5, clear on a sub-window; the other folded) closes 6,042; the
  1,547 left include the bounded small-ratio set (E91) and need other blocks or the sharp conditions (E92 counts).
- Not started this round: the bounded small-ratio certificate.

## E94 — The §6 near-runner region, and the orbits that miss it (2026-10-16)

Owner: *"Yes"* (taken as the recommended option: the §6 orbit proof). Observation and derivation. `s6_region_v1.{py,out}`.
- **Derived region.** Window after k/D: s ∈ [1/(6v₂), 5/(6v₃)], length ℓ; runner 4 sweeps λ₄ = v₄ℓ ∈ [1/2, 2/3) in the
  near-runner case (λ₄ ≥ 2/3 is exactly `s6_meeting_uniform`'s condition); runner 5 needs a stretch where runner 4 is clear
  of reading length μ = v₄/(3v₅) < 1/3. So runner 4 works when p₄ lies in an arc A = [1/6 − λ₄ + μ − v₄s₀, 5/6 − μ − v₄s₀]
  (mod 1) of length 2/3 + λ₄ − 2μ ≥ 1/2 (observed 0.54–0.66+), and runner 1 is clear across the window when
  p₁ ∈ [1/6, 5/9]; before k/D the mirror arc A′ with p₁ ∈ [4/9, 5/6]. Region: [1/6, 5/9] × A ∪ [4/9, 5/6] × A′, area at least
  7/36 on each side. A and A′ cover the whole circle in 2,196 of the 4,306 near-runner sets.
- **Orbit test** (near-runner primitive §6 ≤ 34): the orbit k ↦ (k v₁, k δ) mod D meets the region in 4,131 of 4,306.
- **The 175 misses** are degenerate orbits: direction λ = δ·v₁⁻¹ ≡ ±1 (mod D) — runner 4's phase equals runner 1's, or its
  negative, at every meeting time (e.g. (1, w, 2w, 2w+1, X) with v₁ = δ = 1, for w = 3, 4, 5, …) — in 112; gcd(v₁, D) > 1
  (a coarse orbit for runner 1) in 54; λ = ±2 in 2; others small. All 175 are closed by the meeting-window fold (E93)
  with runner 1 clear on only part of the window, which the simple region leaves out.
- **Reading** [observation]. This is the §7 shape again: a generic orbit meets a region of fixed area (here ≥ 7/36), and
  the exceptions are short-step orbits (direction ±1, ±2) and coarse ones, as `s7_main_route` found G₄ and G₇. Proof plan:
  (1) for directions other than ±1 (and ±2) and orbit size above a bound, the orbit meets [1/6, 5/9] × A — a 2D
  global-isolation statement, provable like `s7_main_route`; (2) the degenerate directions, where runners 1 and 4 move
  together at meeting times, by a direct argument with runner 1 partly clear; (3) small D and coarse orbits by finite or
  explicit checks. Not yet in Lean.

## E95 — §6, part (1) proved: generic orbits meet the region (2026-10-16)

Owner: *"Prove part (1): for orbit directions other than plus or minus 1 and 2, and orbit size above a bound, the orbit
meets the region; follow s7_main_route."* `S6Generic_v1.lean` (`.out`; axioms `[propext, Classical.choice, Quot.sound]`
for all three) [PROVED]; `s6_coverage_v2.{py,out}`.
- **`ap_meets_half_arc`**: for D ≥ 15, 2 ≤ |λ|, 2|λ| ≤ D and any x₀, some integer j ∈ [D/6, 5D/9] has λj/D − x₀ in
  [m, m + 1/2] for an integer m. Proof: if every point were in an upper half-interval, steps of |λ|/D ≤ 1/2 cannot jump
  between upper halves (`floor_eq_of_upper`), so all lie in one, span < 1/2; but the span is |λ|(j₁ − j₀)/D ≥ 1/2 when
  D ≥ 15. The orbit is a progression here, so the region argument needs no case table (unlike `s7_main_route`'s parallelogram,
  whose shape is fixed and was checked by `decide` for n ≤ 35): the runner-4 condition is a half arc in any position.
- **`s6_window_fold`**: at a meeting time with runners 2, 3 on the subject, runner 1 at phase p₁ ∈ [1/6, 5/9] and runner 4
  at phase p₄ whose sweep across the window meets its band in a stretch of length ≥ v₄/(3v₅), runner 5 is folded and the
  arrangement is lonely.
- **`s6_generic`** (whole numbers): v₂ = cD, v₃ = (c+1)D, 3v₁ < v₃, v₃ < v₄ ≤ v₅, gcd(v₁, D) = 1, D ≥ 15, and λ with
  v₄ ≡ λv₁ (mod D), 2 ≤ |λ| ≤ D/2 ⇒ lonely. The half arc comes from λ₄ = v₄ℓ ≥ 1/2 and μ = v₄/(3v₅) ≤ 1/3; k = j·v₁⁻¹ mod D.
  λ = ±2 is included (D ≥ 15 suffices for it).
- **Coverage of the two proved §6 theorems** (`s6_meeting_uniform` ∪ `s6_generic`): all primitive §6 sets ≤ 40 (40,075):
  uniform 31,184, generic 497; left: D < 15 5,936, gcd(v₁, D) > 1 2,389, λ = 1 63, λ = −1 6. Random §6 ≤ 3,000 (3,000):
  uniform 2,747, generic 168; left: gcd > 1 82, D < 15 3.
- **Owed for §6:** (2) λ ∈ {0, ±1} (runners 1 and 4 in step at the meeting times), (3) gcd(v₁, D) > 1 (runner 1's orbit
  coarse: it moves on multiples of g/D) and D < 15 (finitely many orbit shapes per D, so a finite check like
  `check_orbits` is available there).

## E96 — §6 open cases checked: small D, and the degenerate directions (2026-10-16)

Owner: *"Lets check both"* (D < 15 by a finite check; directions 0, ±1). Observation only. `s6_small_v1.{py,out}`,
`s6_degenerate_v1.{py,out}`.
- **D < 15, worst case over the arc's position.** For each D < 15 and residues (a, b) = (v₁, v₄ mod D), D ∤ a: the runner-4
  phases at the k with runner 1 in [1/6, 5/9] meet every closed half arc (all circular gaps ≤ 1/2) in 580 of 910 classes;
  330 classes fail with both the after and the before window (2 at D = 2, 6 at D = 3, …, 62 at D = 14). So for small D the
  orbit is too sparse for a position-free argument: the arc's actual position (fixed by the ratios v₄/v₂, v₄/v₃, v₄/v₅)
  must enter, i.e. a ratio-dependent check per residue class, or other statements (for small D and large c, runners 2, 3,
  4 are within D of each other at speed about cD, a cluster: the cluster-box family of E88 is the candidate).
- **Directions 0, ±1** (gcd(v₁, D) = 1, not uniform, primitive ≤ 60): λ = −1: 3,529 sets, all meet the region (after or
  before window); λ = 1: 5,580 meet it, 355 need the exact meeting fold with runner 1 only partly clear; λ = 0: none
  (outside the uniform case).
- **The 355 all have v₄ = v₃ + v₁ exactly** (a sum relation, mostly c = 1, i.e. v₃ = 2v₂: e.g. (1,3,6,7,X), (1,4,8,9,X)).
  Then runner 4 reads runner 3's reading plus runner 1's at every instant, so at a meeting time runner 4 reads exactly what
  runner 1 reads; on the window after it, x₄ = x₁ + x₃ with x₃ rising from v₃/(6v₂) to 5/6. A dedicated sum-relation
  lemma (x₁, x₃ and x₁ + x₃ all in the band on a sub-window, runner 5 folded) is the natural closure — like BHK's use of
  v₁ + v₂ = v₃ in §5.
- **Owed:** the sum-relation lemma (v₄ = v₃ + v₁), λ = −1 and λ = 1 via the two-window region (a progression argument on
  the diagonal), gcd(v₁, D) > 1, and small D with the actual arc positions.

## E97 — The sum-relation lemma (v₄ = v₃ + v₁) (2026-10-16)

Owner: *"word"* (go ahead with the sum-relation lemma). `s6_sum_v1.{py,out}`, `s6_sum_v2.{py,out}`; `S6Sum_v1.lean`
(`.out`; axioms `[propext, Classical.choice, Quot.sound]`) [PROVED].
- **Observation.** On the §6 sets ≤ 60 with v₄ = v₃ + v₁ (5,574 not uniform), the working runner-1 phases p at meeting
  times spread over most of [0, 29/36] (after) and [0, 34/36] (before); no single small interval.
- **Derived window.** At T = k/D runner 4 reads what runner 1 reads (v₄T = v₃T + v₁T, runner 3 on the subject). After T,
  where runner 3 reads x₃ ∈ [7/6 − p, 5/6]: runner 4 reads x₃ + p + v₁s, one lap on and inside the band; runner 1 reads
  p + v₁s ≤ 5/6 if p ≤ (5/6)(1 − v₁/v₃); runner 2 reads x₃·v₂/v₃ ≥ x₃/2 (c ≥ 1); runner 5 is folded if
  (p − 1/3)/v₃ ≥ 1/(3v₅). So any k with p ∈ I = [1/3 + v₃/(3v₅), (5/6)(1 − v₁/v₃)] works.
- **`s6_sum_window`** proves exactly this (reals, readings at T given as integers plus p; hypotheses v₂ ≤ v₃ ≤ 2v₂).
- **Coverage** (all §6 sets ≤ 60 with v₄ = v₃ + v₁: 13,762): some k has p ∈ I in 9,731, and the exact fold works at that k
  in all 9,731 (0 failures); of the 4,031 without such k, 3,623 are closed by `s6_meeting_uniform`; 408 remain, all with
  small D (e.g. (1,4,8,9,X), D = 4; (1,5,10,11,12), D = 5) where the orbit k/D is too coarse for I, or with v₃ close to 3v₁
  and v₅ close to v₄, where I is empty (I's length is (5/6)(1 − r) − 1/3 − v₃/(3v₅), r = v₁/v₃; negative near r = 1/3,
  v₅ = v₄) — a bounded region of ratios.
- **Owed:** the choice of k (with gcd(v₁, D) = 1, a j/D in I exists once D·|I| ≥ 1); the λ = ±1 two-window argument in
  Lean; the 408 go with small D and the bounded region.

## E98 — The D ≥ 15, gcd 1 branch: what is proved, and the λ = ±1 margin (2026-10-16)

Owner: *"Finish the D >= 15, gcd 1 branch in Lean: the choice of k for the sum lemma and the lambda = plus or minus 1
two-window argument."* `S6Branch_v1.lean` (collects S6Meeting/S6Generic/S6Sum; `.out` 0 errors; axioms
`[propext, Classical.choice, Quot.sound]` throughout) [PROVED]; `S6Sum_v1.lean` updated; `s6_branch_v1.{py,out}`,
`s6_diag_margin_v1.{py,out}`, `s6_diag_cont_v1/v2.{py,out}`.
- **Proved:** `lam_zero_uniform` (λ = 0 ⇒ v₄ ≥ (c+2)D ⇒ the uniform condition); `exists_grid_point` (gcd 1 and an
  interval of length ≥ 1/D in [0, 1) contain some (k v₁ mod D)/D); `s6_sum` (whole numbers: v₄ = v₃ + v₁, gcd 1, D|I| ≥ 1
  ⇒ lonely); `s6_window_fold_before` (the window before the meeting time, by reflection t ↦ −t: runner 1 in [4/9, 5/6]);
  **`s6_off_unit`**: §6 with D ≥ 15, gcd(v₁, D) = 1 and direction λ ≠ ±1 (v₄ ≡ λv₁, 2|λ| ≤ D) ⇒ lonely.
- **Data** (D ≥ 15, gcd 1, primitive ≤ 60: 19,439 sets): uniform 4,458, generic 13,232, sum lemma 1,182, diagonal region
  λ = −1 507, λ = 1 60; rest 0. Random ≤ 3,000: uniform 2,656, generic 344.
- **The λ = ±1 guarantee, over the continuous parameters.** Runner 4's arcs depend only on c, q₄ = v₄/v₃ (near-runner:
  q₄ < 4c/(4c−1)) and μ = v₄/(3v₅) ∈ (0, 1/3]; a grid point j/D lies in the usable set U if U has an interval of length ≥ 1/D.
  Grid search (c ≤ 40 and large c; 400 × 200 in (q₄, μ)): λ = −1: smallest longest interval 1/6 (≥ 1/15 with room);
  λ = 1, c ≥ 3: 0.0909 (≥ 1/15); λ = 1, c ≤ 2: there v₁ < D so δ = v₁ (the sum relation), and the usable set U ∪ I has
  smallest longest interval 0.0561 at c = 1, q₄ ≈ 1.199, μ → 1/3 — below 1/15 = 0.0667, above 1/18. So the simple union
  argument gives every D ≥ 18 there, and D = 15, 16, 17 with c ≤ 2 need a separate look.
- **Owed for the branch:** the λ = ±1 statement itself in Lean — a certificate over (c, q₄, μ) that the usable set has an
  interval of length ≥ 1/15 (≥ 1/18 for c ≤ 2), like §8's — and the D = 15–17, c ≤ 2, λ = 1 corner.

## E99 — §6 branch D ≥ 15, gcd(v₁, D) = 1: proved, every direction (2026-10-16)

Owner: *"Build the lambda = plus or minus 1 certificate over (c, q4, mu), with a separate check for D = 15 to 17 at c <= 2,
and wire the branch theorem."* `s6_lam_cert_v1.{py,out}`, `s6_lam_small_v1.{py,out}`, `s6_lam_lean_gen_v1..v3.py`;
`S6Branch_v1.lean` (`.out`: 0 errors; no `sorry`/`native_decide`/`admit`; axioms `[propext, Classical.choice, Quot.sound]`
for every theorem) [PROVED].
- **Certificate** (parameters U = v₃/v₂ = (c+1)/c, Q = v₄/v₃ ∈ [1, 4/(5−U)] in the near-runner case, M = v₄/(3v₅) ≤ 1/3;
  a cell is closed by the window after or before the meeting time with offset m, or by the sum lemma, on an interval
  [a, a + L] of runner-1 phases, checked at worst corners). Trees: λ = −1, all c: one leaf (after, m = 0, a = 1/6, L = 1/15);
  λ = 1, c ≥ 3: one leaf (the same); λ = 1, c = 2: 4 leaves (L = 1/15); λ = 1, c = 1: 12 leaves with L = 1/20 (so D ≥ 20).
  The c = 1 tree fails at L = 1/15 and 1/18 (the corner Q ≈ 1.2, M → 1/3 of E98).
- **Small cases.** λ = 1, c = 1, D = 15..19: v₁ < D forces δ = v₁; 37 non-uniform coprime cases, each closed at a
  grid point j/D at the largest M = v₄/(3(v₄+1)) (the conditions are monotone in M): 15 by the sum lemma, 22 by the
  window after or before. (The request named D = 15–17 at c ≤ 2; c = 2 needed no small cases, and c = 1 needed D up to 19.)
- **Lean.** `readings_at` (readings at k/D for k v₁ ≡ j), `exists_j`, `close_after`, `close_before`, `close_sum`;
  **`s6_unit_dir`** (λ = ±1, the case tree generated from the certificate and the 37 cases, plus `hδ2`: λ = 1 and c ≤ 2
  force v₄ = v₃ + v₁); **`s6_branch`**: §6 (v₂ = cD, v₃ = (c+1)D, c ≥ 1, 3v₁ < v₃, v₃ < v₄ < v₅) with D ≥ 15 and
  gcd(v₁, D) = 1 ⇒ lonely — uniform, or λ from v₄·v₁⁻¹ mod D (representative in (−D/2, D/2]): λ = ±1 by
  `s6_unit_dir`, otherwise `s6_off_unit`.
- **Left in §6:** D < 15, and gcd(v₁, D) > 1.

## E100 — 2026-10-16 — §6 native branch wired into the order-six dispatch

- **Tree:** new module `LRC/Spec/OrderSixSixNativeN.lean` (namespace `LRC.S6Native`): the content of
  `S6Branch_v1.lean` plus `lonely_6_native_branch`, which takes §6's hypotheses as the dispatch states them
  (v₃ − v₂ ∣ v₃, 3v₁ < v₃) and applies `s6_branch` with c = e − 1 where v₃ = e·D.
- **Dispatch:** `OrderSixWholeN.lean` §6 now splits on `15 ≤ v₃ − v₂ ∧ Coprime v₁ (v₃ − v₂)`: native branch
  when it holds, BHK's `lonely_6` otherwise.
- **Check** (`S6Native_wiring_v1.out`): order 3–7 targets build (8334 jobs); `lonely_6_native_branch`,
  `lonely6_of_lt` and `lonelyRunnerAtN_three` … `_seven` all depend on `[propext, Classical.choice, Quot.sound]`.
  The proof term of `lonely6_of_lt` references `lonely_6_native_branch`, `lonely_6`, `lonely_7_native` and
  `lonely_8_native`. No `sorry`, `native_decide` or `admit` in the new module.
- **Commit:** nested repo `8f77b2d`. Not pushed.
- **Order six's proof of record now:** §2, §7, §8 native; §6 native for D ≥ 15 with gcd(v₁, D) = 1; §6 with
  D < 15 or gcd(v₁, D) > 1, and §5, still BHK.

## E101 — The rest of §6 (D < 15, or gcd(v₁, D) > 1): observation (2026-10-16)

Owner: *"Start the rest of §6: D < 15 and gcd(v1, D) > 1. Observation first."* Observation only; nothing new in Lean.
`s6_rest_v1..v8.{py,out}`. Region left by the dispatch: §6 with D ∤ v₁ and (D < 15 or g = gcd(v₁, D) > 1).
- **Every set tested is closed by the four meeting-window statements** (`s6_rest_v1/v2`): primitive ≤ 50 (109,217 sets)
  uniform 89,874, region 19,019, sum lemma 282, exact meeting fold 42, rest 0; random ≤ 2,000 (2,000) uniform 1,880,
  region 120, rest 0. `s6_meeting_uniform` already needs only D ∤ v₁, so the uniform part is proved.
- **gcd > 1, g ∤ v₄** (`s6_rest_v3`, 8,739 random non-uniform sets, g up to 30, D/g up to 79): δ = v₄ − v₃ is not a
  multiple of g (g | v₃). At the k = k₀ + (D/g)i, i < g, which share one runner-1 phase j/(D/g) ∈ [1/6, 5/9], runner 4's
  phases kδ/D form a coset of ⟨δ/g⟩ mod 1, of order h = g/gcd(δ, g) ≥ 2, so consecutive points are ≤ 1/2 apart. The
  after-window arc A has length 2/3 + λ₄ − 2μ ≥ 1/2 (λ₄ ≥ 1/2 from v₃ ≤ 2v₂, μ ≤ 1/3), so the coset meets it: 8,739 of
  8,739, with h ranging over 2–30. No bound on D is used. This is `s6_window_fold` with a coset in place of an orbit.
- **gcd > 1, g | v₄**: g divides v₁…v₄, and the meeting-window data at k/D are those of (v₁, …, v₄)/g, v₅/g at D′ = D/g
  with gcd(v₁/g, D′) = 1; the region test agrees on the set and its reduction (2,522 of 2,522). With D′ ≥ 15 the reduced
  set is closed by the proved branch's cases (generic 2,019, diagonal 133, sum 6, rest 0). Its v₅/g is rational, so using
  `s6_branch` here needs v₅ real (or a restatement); D′ < 15 joins the next case.
- **Coprime, D < 15** (`s6_rest_v4..v6`): the orbit at meeting times is {(j, λj)} mod D, so the class is (D, λ), 104
  classes. Runner 4's arcs depend on U = (c+1)/c, Q = v₄/v₃ and M = v₄/(3v₅) only. Over a grid (c ∈ {1..8, 20, 100,
  1000}, 80 Q × 40 M) the region closes every point in 89 classes; the 15 others are λ = 1 for every D, plus (5, 3) and
  (7, 5), both λ ≡ −2. **With integrality** (δ ≥ 1, Q = 1 + δ/((c+1)D), δ ≡ λv₁): for c ≤ 30, failures occur in only
  39 cells (D, c, δ, v₁ mod D): c = 1: 27, c = 2: 8, c = 3: 3, c = 4: 1, none for c ≥ 5; λ = 1 in 37 cells, λ = −2 in 2
  ((7, 1, 2, 6) and (7, 1, 3, 2)). D = 2 has none: its failures need Q − 1 below 1/((c+1)D).
- **The cells are finite** (`s6_rest_v7/v8`): v₁ < v₃/3 restricts v₁ to finitely many values in its class, and M ≥ M_min
  bounds v₅. 125 integer sets: sum lemma 113, meeting fold 10, region 2. Since the sum lemma's I = [1/3 + v₃/(3v₅), …]
  and the meeting fold's condition v₅|W| ≥ 1/3 both get harder as v₅ decreases, v₅ = v₄ is each cell's worst point.
  There all 41 (cell, v₁) pairs close: sum lemma 31 (v₁ = δ, so v₄ = v₃ + v₁) and meeting fold 10 (v₁ = δ + D, e.g.
  (8, 21, 28, 29, ·), and the λ = −2 cells (2, 7, 14, 17, ·)). This covers every v₅ > v₄, including the rational v₅/g
  from the reduction.
- **Reading** [observation]. The rest of §6 has the same shape as the proved branch, with one new piece:
  1. uniform: proved;
  2. g ∤ v₄: a coset of order ≥ 2 meets a half arc (short proof from `s6_window_fold`);
  3. g | v₄: reduce to D′ = D/g;
  4. coprime D < 15: 104 direction classes, a region certificate over (c, Q, M) with integer δ, like E99's λ = ±1
     certificate, plus 41 finite pieces closed by the sum lemma or the meeting fold at M = 1/3.
- **Not established here:** the region results are grid samples, not a certificate; c was scanned up to 30 and no failing
  cell appears for c ≥ 5, but large c needs an argument; the g | v₄ reduction needs `s6_branch`'s v₅ to be real.

## E102 — The coset case and the E < 15 certificate, proved (2026-10-16)

Owner: *"Lets continue with coset case and the d <15 cert"*. `S6Coset_v1.lean` (`.out`) and `S6Small_v1.lean` (`.out`):
0 errors, no `sorry`/`native_decide`/`admit`, axioms `[propext, Classical.choice, Quot.sound]` for every theorem below
[PROVED]. Prototype scripts: `s6_small_cert_v1.{py,out}`, `s6_small_fold_v1.{py,out}`.
- **`step_meets_half_arc`**: a progression with step σ ∈ (0, 1/2] meets every closed half arc: n = ⌈(⌈x₀⌉ − x₀)/σ⌉.
- **`s6_coset`** (§6, D ∤ v₁, g = gcd(v₁, D) ∤ v₄, no bound on D): the meeting times k = k₀ + (D/g)·i·n hold runner 1 at
  the orbit residue of `orbit_residue` (v₁·(D/g) = (v₁/g)·D), while runner 4 advances by i·v₄/g ≡ d/g (mod 1) per step,
  where v₄ i ≡ d = gcd(v₄, g) (mod g) by Bézout and d < g, so d/g ≤ 1/2. The half arc then comes from
  `step_meets_half_arc`, and `s6_window_fold` closes.
- **`s6_small`** (§6, D ∤ v₁, g | v₄, E = D/g < 15; g = 1 is coprime D < 15): uniform → `s6_meeting_uniform`; else
  near-runner, written as the integer inequality 4cδ < (c+1)E + δ with δ = (v₄ − v₃)/g. `readings_E` gives readings j/E
  and l·j/E at the meeting times, with l ≡ δ·(v₁/g)⁻¹ (mod E). Every closing condition is an upper bound on
  M = v₄/(3v₅), so all checks are made at M = 1/3.
  - **c ≥ 5** (`bigAll`, `decide +kernel`): for each class (E, l), E < 15, either 6E ≤ 19·gcd(l, E) — then
    gcd(l, E) | δ and the near-runner inequality give c < 5, a contradiction — or one window (after/before, j, lap)
    closes the whole box Q ≥ 1, QU ≤ 24/19 (QU ≤ 24/19 follows from near-runner with c ≥ 5). This is 28 empty classes
    and 76 one-leaf classes (prototype count).
  - **c ≤ 4** (`smallAll`, `decide +kernel`): every point (E, c, δ, a = v₁/g) with the near-runner bound, 3a < (c+1)E and
    gcd(a, E) = 1 is closed at its exact Q, QU by a window (956 points in the prototype), the sum lemma (31; δ = a means
    v₄ = v₃ + v₁) or one of ten listed sub-window folds (`closeF`, witnesses from `s6_small_fold_v1.py`; runner 5 folded
    via v₅ ≥ v₄).
  - Soundness: `region_sound`, `sum_sound`, `fold_sound` (readings abstracted as `Readings`), with real-speed closers
    `closeA`, `closeB`, `closeF`.
- **§6 coverage now proved natively** (none of it wired in yet): D ≥ 15 with gcd(v₁, D) = 1 (`s6_branch`, in the dispatch);
  g ∤ v₄ (`s6_coset`); g | v₄ with D/g < 15 (`s6_small`). **Left:** g > 1, g | v₄, D/g ≥ 15. The readings there are those
  of the coprime branch at modulus D/g (E101), so `s6_branch` restated through `readings_E` is the candidate.

## E103 — §6 fully native and wired into the order-six dispatch (2026-10-16)

Owner: *"Close the last §6 case (g > 1, g | v4, D/g >= 15) by restating s6_branch through readings_E, then wire all of
§6 in."* `S6All_wiring_v1.out`, `s6_small_cert_v2.{py,out}`. Nested repo commit `aea3db2`; not pushed.
- **The last case went through scaling rather than through `readings_E`.** At speeds (v₁, …, v₄)/g (whole numbers,
  gcd(v₁/g, E) = 1) and v₅/g (real), the instant scales by 1/g. `s6_branch` used integrality of v₅ only in its explicit
  cases at D = 15..19, c = 1 (via M ≤ v₄/(3(v₄+1))). So in `OrderSixSixNativeN.lean` v₅ is now real in
  `s6_meeting_uniform`, `s6_generic`, `s6_off_unit`, the closers, `s6_unit_dir` and `s6_branch`. The hypothesis
  `20 ≤ D ∨ v₄ + 1 ≤ v₅` is used only in the D < 20 explicit cases. `lonely_6_native_branch` supplies it from integer v₅.
- **`s6_scaled`**: g | v₄, D/g ≥ 20 ⇒ `s6_branch` on the reduced speeds with `Or.inl`.
- **E = 15..19**: the E < 15 certificate extends unchanged in method (`s6_small_cert_v2`: c ≥ 5, 150 one-leaf classes
  and 39 empty; c ≤ 4, 2,646 window points, 49 sum, the same 10 folds). In Lean `bigAll`/`smallAll` range E < 20,
  δ, v₁/g < 32; `s6_small` now takes D/g < 20.
- **Tree:** new `LRC/Spec/OrderSixSixRestN.lean` holds `s6_coset`, `s6_small` (E < 20), `s6_scaled`, `s6_all` (§6 for
  every D ∤ v₁: g ∤ v₄ coset; g | v₄ small or scaled) and `lonely_6_native` (dispatch form). `OrderSixWholeN.lean`
  §6 is now one line: `S6Native.lonely_6_native`. BHK's `lonely_6` is kept in the tree but no longer used by
  `lonely6_of_lt`.
- **Check** (`S6All_wiring_v1.out`): order 3–7 targets build (8,335 jobs). `s6_coset`, `s6_small`, `s6_scaled`,
  `s6_all`, `lonely_6_native`, `lonely6_of_lt` and `lonelyRunnerAtN_three` … `_seven` all depend on
  `[propext, Classical.choice, Quot.sound]`. The `LRC` constants of `lonely6_of_lt` are `Lonely6`, `lonely_8_native`,
  `S7.Named.lonely_5`, `lonely_6_native` and `lonely_7_native`. No `sorry`/`native_decide`/`admit`/`unsafe` in either §6
  module.
- **Order six's proof of record now:** §2, §6, §7, §8 native; §5 (`lonely_5`, Proposition 11 at named instants) is the
  remaining BHK case.

## E104 — §5 natively: observation (pair windows, four-block fold) (2026-10-16)

Owner: *"Start §5 natively: observation first, pair windows and the four-block fold, as for §6."* Observation only.
`s5_obs_v1..v4.{py,out}`. §5: D = v₃ − v₂ divides v₁, 3v₁ < v₃; k = v₁/D (BHK split: k = 1 Proposition 11 part 1,
k = 2 part 2, k ≥ 3 Case 5.1 — `OrderSixSecFiveN.lean` header).
- **The relation.** For integers, x₁ ≡ k(x₃ − x₂) (mod 1) at every instant: runner 1 reads k times the 2–3 gap.
  k = 1 is the sum relation x₃ = x₁ + x₂ (v₃ = v₁ + v₂).
- **Pair windows.** Runners 2, 3 on one lap j are clear together on P_j = [(j+1/6)/v₂, (j+5/6)/v₃], nonempty iff
  6jD ≤ 4v₂ − v₃, so all lie before the first meeting 1/D. Across them runner 1's phase is the progression j·v₁/v₂
  (step kD/v₂), and runner 4's is j·v₄/v₂.
- **Coverage** (`s5_obs_v1`; A uniform pair window, B sharp `window_two`, C pair-window four-block fold, D other
  four-block fold, E cluster box, F none):

  | k | primitive ≤ 36 (32,292) | random ≤ 2,000 (2,000) |
  |---|---|---|
  | 1 | A 5,140, B 1,824, C 6,357, D 3,139, E 9, F 34 | A 135, B 37, C 133, D 59 |
  | 2 | A 4,044, B 1,367, C 1,346, D 123 | A 111, B 31, C 45, D 4 |
  | ≥ 3 | A 6,520, B 1,695, C 681, D 13 | A 1,344, B 82, C 19 |

  Closing j: for k ≥ 3, in the first quarter of the range with runner 1 in [1/6, 1/3) (mostly); for k = 1, spread over
  the first three quarters.
- **The explicit lap** j₀ = ⌈v₂/(6v₁) − 1/6⌉ (`s5_obs_v4`), where runner 1 enters its first band at the start of P_{j₀}:
  for k ≥ 2 every uniform pair-window closure happens at j₀ (k = 2: 4,044 of 4,044; k ≥ 3: 6,520 of 6,520; random:
  111 and 1,344). B/C sets have runner 4 near runner 3: v₄/v₃ ≤ 1.25 (k ≥ 3; median 1.07) and ≤ 1.47 (k = 2; median
  1.12). This is the near-runner case of §6 (E93), here on the pair-window progression. For k = 1, 4,951 at j₀ and 189
  at another j.
- **What pair windows miss** (`s5_obs_v2`, first closing four-block fold). k = 1:
  - runner 3 folded alone (block {1, 2, 4, 5}), runner 1 on its first lap: 1,415;
  - block {1, 2, 3, 4/5} with runner 3 one lap ahead of runner 2 (m₃ − m₂ = 1) and runner 1 on lap 0: 1,356 (and 102
    on lap 1);
  - runner 2 folded: 216.

  k = 2: 123, spread over runner 3 folded (49), runner 4 folded with m₃ − m₂ = 1 and runner 1 on lap 1 (38), and others.
  k ≥ 3: 13.
- **Cluster box family** (k = 1): (1, w, w+1, w+2, w+3), w = 8, 11, …, 32 (w ≡ 2 mod 3): no fold up to 3/v₁; the box
  (0, m, m, m, m) closes them.
- **The 34 left (F)** (`s5_obs_v3`): every one is closed by a lap box with runner 1 on lap 0 (e.g. (0,0,0,0,1),
  (0,1,1,1,3), (0,1,1,2,5)). They fall into eleven patterns: (1,3,4,5), (1,4,5,6), (1,5,6,7), (1,8,9,10), (1,9,10,11),
  (1,10,11,12), (2,5,7,9) and multiples (2,6,8,10), (2,8,10,12), (3,9,12,15), (4,10,14,18), each with finitely many v₅.
  This is the bounded small-ratio region near the tight set (1,3,4,5,9) seen in E91.
- **Reading** [observation]. For k ≥ 2, §5 has the shape of §6 with pair windows in place of meeting windows:
  1. the uniform pair window at the explicit lap j₀;
  2. the near-runner case (v₄/v₃ small) by a pair-window fold, i.e. a 2D progression of (runner-1, runner-4) phases
     over j;
  3. a few folds.

  k = 1 (the sum relation) needs windows past the pair windows: runner 3 folded, or runners 2 and 3 one lap apart with
  x₃ = x₁ + x₂. It also has a cluster-box family and a bounded set closed by lap boxes. Not established: none of this
  is a proof; the counts are samples (primitive ≤ 36, random ≤ 2,000).

## E105 — §5, k ≥ 2: the pair-window fold, its exceptions, and the first Lean pieces (2026-10-16)

Owner: *"Prove the k >= 2 part: the uniform pair window at j0, then the near-runner pair-window fold as a 2D
progression, following the §6 pattern."* Mid-turn: *"Also we should look into the ones it did not close and why.
Understanding the exception is a standing rule for us."* `s5_pf_v1..v4`, `s5_exc_v1..v2` (`.py`, `.out`);
`S5Pair_v1.lean` (`.out`; axioms `[propext, Classical.choice, Quot.sound]`) [PROVED for the three theorems below].
- **Simple pair-window fold** (`s5_pf_v1`): runner 1 clear across all of P_j, runner 4's sweep meets its band in a
  stretch ≥ μ = v₄/(3v₅), runner 5 folded alone. On k ≥ 2 sets not closed by the uniform window at j₀: primitive ≤ 40,
  8,076 of 8,335; random ≤ 3,000, 275 of 278.
- **1D form** (derived; `s5_pf_v2` agrees with the direct computation on all 2,337 primitive sets ≤ 30). At lap j,
  u = j + 1/6: runner 1 reads p = αu (α = v₁/v₂, the progression), runner 4 reads j + 1/6 + λp with λ = (v₄ − v₂)/v₁.
  The window length is (2/3 − p/k)/v₃, so runner 1 sweeps ρh and runner 4 sweeps w = qh, with h = 2/3 − p/k,
  ρ = v₁/v₃, q = v₄/v₃. Fold condition: p − n₁ ∈ [1/6, 5/6 − ρh], w ≥ μ, and λp ∈ [m − w + μ, m + 2/3 − μ]. Everything
  is a function of k, α, β = (v₄ − v₂)/v₂ = λα and μ.
- **Continuous map** (`s5_pf_v3`, grid over α, β, μ in the non-uniform domain): failures only at k = 2 (7.5% of grid
  points) and k = 3 (2.2%); none at k = 4, 6, 10 (k = 100: the whole grid is uniform at j₀). Mostly at α near
  α_max = k/(3k−1).
- **The exceptions, understood** (`s5_exc_v1`: all 262 integer exceptions, primitive ≤ 40 plus random ≤ 3,000;
  `s5_pf_v4`, `s5_exc_v2`: the small-α part).
  - **(i) Feature.** k ∈ {2, 3}; λ ≈ 0.8–1.5 (v₄ ≈ v₂ + v₁, near a second sum relation x₄ = x₂ + x₁); μ near 1/3
    (v₅ near v₄) in most. Two regimes:
    - large α (≥ 0.62 α_max: v₃ just above 3v₁, near the §8 boundary): only 1–3 pair windows have runner 1 clear
      across them, and at those runner 4's offset z = βu (mod 1) lies just past the arc's upper end 2/3 − μ
      (z ≈ 0.35–0.64 against ≈ 0.35);
    - small α (α ≈ 0.12–0.24): z starts just past the arc (≈ 0.34–0.40), drifts away with step β ≈ 0.16, and wraps
      back into the arc after 4–5 windows, when the pair windows have shrunk so that w < μ.

    In both, runner 4 is in the second half of its lap while runners 1, 2, 3 are clear, and the progression has no
    room to bring it back.
  - **(ii) What forces the witness.** Small α (integer examples (10, 83, 88, 97, 98), (14, 117, 124, 136, 137): the
    region has positive measure in ratio space, so infinitely many sets):
    - the pair window P₁ with runner 1 only partly clear (it enters its band inside P₁), runners 1–4 on laps
      (0, 1, 1, 1), runner 5 folded;
    - or runners 3, 4, 5 on one lap j (laps (0, j, j, j)) with runner 2 folded.

    Large α: four-block folds past the pair windows, with runners 2, 3 one lap apart (laps (0, 1, 2, ·), runner 3
    folded), runner 1 on lap 1 (laps (1, 3, 4, 5), (1, 4, 5, 6), runner 4 or 5 folded), or runner 2 folded
    (0, 1, 1, 1).
  - **(iii) Same mechanism.** The small-α witnesses are the pair-window fold with runner 1 on a sub-window
    (`s5_pair_fold` covers it), and a cluster window (runners 3, 4, 5 together). The large-α witnesses lie in a bounded
    ratio region (k ∈ {2, 3}, v₃/v₁ ∈ (3, ~4.5), v₄/v₃ ≤ ~1.3) — §8-type four-block folds, the same windows §5 k = 1
    and §8 use.
- **Proved** (`S5Pair_v1.lean`):
  - `exists_j0`: some j₀ has v₂ ≤ v₁(6j₀+1) < v₂ + 6v₁;
  - `s5_uniform_j0`: §5 order (v₁ < v₂ < v₃ < v₄ ≤ v₅, 3v₁ < v₃) and |P_{j₀}| ≥ 2/(3v₄) ⇒ lonely; runner 1 is clear across
    all of P_{j₀} using only 3v₁ < v₃;
  - `s5_pair_fold`: any sub-window of P_j where runners 1 and 4 read in bands at both ends and of length ≥ 1/(3v₅) ⇒
    lonely.
- **Design for the rest (not done).** As for E99/E102:
  - a certificate over (k ∈ {2, 3} and k ≥ 4, α, β, μ) whose leaves are a lap j with an exact sub-window
    (`s5_pair_fold`), or an interval of p of length ≥ α (for small α, where the progression must land);
  - the cluster window as a second closer;
  - §8-type four-block folds for the bounded large-α region.

## E106 — §5, k ≥ 2: proved (small-α leaves and step lemma; large-α kernel-checked box tree) (2026-10-17)

Owner: *"Build the k >= 2 certificate over (k, alpha, beta, mu) with pair-fold sub-window leaves, long-interval leaves
for small alpha, the cluster window, and §8-type folds for the bounded large-alpha region."* `S5Cert_v1.lean` (`.out`),
`S5K2_v1.lean` (`.out`; 0 errors; no `sorry`/`native_decide`/`admit`; axioms `[propext, Classical.choice,
Quot.sound]` for `s5_small_alpha`, `tree_ok`, `s5_large_of`, `s5_k2`) [PROVED]. Generators and prototypes:
`s5_cert_v1..v3.py` (`s5_cert_v2.out`), `s5_cert_tree_v1.lean.txt`, `s5_corner_v1.py`.
- **`s5_k2`**: v₁ < v₂ < v₃ = v₂ + D < v₄ < v₅ with 0 < D, 2D ≤ v₁ and 3v₁ < v₃ ⇒ lonely. That is §5 with k ≥ 2, with no
  use of D | v₁: the statement holds for every arrangement with D ≤ v₁/2 and 3v₁ < v₃.
- **Small α = v₁/v₂ ≤ 1/25** (`s5_small_alpha`):
  - v₄ ≥ 1.21v₂: the uniform pair window at j₀ (`s5_uniform_j0`; |P_{j₀}|·v₃ ≥ 169/300 from p₀ < 1/6 + 1/25).
  - Otherwise, with λ = (v₄ − v₂)/v₁:
    - λ ≤ 5: six leaves in (p, λ) (`s5_leafP`; μ at its worst value 1/3; m = 0 on p ∈ [1/6, 5/24] for λ ≤ 8/5, and
      m = 1 on five λ-ranges up to 5). Each is an interval of p of length ≥ 1/25 ≥ α, so a progression point
      α(j + 1/6) lies in it (`exists_p`).
    - λ > 5: `step_meets_arc`. Runner 4 steps by β = (v₄ − v₂)/v₂ < 0.21 per pair window, and the target arc
      [M, M + β] is reached within (1 + β)/β steps, while runner 1 stays in [1/6, 0.449].
- **Large α > 1/25** (`s5_large_of tree_ok`): speeds/v₂ = (α, 1, 1 + ακ, 1 + β, (1 + β)ν), κ = D/v₁ ≤ 1/2,
  ν = v₅/v₄. A tree over boxes in (α, κ, β, ν), with β and ν unbounded above at the root, was generated by
  `s5_cert_v3.py`: **6,084 leaves, 10 empty boxes, 6,093 splits**. A leaf is a kind and five laps; the checker
  recomputes the window [y_a, y_b] (runner-2 reading) and checks it at the box's worst corners. Kinds:
  - 0: a lap box (all five runners in their bands);
  - r ∈ 1..4: runner r folded alone (pair-fold sub-windows, the cluster window with runner 2 folded, §8-type folds);
  - 5: `window_two` on runners 4 and 5.

  `tree_ok` is `decide +kernel` (about 8 minutes). Soundness: `leaf_sound` (`band_of`, `lo_hi`, `fold_one`,
  `window_two_uniform`), `emptyB_sound`, `splitB_sound`, `check_sound`.
- **Exceptions met while building, understood:**
  1. The first prototype failed at the corner α → 2/5, κ → 1/2 (k = 2 with v₃ → 3v₁, the §8 boundary), β ≈ 0.40,
     ν ≈ 1.15. That is near the arrangement (2, 5, 6, 7, 8). The corner is not tight (`s5_corner_v1`: best gap
     ≥ 0.20 > 1/6). Its lonely instants have runner 1 on laps 4–5, outside the first search range (laps 0–2), and no
     runner sweeps a third of a lap there: all five are in their bands at once.
  2. So two additions were needed: runner-1 laps up to 7, and the five-runner lap box as a leaf type.
  3. Separately, a split-order artefact: β and ν doubled to 10¹³ before α was narrowed. Fixed in `choose`.

  With these the tree closes with no failures.
- **Order six, current state:** §2, §6, §7, §8 native and in the dispatch. §5 with k ≥ 2 is native in `S5K2_v1.lean`,
  not yet in the tree or the dispatch. §5 with k = 1 (v₃ = v₁ + v₂, BHK Proposition 11 part 1) is still BHK.

## E107 — §5, k = 1 (v₃ = v₁ + v₂): observation (2026-10-17)

Owner: *"Start §5 k = 1 (the sum relation v3 = v1 + v2): observation first, mapping the runner-3-folded and one-lap-apart
windows."* Mid-turn: *"Thats been running for 34mins or so are you sure its ok?"* — it was not: the first scripts
(`s5k1_obs_v1`, the first `s5k1_tight_v1`) used exact fractions over all lap or crossing combinations and were stopped;
`s5k1_obs_v2..v5` and `s5k1_tight_v1` (floats) run in seconds. Observation only.
- **The geometry.** x₃ = x₁ + x₂ at every instant. Runners 1, 2, 3 are clear exactly when (x₁, {x₂}) lies in one of two
  triangles: T_same (x₁ + {x₂} ≤ 5/6; runners 2 and 3 on one lap — the pair windows) or T_apart (x₁ + {x₂} ≥ 7/6;
  runner 3 one lap ahead). The trajectory is a line of slope a = v₂/v₁ > 2.
- **Coverage** (`s5k1_obs_v2`, closing windows with t ≤ 3/v₁): a window on the block {1, 2, 3} in either triangle, with
  runners 4, 5 by `window_two` or a fold, closes 66,325 of the 66,508 primitive sets ≤ 50 and all 2,000 random ones.
  The earliest such window (`s5k1_obs_v3`) has runner 1 on lap 0 in most cases (T_same with fold of 5: 25,490; fold
  of 4: 16,734; `window_two`: 11,968; T_apart: 9,818). T_apart matters mainly for a < 4: lap 0 apart 8,179 of
  26,561 there, against 111 of 13,889 for a ≥ 10.
- **The 183 exceptions** (no 123-triangle window), in three families (`s5k1_obs_v4`, `v5`):
  1. **AP: v₄ = v₃ + v₁** (84; v₂, v₃, v₄ in arithmetic progression with step v₁, so x₄ = x₂ + 2x₁: runner 4 is tied to
     the line). Closed by lap boxes (0, 1, 1, 2, ·), (0, 1, 1, 1, ·) at x₁ ≈ 0.29–0.45, or with runner 3 folded (laps
     (0, 1, 2, 3) …).
  2. **Cluster at (1, 3, 4, 4, 4)** (99; v₂ = 3v₁, v₃ = 4v₁, v₄ and v₅ just above v₃, e.g. (c, 3c, 4c, 4c+1, 4c+2) for
     every c). Closed by the lap box (0, 0, 0, 0, 0) on the (1, 3, 4) window t ∈ [1/6, 5/24]/v₁, where runners 4 and
     5 follow runner 3.
  3. **The tight set (1, 3, 4, 5, 9)** itself: no window of positive length at any time (lonely only at isolated
     instants).
- **Near the tight set** (`s5k1_tight_v1`, integer k = 1 sets within 6% of (1, 3, 4, 5, 9) in ratio, v₁ ≤ 20): every one
  except the tight set has best gap ≥ 1/6 + 1/18. Examples: (20, 60, 80, 100, 179) and (20, 60, 80, 100, 181), at
  ratio distance 0.0056; (20, 60, 80, 99, 180), 1/6 + 1/12. The gap does not shrink with the ratio distance, but the
  instant moves later (runner 1 on about lap 4–8). In ratio space the gap is not continuous at the tight point.
- **Reading** [observation].
  - Generic k = 1 works like §5 k ≥ 2 and §6: pair windows (T_same) and the apart triangle on runner 1's first lap, with
    runners 4, 5 by `window_two` or a fold.
  - The exceptions are the relation v₄ = v₃ + v₁ (a second AP among runners 2, 3, 4), the cluster (1, 3, 4, 4, 4), and the
    tight set.
  - A box certificate in (α, β, ν) like E106's cannot close a neighbourhood of the tight point. Its integer
    neighbours are lonely only at later laps, by an amount that grows as the perturbation shrinks. That is a
    displacement-type statement (a small speed perturbation δ accumulates to a band-sized shift after about 1/(6δ)
    of time) rather than a window at bounded laps. Not yet tested.

## E108 — §5, k = 1: the neighbourhood of the tight set (1, 3, 4, 5, 9) (2026-10-17)

Owner: *"Tight neighbourhood and then k=1 cert"*. Observation; `s5k1_tight_v2..v4.{py,out}`.
- **Coordinates.** Write ratios to v₁ as v₂/v₁ = 3 + a, v₃/v₁ = 4 + a (k = 1), v₄/v₁ = 5 + b, v₅/v₁ = 9 + a + b + e. The
  tight set is a = b = e = 0. It is the meeting point of three relations besides v₃ = v₁ + v₂: v₂ = 3v₁ (a), v₄ = 5v₁ (b),
  v₅ = v₃ + v₄ (e). Its lonely instants are T = v₁t ≡ ±1/6 (mod 1), with readings (1/6, 1/2, 2/3, 5/6, 1/2) at T = 1/6:
  runners 1 and 4 on band edges.
- **Every integer neighbour checked is lonely** (`s5k1_tight_v3`, all 17,704 sets (c, 3c + d₂, 4c + d₂, 5c + d₄, 9c + d₅),
  6 ≤ c ≤ 40, |d₂|, |d₄| ≤ 3, |d₅| ≤ 5, primitive, ordered).
- **b < 0** (v₄ < 5v₁): the earliest lonely interval starts exactly at T = 1/6 in every case (7,699 sets). Runner 4 reads
  5/6 + b/6 < 5/6 there, and the window is T ∈ [1/6, 5/(6(5 + b))], of length (−b)/(6(5 + b)). Runners 2, 3, 5 are in
  their bands on it when a and e are small (a ≤ 1 + b, 7 ≤ v₅/v₁, 5v₅ ≤ 11v₄ — conditions of fixed size, not relative
  to b).
- **b > 0**: the mirror window T ∈ [25/(6(5 + b)), 5/6] before the tight instant 5/6 (runner 1 at 5/6 from inside, runner 4
  at 1/6 + 5b/6 on lap 4), of length 5b/(6(5 + b)). Earlier windows (T ≈ 0.21–0.48) also occur in the data.
- **b = 0** (v₄ = 5v₁): the windows come later, and the time grows as the deviation shrinks (`s5k1_tight_v4`):
  - a = 0: earliest T ≈ (0.04–0.07)/|e|, e.g. c = 160, d₅ = ±1, T ≈ 7.5;
  - e = 0: T ≈ (0.03–0.09)/|a|.

  Mechanism: with b = 0 and a = 0, runners 1–4 are exactly (1, 3, 4, 5)·v₁, whose lonely windows recur every period
  (T ∈ [n + 13/30, n + 11/24] and others). At those windows runner 5 reads 9T + eT with 9T mod 1 ∈ [0.9, 0.125], so
  runner 5 starts just outside its band. The deviation eT accumulates by e per period, and the first n at which it has
  carried runner 5 into its band gives the window. This is displacement along a progression (step e per period), the
  `step_meets_arc` mechanism, at unbounded laps.
- **Reading** [observation]. A neighbourhood of the tight point has no box certificate at bounded laps. It splits by
  which relation is broken:
  - b ≠ 0: an explicit window at the first tight instant (T = 1/6 or 5/6), of length proportional to |b|;
  - b = 0: a progression in the deviations (a·n, (a + e)·n) over the recurring windows of (1, 3, 4, 5) — a 2D
    displacement orbit, as in §6's generic orbits.

  Away from the tight point the k = 1 certificate is the E106 tree with κ = 1.

## E109 — §5, k = 1: the box tree away from two tight points; the second tight neighbourhood (2026-10-17)

Observation; `s5k1_cert_v1.{py,out}`, `s5k1_tight2_v1.{py,out}`.
- **k = 1 tree prototype** (`s5k1_cert_v1`): E106's leaf search with κ = 1 (speeds/v₂ = (α, 1, 1 + α, 1 + β, (1 + β)ν),
  domain α < 1/2, β > α, ν > 1). Every α-slab from 0.04 to 0.5 closes with no failures except two accumulation points:
  1. α ≈ 1/3, β ≈ 2/3, ν ≈ 1.8: the tight set (1, 3, 4, 5, 9) (E108);
  2. α → 1/2, β → 1, ν → 1.25: speeds proportional to (1, 2, 3, 4, 5), the other tight arrangement. It satisfies
     v₃ = v₁ + v₂ and sits on the boundary v₃ = 3v₁ of §5. Sets such as (c, 2c + 1, 3c + 1, 4c + ·, 5c + ·) approach it
     from inside §5 with k = 1.

  Leaves per slab: 163–1,569 (window_two, folds, lap boxes).
- **The neighbourhood of (1, 2, 3, 4, 5)** (`s5k1_tight2_v1`, all 7,656 sets (c, 2c + d₂, 3c + d₂, 4c + d₄, 5c + d₅),
  6 ≤ c ≤ 60, 1 ≤ d₂ ≤ 3, |d₄|, |d₅| ≤ 3; every one lonely). Tight readings at T = v₁t = 1/6 are
  (1/6, 1/3, 1/2, 2/3, 5/6): runners 1 and 5 on band edges. d₂ ≥ 1 always (3v₁ < v₃). By runner 5's relation to 5v₁:
  - d₅ < 0: the earliest window starts at T = 1/6 in all 3,320 cases;
  - d₅ > 0: windows by T ≤ 0.83 (the mirror tight instant 5/6);
  - d₅ = 0: drift; the earliest T grows as a = d₂/c shrinks, with aT ≈ 0.03–0.07 (c = 60, a = 1/60: T ≈ 1.7–2.6).
- **Reading** [observation]. Both tight points have the same structure (E108). The edge relation (v₄ vs 5v₁ at
  (1, 3, 4, 5, 9); v₅ vs 5v₁ at (1, 2, 3, 4, 5)), when broken, gives a window at the first tight instant of length
  proportional to the deviation. When it holds exactly, the remaining deviations drift into the bands over periods of
  the exact sub-arrangement. So a k = 1 proof needs:
  1. the box tree away from both points;
  2. for each point, a window lemma for a broken edge relation (explicit instant T = 1/6 or 5/6);
  3. a displacement lemma on the plane where the edge relation holds (a progression in the remaining deviations
     over recurring windows, at unbounded laps);
  4. the small-α part redone for κ = 1 (E106's leaves used κ ≤ 1/2).

## E110 — §5, k = 1: the tight-point lemmas; correction to E108–E109 (2026-10-17)

Owner: *"Prove the tight-point lemmas first: the broken-edge windows at T = 1/6 and 5/6 for both points, then the
displacement lemmas on the exact-edge planes; then the k = 1 tree and small alpha."* `S5Tight_v1.lean` (`.out`; axioms
`[propext, Classical.choice, Quot.sound]`) [PROVED]; `s5k1_tightinst_v1.{py,out}`.
- **Correction to E108–E109.** The scripts there (`lonely` in `s5k1_tight_v2`) counted only lonely intervals of
  **positive length** (an EPS margin). The target is non-strict (1/6 ≤ ‖vᵢt‖, `Lonely6`), so a single instant counts.
  Under the non-strict target the exact-edge planes (v₄ = 5v₁ near (1, 3, 4, 5, 9); v₅ = 5v₁ near (1, 2, 3, 4, 5)) are
  lonely at the first tight instant, with equality. The drift at unbounded laps measured in E108–E109 (aT, eT ≈ 0.03–0.07)
  describes where the first **positive-length** window appears; it is real but not needed for the proof. The displacement
  lemmas asked for are therefore not needed, and were not built.
- **`tight_13459`** (real speeds, r = v/v₁; v₃ = v₁ + v₂, r₂ ∈ [14/5, 17/5], v₃ ≤ v₄ ≤ 29v₁/5, r₅ ∈ [43/5, 47/5]):
  - v₄ ≤ 5v₁: lonely at t = 1/(6v₁) (laps (0, 0, 0, 0, 1));
  - v₄ ≥ 5v₁: lonely at t = 5/(6v₁) (laps (0, 2, 3, 4, 7)).
- **`tight_12345`** (v₃ = v₁ + v₂, r₂ ∈ [2, 11/5], r₄ ∈ [19/5, 23/5], v₄ ≤ v₅ ≤ 29v₁/5):
  - v₅ ≤ 5v₁: lonely at t = 1/(6v₁) (all on lap 0);
  - v₅ ≥ 5v₁: lonely at t = 5/(6v₁) (laps (0, 1, 2, 3, 4)).
- **Exact check** (`s5k1_tightinst_v1`, fractions, closed bands): every integer k = 1 set with v₁ ≤ 60 in either
  neighbourhood (2,757,566 and 820,354 sets) is lonely at the named instant; 0 failures.
- These two neighbourhoods become leaves of the k = 1 tree (next).

## E111 — §5, k = 1, α = v₁/v₂ > 1/25: proved; the small-α structure (2026-10-17)

`S5K1Large_v1.lean` (`.out`; 0 errors; no `sorry`/`native_decide`; axioms `[propext, Classical.choice, Quot.sound]` for
`tight_13459`, `tight_12345`, `tree_ok`, `s5k1_large`; the kernel check of the tree takes about 9 minutes) [PROVED].
`s5k1_cert_v2.{py,out}` (float prototype), `s5k1_cert_v3.py` (exact generator), `s5k1_cert_tree_v1.lean.txt`,
`s5k1_small_v1.{py,out}`.
- **`s5k1_large`**: v₁ < v₂ < v₃ = v₂ + v₁ < v₄ < v₅, 3v₁ < v₃, v₂ < 25v₁ ⇒ lonely.
- **The tree** (κ fixed at 1, non-strict windows): **6,328 leaves, 34 empty boxes, 6,361 splits**, over α ∈ [1/25, 1/2],
  β ∈ [0, ∞), ν ∈ [1, ∞). Leaf kinds as in E106, plus kind 6 / 7 for a box inside the neighbourhood of (1, 3, 4, 5, 9) /
  (1, 2, 3, 4, 5), sound by `tight_13459` / `tight_12345` (`tp1_sound`, `tp2_sound`). The float prototype used
  18 + 58 such leaves.
- **Small α < 1/25** (`s5k1_small_v1`, the α → 0 limit; observation). Within one lap of runner 2, runners 2, 3, 4 read
  y, y + p, y + λp (p = runner 1's reading, λ = (v₄ − v₂)/v₁ > 1), so their common clear arc has length
  2/3 − spread({0, p, λp}). With κ = 1 the pair-window sweep is w ≥ 2/3 − p, so the fold of runner 5 needs p ≤ 1/3.
  - Over λ ∈ (1, 40] and p ∈ [1/6, 0.8], the minimal spread exceeds 1/3 − 0.02 only for λ ∈ [1.89, 2.09] (worst 0.343)
    and λ ∈ [2.92, 3.19] (worst 1/3). These are the relations v₄ = v₃ + v₁ and v₄ = v₃ + 2v₁ (λ = 2, 3; the AP family of
    E107).
  - At λ = 2 the clear arc is 1/3 − 2α/3 to first order, and the runner-5 fold needs v₂/(3v₅) ≤ 1/(3(1 + 2α)): equal to
    first order. The fold alone does not decide it.
  - There the closing instant is a lap box placing runner 5 by its own phase λ₅p (λ₅ = (v₅ − v₂)/v₁) when v₅/v₂ is close
    to 1. At p near 5/6 the three points {0, p, 2p} occupy an arc of length about 1/3, and any fourth point keeps the
    spread ≤ 2/3. When v₅/v₂ is bounded away from 1, the fold works with margin.
- **Plan for α < 1/25** (not done): as E106 — the uniform window at j₀ for large β; the step lemma for large λ (p ≤ 1/3
  now); and for λ ∈ (1, Λ] a tree over (λ, runner-5 parameter) with α ∈ (0, α₁] whose leaves are p-intervals of length
  ≥ α₁ with a y-window (fold of runner 5, or a lap box with runner 5 by λ₅ when v₅/v₂ is near 1).

## E112 — §5, k = 1, α < 1/25: the structure, and why it is a 2D orbit problem (2026-10-17)

Owner: *"Build the k = 1 small-alpha part: uniform cut, step lemma for large lambda, and the (lambda, runner-5) tree with
p-interval leaves including the runner-5 lap box near lambda = 2, 3."* Observation and design; nothing new in Lean.
`s5k1_small_v2..v4.{py,out}`, `s5k1_cert_v2_lo1.out`, `s5k1_cert_v2_lo2.out`.
- **Uniform cut** (derived). `s5_uniform_j0` closes β = (v₄ − v₂)/v₂ ≥ (1/6 + 5α/3)/(1/2 − α): 0.507 at α = 1/25, 0.417
  at 1/50, 0.35 at 1/100. The step lemma needs runner 4's step β to be shorter than its target arc 2/3 − p (p ≤ 1/3 for
  κ = 1), so it covers only β < 0.35 (λ ≳ 10 with α ≤ 1/100).
- **Tree extension** (`s5k1_cert_v2` floats): α ∈ [0.03, 0.04] closes with 1,891 leaves and α ∈ [0.02, 0.03] with 5,036.
  The leaf count roughly triples per halving of α, so the box tree is not the route to α → 0.
- **The intermediate-value box lemma** (derived; not yet in Lean). Write v₃ = v₂ + v₁, v₄ = v₂ + λv₁, v₅ = v₂ + λ₅v₁.
  At every instant runners 2–5 read y, y + P, y + λP, y + λ₅P (P = runner 1's reading, exactly). Suppose for all P in
  an interval [p_a, p_b] of length ≥ α = v₁/v₂, inside a runner-1 band, with fixed laps, the lower envelope
  ℓ(P) = max(1/6, m₃ + 1/6 − P, m₄ + 1/6 − λP, m₅ + 1/6 − λ₅P) is at most the upper envelope u(P). Then an exact lonely
  instant exists: f(t) = v₂t − ℓ(v₁t) is continuous and rises by ≥ 1 over one lap of runner 2 (ℓ is antitone), so
  f(t) is an integer n for some t, and then runner 2 reads n + ℓ, runner k reads n + ℓ + d_kP. No drift error, any α.
- **Coverage of the box criterion** (`s5k1_small_v4`, fine P grid). With runner 5 not fast, γ = (v₅ − v₂)/v₂ ≤ 1/2
  (spread{0, P, λP, λ₅P} ≤ 2/3 on a P-run of length ≥ α), every case closes over α ∈ {0.04 … 0.001} and λ up to the
  uniform cut. With γ > 1/2 (runner 5 fast; the box criterion cannot work since runner 5's good P-intervals have length
  about (2/3)/λ₅ < α), a fold of runner 5 with drift margins fails in 316 of the cases, at every α (59–71 per α), for
  λ ≳ 2–7.
- **Reading** [observation]. Small α splits by whether runners 4 and 5 are slow or fast relative to runner 2:
  1. β and γ small (λ and λ₅ bounded): the box lemma on P-intervals — a finite tree in (λ, λ₅).
  2. β or γ macroscopic: the phases of runners 4 and 5 at runner-2 lap j are βj and γj (mod 1), a 2D orbit as j runs
     over the laps with runner 1 in band (about 1/(3α) of them). It must enter a region of positive area. Resonant
     directions (e.g. γ ≈ 2β, β ≈ 1/2) are the exceptions to treat separately.

  This is the shape of §6's near-runner case (E93–E99: generic orbits by a progression lemma, the degenerate
  directions by certificate). The earlier E111 obstacles λ = 2, 3 belong to regime 1 and are covered there (box with
  runner 5 by λ₅).

## E113 — §5, k = 1, small α: the intermediate-value box lemma proved; the fast regime has slack; the build plan (2026-10-17)

Owner: *"Go ahead: prove the intermediate-value box lemma and the slow regime tree first, then the fast regime as a 2D
orbit (generic orbits plus resonant directions), as for §6."* `S5IVT_v1.lean` (`.out`; axioms `[propext,
Classical.choice, Quot.sound]`) [PROVED]; `s5k1_slow_v1`, `s5k1_fast_v1..v3`, `s5k1_cert_v2_lo3/lo4` (`.py`, `.out`).
- **`ivt_box`** [PROVED]: v_k = v₂ + d_k v₁ (d_k ≥ 0) for k = 3, 4, 5. On an interval [p_a, p_b] of runner-1 readings of
  length ≥ v₁/v₂, inside one runner-1 band, suppose the lower envelope `envL` (max of 1/6 and m_k + 1/6 − d_kP) is at most
  the upper envelope `envU` (min of 5/6 and m_k + 5/6 − d_kP). Then some instant is lonely. Proof by
  `intermediate_value_Icc` on f(t) = v₂t − envL(v₁t), which rises by ≥ 1 over one lap of runner 2.
- **Slow-regime tree prototype** (`s5k1_slow_v1`, P-intervals of length ≥ 1/25, any α ≤ 1/25):
  - λ ≤ 4, λ₅ ≤ 8: 17 leaves;
  - λ ≤ 8, λ₅ ≤ 16: 129 leaves;
  - λ ≤ 12, λ₅ ≤ 24: fails near λ = 2, λ₅ ≈ 22–24 (runner 5 sweeps almost a lap over an interval of length 1/25);
  - λ ≤ 16: fails throughout.
- **The fast regime has slack** (`s5k1_fast_v1`, α = 0.002). Across β ∈ (0, 0.51), γ ∈ (β, 3.1), at least 77% of the
  runner-2 laps in runner 1's first band contain a lonely instant (over 90% for β ≥ 0.1); no (β, γ) without one.
  `s5k1_fast_v2`: the good set G of (runner-4, runner-5) phases covers 90–100% of the torus. `s5k1_fast_v3`: the runner-4
  phases good for every runner-5 phase contain an arc of length 0.38–0.78 (depending on P). That uniform condition is
  the pair-window fold of runner 5 with μ ≤ 1/3, so in most of the fast regime runner 5 can be ignored and a step lemma
  on runner 4 (as E106 R3) suffices. The 2D orbit is needed only near λ = 2, 3.
- **Leaf counts below α = 1/25** (k = 1 tree, floats): [0.03, 0.04] 1,891; [0.02, 0.03] 5,036; [0.015, 0.02] 6,240;
  [0.01, 0.015] 22,567. Extending the tree to α = 1/50 costs about 7,000 leaves; below that it is not viable.
- **Plan** (thresholds derived for α ≤ 1/50):
  1. α ∈ [1/50, 1/25]: the box tree (a second kernel-checked file).
  2. α ≤ 1/50, β ≥ 0.417: uniform window at j₀.
  3. α ≤ 1/50, runner-4 leaves and step lemma (κ = 1, μ at worst 1/3; runner 5 folded, any λ₅): λ ≤ 1.78
     (m = 0), λ ≥ 3.2 (m = 1 leaves, then the step lemma for large λ; the progression stays in p ≤ 2/3 − β).
  4. α ≤ 1/50, λ ∈ [1.78, 3.2] (the v₄ = v₃ + v₁, v₃ + 2v₁ strip):
     - λ₅ ≤ Λ₅: the slow tree in (λ, λ₅) with `ivt_box` leaves (intervals ≥ 1/50);
     - λ₅ > Λ₅, γ ≤ 2/3: runner 5 swept into a 4-runner `ivt_box` interval;
     - γ > 2/3: the fold of runner 5 with μ ≤ (1 + β)/(3(1 + γ)) ≤ 0.213.

## E114 — §5, k = 1 completed: 1/50 ≤ α ≤ 1/25 by tree, α ≤ 1/50 analytically (2026-10-17)

`S5K1Mid_v1.lean` (`.out`; `tree_ok`, `s5k1_mid`), `S5K1Small_v1.lean` (`.out`; `treeS_ok`, `k1_strip`, `s5k1_small`):
0 errors, no `sorry`/`native_decide`/`admit`, axioms `[propext, Classical.choice, Quot.sound]` [PROVED]. Generators
`s5k1_cert_v4.py` (tree `s5k1_cert_tree_v2.lean.txt`), `s5k1_small_gen_v1/v2.py`, `s5k1_small_gen_r5.py`,
`s5k1_strip_v1.py` (prototype), `s5k1_small_treeS_v1.lean.txt`.
- **`s5k1_mid`** (25v₁ ≤ v₂ ≤ 50v₁): the E111 checker on the root box α ∈ [1/50, 1/25]; 6,939 leaves, 5 empty boxes.
- **`s5k1_small`** (v₂ ≥ 50v₁), with λ = (v₄ − v₂)/v₁:
  - **λ ≤ 25/14**: one runner-4 leaf (`k1_leafI`, m = 0, p ∈ [1/6, 14/75]; runner 5 folded at worst μ = 1/3).
  - **λ ∈ [25/14, 16/5]** (`k1_strip`, the v₄ ≈ v₃ + v₁, v₃ + 2v₁ resonance):
    - 3v₅ ≥ 5v₂: two runner-4 leaves with μ₀ = 133/625 (μ ≤ (1 + β)/5 there);
    - λ₅ = (v₅ − v₂)/v₁ ≤ 30: the (λ, λ₅) tree `treeS` (126 leaves, `decide +kernel`) of `ivt_box` leaves (runner 5
      placed by its own lap; P-intervals ≥ 1/50 ≥ α; 16 pairwise envelope checks per leaf, term-wise bounds,
      `pairOK_sound`);
    - λ₅ > 30: `sweep5` — runners 1–4 fit on a P-interval (two 4-runner leaves `r5_ok1`, `r5_ok2`); runner 5's offset
      λ₅P moves faster than the envelopes (slopes λ₅ − λ and λ₅), so an intermediate-value step picks its lap m₅ and a
      sub-interval of length 2/(3λ₅) ≥ α (from 3v₅ < 5v₂), then `ivt_box`.
  - **λ ∈ [16/5, 8] and [20, 45/2]**: 14 runner-4 leaves (m = 1, 2, 4).
  - **λ ∈ [8, 20]**: `k1_step` — from lap j₀ runner 4's offset λp = βu steps by β per lap and lands in
    [M + 1/3 − β, M + 1/3] while p ≤ min(1/3, 2/3 − β) (β ≤ λ/50).
  - **λ ≥ 45/2**: `k1_uniform` if 17v₂ ≤ 12v₄ (the window at j₀, using α ≤ 1/50), else `k1_step` with β < 5/12.
- **On the "2D orbit" of E112–E113.** It was not needed in that form. With runner 5 folded at worst μ = 1/3, runner 4
  alone decides everywhere except the strip around λ = 2, 3. There runner 5's phase matters, and the strip's (λ, λ₅)
  tree and the sweep supply it. The resonant directions are exactly that strip.
- **§5 is now native in full** (experiment files):
  - `s5_k2` (k ≥ 2, `S5K2_v1.lean`, E106);
  - k = 1: `s5k1_large` (v₂ < 25v₁, `S5K1Large_v1.lean`, E111), `s5k1_mid` and `s5k1_small` (this entry).

  Not yet moved into the tree or wired into the order-six dispatch, where §5 is still BHK's `lonely_5`.

## E115 — §5 wired in: order six fully native (2026-10-17)

Owner: *"Move the §5 proofs (k >= 2 and k = 1, all alpha) into the tree as modules and wire them into the order-six
dispatch, so order six is fully native; build, axiom check, commit both repos."* `S5Native_wiring_v1.out`.
- **Tree modules** (`LRC/Spec/`):
  - `OrderSixSecFiveNativeK2N` (from `S5K2_v1`);
  - `OrderSixSecFiveNativeK1LargeN` (from `S5K1Large_v1`);
  - `OrderSixSecFiveNativeK1MidN` (from `S5K1Mid_v1`);
  - `OrderSixSecFiveNativeK1SmallN` (from `S5K1Small_v1`, importing K2N for the shared pair-window lemmas instead of
    re-declaring them);
  - `OrderSixSecFiveNativeN`: `s5_all` (v₁ = kD; k ≥ 2 → `s5_k2`; k = 1 → `s5k1_large` / `s5k1_mid` / `s5k1_small` by
    v₂ against 25v₁, 50v₁) and `lonely_5_native` (dispatch form, positive-time shift).

  The tree literals are `noncomputable def` (no code generation; the kernel still reduces them for
  `decide +kernel`).
- **Dispatch:** `OrderSixWholeN.lean` §5 now calls `S5Native.lonely_5_native`; BHK's `lonely_5` and `lonely_6` stay in
  the tree, unused by `lonely6_of_lt`.
- **Check** (`S5Native_wiring_v1.out`): order 3–7 targets build (8,340 jobs). `lonely_5_native`, `s5_k2`, `s5k1_large`,
  `s5k1_mid`, `s5k1_small`, `lonely6_of_lt`, `lonelyRunnerAtN_three` … `_seven` all depend on
  `[propext, Classical.choice, Quot.sound]`. No `sorry`/`native_decide`/`admit`/`unsafe` in the five new modules. The `LRC`
  constants of `lonely6_of_lt` are `Lonely6`, `lonely_8_native`, `lonely_5_native`, `lonely_6_native`,
  `lonely_7_native`.
- **Commits:** nested repo (below), outer repo with this entry. Not pushed.
- **Order six's proof of record is now native in every case** (§2, §5, §6, §7, §8). No BHK case remains in its proof
  term.
