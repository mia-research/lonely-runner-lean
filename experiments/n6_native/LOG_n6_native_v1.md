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
