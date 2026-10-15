# The order-six cascade, case by case, against BHK — v3

Supersedes v2 (kept): §5 Case 5.1 and the endings at runners 4, 5 (E16); §3 rewritten.

2026-10-15. Source: `LOG_n6_native_v1.md` E1–E14 and the files named there. Scope: primitive integer
residual sets (`SixResidual`), mostly `[1,40]`; ranges are stated per item.

**Purpose (owner).** Understand how the cascade proves n = 6, or how and why the BHK proof can be
reformulated. The cascade is the oracle: it stops exactly at the first lonely instant
(`lonely_iff_run_ends`, `first_isolation_of_fixed`) and never fails. Flanks, residues, laps and phases
are explanations of what it does.

**Grades.** [L] proved in Lean, axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
[X] exact over the stated range (0 mismatches). [C] count, not a rule.

## 1. What the cascade does in every case

| Explanation | Grade | Source |
|---|---|---|
| First move: element in the way at 1/(6 v1) iff \|v/v1 − 6m\| < 1; setter = latest next opening | [L], [X] 17,135 | `CascadeFirstMove_v1` (`first_move`); `six_first_setter_v1` |
| Later moves: blocking = residue band at the current flank opening; next setter = latest nearest-lap opening (a residue walk) | [L], [X] 25,638 moves | `CascadeResidueWalk_v1` (`later_move_blocking`); `six_later_moves_v1` |
| Opening-1 rule: x in the way at 7/(6z) iff \|7x − 6Nz\| < z for some N | [L] | `CascadeOpeningOne_v1` |
| Staircase: consecutive moves at the same opening index go to strictly smaller flanks | [L], [X] 8,240 | `CascadeStaircase_v1` |
| Early end: final state (x, k) has v1·T < 1/3 iff v1(6k+1) < 2x | [L]; [C] 16,530 of 17,135 | `CascadeStaircase_v1` (`early_iff`) |
| Returns lie inside the proved growth window (`ChainBounds`); lap skip iff g > (6P+11)/(6P+1); position in the window set by setter depths | [L], [X] 1,188 returns | `CascadeReturnLap_v1`; `six_return_exceptions_v1` |
| Where it stops is capped by the first lonely opening of the largest flank; the cap comes from the second-largest flank in the 13 sets where the largest has none | [X] to 150; the two scaled blocking families settled for all k | `six_largest_flank_v2`, `scaled_phase_v1`, E13 |
| Divisible largest flank e = 6E: cell reduction and residue pinning (no free flank pins residues to {1,2,3,5} or {1,3,4,5}) | [L] | `SixCells_v1` |

## 2. Case by case

BHK's normalisation v3 = 1, t0 = 1/(v3 − v2); in integers D = v3 − v2. Dispatch as in `lonely6_of_lt`.

### §8 (v3 ≤ 3 v1) — reproduced

- **Cascade.** Only v4, v5 can be in the way at the start [L `s8_slow_three_clear`]. The walk of S equals
  the walk of {v1, v4, v5} in 3,710 of 3,716 sets [C]. At v5's opening 1 the slow three are clear
  [L `s8_slow_clear_at_v5`]; the walk steps on to v4 iff 7 v4 > 5 v5 [L `s8_v4_steps_on`]; runner j (2, 3)
  then blocks at v4's opening 1 iff 5 v4 < 7 v_j [L `s8_slow_blocks_at_v4`, X 8,954 visits].
- **BHK, as ported** (`OrderSixEightN.lean`). `lonely_8` splits on **5 v4 < 7 v3** (Case 8.1) against
  7 v3 ≤ 5 v4 (8.2): the cascade's condition for runner 3 to block at v4's opening 1. Case 8.1's first
  step, `s81_step1`, concludes "lonely, or 5 v1 < v5 and 5 v5 < 7 v4": the cascade's conditions for the
  path (1,0) → (5,1) → (4,1). Case 8.1 then splits on 13 v2 ≤ 7 v4, runner 2's reading at v4's opening 2
  against 7/6.
- **Reading.** BHK's §8 case structure is the cascade's walk structure: its split conditions are the
  cascade's step and blocking conditions. **Reproduced**, at the level of the case split. Not checked: the
  sub-cases inside 8.2 (`lonely_8_2_1`, `lonely_8_2_2`, `lonely_or_v4_lt_2v3`) against cascade readings.

### §7 and §2 (generic: D ∤ v1, D ∤ v3, 3 v1 < v3) — partly reproduced

- **Cascade.** Runner 3 is the commonest first and final setter [C]. When the cascade ends at v3's
  opening, that clear lap contains a meeting time k/D in 56.5% of sets against 35.8% for all v3 laps [C];
  when it ends elsewhere, 35.6% against 34.7% [C]. 63% of sets end at another flank [C].
- **BHK.** A meeting time k t0 inside a clear lap of runner 3 on which runners 1–3 are clear, then
  Corollary 5 (two-flank window) for runners 4, 5; the torus subgroup ({t0}, {v1 t0}) and the Main Lemma
  choose k.
- **Reading.** Runner 3's clear lap is central to both, and BHK's meeting-time laps are over-represented
  where the cascade ends at runner 3. But most cascade endings are at other flanks or other laps, so the
  cascade does not follow BHK's route here. **Partly reproduced**; the cascade's own route in this case is
  not yet described.

### §5 (D | v1) — route departs; reduction shared

- **Cascade** (`six_s5_prop11_v1.out`, [1,40]). By k = v1/D: k = 1 (1,084 sets), k = 2 (594), k ≥ 3 (766).
  For every k the cascade ends at runner 4 or 5 most often (about 58%), at runner 2 in 22–31%, almost never
  at runner 3 [C].
- **BHK.** k = 1 is Proposition 11 part 1 (v1 + v2 = v3); k = 2 is part 2 on v1/2 with a fictional runner of
  speed v1; k ≥ 3 is Case 5.1. Proposition 11 works at runner 3's half-lap instants t = (l + 1/2)/v3: if
  runner 1 reads in [1/6, 1/3] there (BHK (36)), [t, t + 1/(3 v3)] is clear for runners 0–3 and Lemma 4
  names a lonely instant in it; the Main Lemma (Part 3) chooses l from the orbit of (runner 4, runner 1).
- **Route.** The cascade ends inside a Proposition 11 window in 16.1% of k = 1 sets against 11.2% of all
  lonely openings [C]; for k = 2, 3.7% against 12.1% [C]. The cascade does not follow Proposition 11's route.
- **Shared reduction.** With v3 = v1 + v2 the readings satisfy x3 = x1 + x2 (mod 1) at every instant
  (exact). BHK pin x3 = 1/2 (half lap): runners 1–3 become one-parameter in x1, condition x1 ∈ [1/6, 1/3]
  plus a forward window. The cascade, when it ends at runner 2's opening (x2 = 1/6), gives x3 = x1 + 1/6:
  runners 1–3 clear iff x1 ∈ [1/6, 2/3] (exact). For k = 2, v3 = v2 + v1/2 gives x3 = x2 + x1/2: BHK's
  fictional half-speed runner arises from the speeds. Both collapse the triple with the same relation,
  pinned at different runners. The cascade's endings at runners 4, 5 keep the triple two-dimensional and
  have no counterpart in Proposition 11.
- **Case 5.1 (k ≥ 3)** (`six_s5_case51_v1.out`). All 766 cascade endpoints lie just after a 2–3 meeting
  (frac(D T) in [0, 1/6], against 19.6% of lonely openings) — **forced**: D T = v1 T / k and v1 T < 1/2 in
  every such set. The cascade lands in the first meeting window (j = 0 in BHK (31)), Case 5.1's premise
  (runners 2, 3 together), because it ends early.
- **Endings at runners 4, 5 (1,333 sets, all k).** The 123-gap around the endpoint is at least Lemma 4's
  2/(3 v4) in 22.9% (control 33.8%), at least half a lap of runner 3 in 14.0% (control 18.9%) [C]. In about
  77% the cascade's lonely instant lies in a 123-gap too short for BHK's length lemmas to guarantee one.

### §6 (D | v3, D ∤ v1) — partly explained

- **Cascade.** v2 = (c−1)D, v3 = cD. Runner 2 is clear at runner 3's opening k < c iff 2c − 1 ≤ 6k
  [L `s6_runner2_at_runner3`]. The final flank sorts by c (none at c = 2, 6; runner 3 at c = 3; runner 4
  at c = 4; runner 2 at c ≥ 8) [C]; runner 3 ends it 5 times of 403 at c = 6 [C].
- **BHK.** Meeting times k/D, where runners 2 and 3 read whole numbers; the orbit of runners 1 and 4 at
  those times; Corollary 6 on a rectangle R; Cases 6.1–6.5, and two steps (1/N_G, ±3/N_G) omitted from
  BHK's printed list (found earlier this session; independent confirmation owed).
- **Reading.** The cascade's exact rule concerns the same pair (runners 2 and 3, ratio (c−1):c) that BHK's
  meeting times use, but the cascade's route depends on c in a way BHK's §6 does not. **Partly explained,
  not compared** case by case.

## 3. Where this stands

- **§8: BHK reformulated.** BHK's case split is the cascade's walk (same step and blocking conditions).
- **§5, §7: same regions, different instants.** The cascade works where BHK work (the case relation
  collapsing runners 1–3; meeting windows; runner 3's laps) but reaches earlier lonely instants that BHK's
  length lemmas (Lemma 4, triple and multiple configurations, Main Lemma) do not account for: in §5, about
  77% of endings at runners 4, 5 sit in 123-gaps shorter than Lemma 4's length.
- **§6:** route organised by c = v3/D, not compared with BHK case by case.
- **A framework proof of n = 6 exists** (the framework track, BHK in framework objects, axiom-checked). A
  proof following the cascade's own route would need, for §5 and §7, an exact residue explanation of the
  lonely openings at runners 4, 5 (and 2) inside the first meeting window, in place of BHK's length lemmas.
  That explanation does not exist yet; it is the next object to observe.
- **Explanations holding in every case:** section 1.
