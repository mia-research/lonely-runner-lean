# The order-six cascade, case by case, against BHK — v1

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

### §5 (D | v1) — departs

- **Cascade.** Almost never ends at runner 3 (15 of 2,444) [C]; its endpoint never lies in a meeting-time
  lap of runner 3 (0 of 2,444, against 4–15%) [C]; runner 2 appears as a setter in runner 3's place [C].
- **BHK.** Runner 1 sits at the origin at every meeting time, so the generic route is closed; Case 5.1
  (k ≥ 3) by triple configurations, Case 5.2 by Proposition 11 (v1 + v2 = v3).
- **Reading.** Both avoid runner 3's meeting-time laps, for the same reason. What the cascade does instead
  (runner 2's openings) has not been compared with Proposition 11. **Not yet compared** beyond that.

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

- **Reproduced:** §8, at the level of BHK's case split.
- **Partly:** §7/§2 (runner 3's lap central to both; cascade mostly elsewhere), §6 (same pair, different
  organisation).
- **Open:** §5 against Proposition 11; §7's own route; §6 case by case; §8's inner sub-cases.
- **Explanations that hold in every case** are section 1. None of them yet explains, by itself, why the
  cascade's first lonely instant comes at a low opening; that is the question the case comparisons above
  are approaching.
