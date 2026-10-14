# Order eight — the mechanism map, v1

2026-09-30. **A working map, not the record.** The record is `docs/n8/RUNNING_LOG_order8_v1.md`; the manuscript of
record is `docs/n8/MANUSCRIPT_v21.md`. This file is where each step **starts**: read it before any step, place the
step on it, and add what the step finds (as a new version, never in place). Scope of v1: log E100–E188 and v21
§15–§17E. It is not a complete summary of the log; the `compile-diff` check against its sources is owed before it is
relied on as complete (see §8).

---

## 0. The method (owner, 2026-09-30)

**Owner:** *"This is a much better approach.  We need to learn from the failed attempts methodologically not just about
that proposed statement.  Always understanding the exceptions should always be required"* (log E189), approving the
method proposed in E188. The occasion (E188): *"we propose a a why, check it against cascade and find an exception that
rules it out.  But are we understanding why the exception happens, are we trying to tie all these hints clues of what is
happening together.  Are we mapping  things so we understand before proposing a the mechanisim."*

- **M1. Map first.** Before a step, name the object (§1) and the open question (§4) it serves. A step that places on
  neither is not started.
- **M2. Classify the step before doing it.**
  - (a) An equivalent restatement of the obligation: **not a step** (§5 lists the known ones).
  - (b) A rule the majority of sets obey: **not a proof**.
  - (c) An argument uniform over an infinite family: **a step**. Only (c) moves the proof.
  - (d) A map run: records coordinates, with only derivation checks and the oracle check as pass conditions. Allowed;
    its output goes to §3 and §4, never straight to a statement.
- **M3. Every exception is understood, always.** Required before any new statement is made on the ground it covers:
  (i) the feature that makes it exceptional; (ii) what forces the witness where the cascade finds it; (iii) whether that
  is the main mechanism in disguise (`methodology_understand_exceptions`). An exception without the three answers is
  entered in §3 as **not understood**, and nothing that depends on it is proposed. Never answer an exception by opening
  a new vantage.
- **M4. Derive the forced facts first.** A count that the definitions force is a check, not a finding (§6 F5).
- **M5. Learn from failures by method, not only by statement.** Every failed attempt is entered in §6 with its
  methodological class. Before a step, check it against §6's classes.
- **M6. State every restriction.** A parameter left unrestricted makes a statement describe any instant (§6 F6).
- **Standing rules kept** (memories `feedback_n8_cascade_is_the_oracle`, `feedback_n8_no_prereg_no_imports`): the place
  test; no density, no coverage, no rate as an answer; no pre-registration on LRC; the cascade is the oracle, and on an
  exception the explanation is wrong, not the cascade; no stationary runner; the log is append-only.

---

## 1. Objects, in rung coordinates

Readings `d` are the subject's disparities: positive (no stationary runner), whole numbers unless stated. Real readings
enter through the path route (§2 group E).

| object | definition |
|---|---|
| in the way / clear / lonely | `‖d t‖ < 1/8` / `≥ 1/8` / every reading clear |
| opening, closing, slot of `d` on lap `k` | `(8k+1)/(8d)`; `(8k+7)/(8d)`; `((k − 1/8)/d, (k + 1/8)/d)` |
| certificate `(e, k)` (candidate scale `e/(8k+1)`) | the instant `(8k+1)/(8e)`; `e` is clear there by construction; lonely iff every `d` has `d(8k+1) mod 8e ∈ [e, 7e]` |
| grid instant `i/q`, `gcd(i, q) = 1` | multiples of `q` read `0`; a non-multiple reads a nonzero multiple of `1/q`. For `q ≤ 8` the readings in the way are exactly `D_q`, the multiples of `q`; for `q ≥ 9` residues within `q/8` of `0` are also in the way |
| rung `(q, i, e)` | the instant `i/q + 1/(8e)`, `e = min D_q`. A multiple reads as at `e`'s first opening (clear iff `d mod 8e ∈ [e, 7e]`, R1 on the multiples); a non-multiple reads `d·i/q + d/(8e)`. `q = 1`, `i = 0`: the bound `1/(8 d_min)`. `D_q` empty: R6 at `i/q`. `φ(q)` units |
| separation | the readings in the subject's slot leave; the latest exit is the cascade's next move |
| the cascade | from the bound; each move is the latest next opening among readings in the way; it arrives exactly when the subject is lonely. Its landing is the first lonely instant, a by-product (O1, E109), not the obligation |
| move types | sweep, bridge down, bridge up (`SweepBridgeN`) |
| host, last opener | at a landing: the reading opening there; the reading whose opening starts the six others' clear stretch (E187) |
| near-miss of `m` | a closed interval before the landing where the other six are clear and `m` alone is in the way throughout (E187) |
| `q_c` | the landing's own rung, `h/gcd(h, K)`. **Every opening has one: a coordinate, no content** (M6, E177) |
| `q_min` | the least `q` whose rung (rung-selection rule, exact unit test, R6 included) certifies the set. Content only because it is small, and only per window |
| pinch, death, reflection | events along a deformation of real readings (E178–E181) |

---

## 2. Derived facts and their status

"Tracked" = committed in the nested `LonelyRunner` repo; paths under `LonelyRunner/LonelyRunner/`.

**A. The mechanism** (E162 (1) and (2)).

| fact | declaration | status |
|---|---|---|
| at any grid through the arrangement's own reading, every runner is clear except those in the subject's slot | `GridPairLawN.grid_class_clear` | proved, tracked |
| those runners separate, and that is the cascade's next move; the next obstruction is only readings carried over an entering edge | `SeparationN.lonely_of_separation`, `move_eq_separation`, `transport` | proved, tracked |
| a pair of distinct speeds hands over by a sweep on finitely many laps | `SeparationN.sweep_lap_bound` | proved, tracked |
| three move types; between bridges up the setter's rank strictly falls (so a run has at most 7 moves) | `SweepBridgeN`; the rank fall derived in E183 | module proved, tracked; rank fall on paper |

**B. Certificates and the case list.**

| fact | declaration | status |
|---|---|---|
| the band at every disparity is the lonely opening `(8k+1)/(8e)` (the bridge) | `OrderEightCasesN.lonely_eight_of_opening` | proved, tracked |
| rational opening `i/N + 1/(8NM)` is the certificate `(e, 8iM+1)` | `rationalOpening_reading` | proved, tracked |
| Theorem 6.15: lonely iff some candidate scale is clear; 6.16: `e` clear at its own; 6.17: bad scales are explicit open intervals | `Cascade/ScaleCandidates.lean`: `lonely_iff_exists_candidate_scale` (line 82), `candidate_clear_own`, `inWay_at_scale_interval` | proved, tracked |
| **the rung budget**: fewer than `φ(N)` blocked units leaves a unit free; the link lemma: `N ∣ d′ − c·d` makes two readings move together | `RungBudgetEightN`: `lonely_eight_of_rung_budget`, `card_rungUnits`, `link_reading` | proved, tracked. **The one argument uniform in `q` in view** |
| the case list; the residual | `lonely_eight_or_residual`, `existenceAt8_iff_residual` | proved, tracked; the residual statement is `[OPEN]` |

**C. Equivalences to the obligation** (see §5; proved, and restatements for that reason): `Spec/Doors.lean`
`doors_agree`, `lonely_iff_run_ends` (`Cascade/Iteration.lean:772`), `GrandReturnN.exists_lonely_iff_half`,
`first_isolation_of_fixed` (`Cascade/Iteration.lean:213`).

**D. On paper, checked, not in Lean.**

| fact | where | check |
|---|---|---|
| D1: the host is the least reading divisible by `q_c` | E188 | 0 of 346,104 |
| D2: the landing is the rung instant `i/q_c + 1/(8h)` | E188 | 0 of 346,104 |
| for `q ≤ 8`, the readings in the way at `i/q` are exactly `D_q` | E188 | derivation |
| a near-miss lies in one slot of its blocker; the seven first near-misses are pairwise disjoint | E187 | 0 of 971 |
| with one host, the six others are clear on `[c, t*]` with `c` inside the host's slot | E187 | 0 of 949 |
| at `k/m`, the six others are clear iff every other `d` has `d·k mod m ∈ [m/8, 7m/8]` | E187 | 22 cases where the slot holds two clear intervals |
| at a clear instant, the phases blocked at `2t`, `3t`, `5t` are pairwise disjoint (not for any pair with 6 or 7, nor `{2,4}`, `{4,5}`) | E187 | exact |
| the landing is never later than `q_min`'s first certified instant | E188 | forced (the landing is the first lonely instant) |

**E. Real readings and the path route.** Tracked: `OneFreeN.lonely_of_one_free_eight`; `PathRouteN.segment_lonely`,
`move_one_strict`, `move_one_period`; `DeformationN.lonely_along_path`; `PathWindowN.lonelyRunnerAt8_of_window`;
`PinchOpenN`; `MirrorCentreN.exists_lonely_mirror_meeting`, `lonely_of_mem_window`; `DoorsN.lonelyAt_add_const`.
**Untracked** (other sessions' work, or held): `PinchReflectionN`, `HandoffDriftN`, `SymbolicWindowTransportN`,
`DoubleBacktrackN`, and `PartialReflectionN` (this session's, held until `PinchReflectionN` is committed).
- Local stability (`hopen`) is proved (`PinchOpenN`; the reflections).
- The window (B) on a move is loneliness at its lattice points (E116, O5); at the target it is Theorem 6.15 at the host's
  candidate scale (E187). The path route relocates the obligation to the target; it does not reduce it.

---

## 3. Regularities, their exceptions, and the three answers

Each entry: the regularity and its scope; its exceptions; (i) feature, (ii) what forces the witness, (iii) same
mechanism?; status.

**R1. The landing is a named view** (E100; all 346,104 sets `≤ 24`): the bound 200,736; the next opening `9/(8e)` 63,806;
rung R1 37,438; reverse R1 7,847; a ladder rung 1,062. Exceptions: 35,215 (E103, E174): 31,318 are one separation from a
view; 3,897 misses (E175), of which 3,129 are the stretch at a rung with `q ≤ 8` and 768 are placed by rungs with
`q ∈ {9, 10, 11}` (in 692 of the 768 the runner that leaves is the only reading in the way at the rung).
(i) the landing sits at a finer rung, or one separation later; (ii) grid and separation at that rung; (iii) yes.
**Status: answered in kind. What sets `q` is open (Q1–Q3).**

**R2. The event is in the other six's first clear interval for some mover** (E185): all but 971 of 346,104.
(i) every runner has a near-miss before the landing; the slowest's is its lap-0 slot before the bound, forced by the
bound; (ii) the host's exit at a rung: 970 at E174/E175's places, 1 in the 768 (E187); (iii) yes. The first-interval
reading was the first isolation's incidental arithmetic. **Status: answered.**

**R3. The rung-selection rule** (v21 §17E; `LonelyRunner/experiments/nN/rung_selection_v1.out`): certifies 12,309 of
12,309 v1 residual sets on `[1,30]` and 91,523 of 91,523 on `[1,40]`, least `q` up to 9 and 16. On all sets `≤ 24`,
`q_min ≤ 9` (E188: 1: 200,736; 2: 74,083; 3: 47,567; 4: 16,563; 5: 6,597; 6: 360; 7: 190; 8: 7; 9: 1). The needed `q`
grows with the window (§17D), so no fixed list of `q` closes the residual.
- The **exact** rule has no exception in these windows.
- The **budget** form (pigeonhole) fails on 1,329 of 91,523 on `[1,40]`: every unit count exceeds `φ(q)`, yet a unit is
  free. **(i)–(iii) not understood** (Q2).

**R4. First isolation against structured isolation** (E188): of the 145,368 sets whose bound is blocked, the landing is
`q_min`'s first certified instant in 61; its own rung is `q_c = h` (full resolution) in 115,094, `q_c ∈ [2,8]` in 24,039,
`q_c ∈ {9,…,12}` in 6,235. A map fact, no exception to answer. Reading: the first isolation is the multi-move chain's
endpoint; the structured one is the mechanism started at a better grid instant, landing in one move.

**R5. The restart after a death** (E183): pairwise separation controls it exactly when there is no bridge up; bridges up
are residue coincidences `(8k+1)b mod 8a` between distinct pairs. **Partly understood**: which pairs coincide, and why,
is not derived.

**R6. The double-and-backtrack rule** (E186): its window is the cascade's replacement in 61 of 267, 20 of 87, 25 of 532
strict cases. (i)–(iii): it names a window that survives the pinch (local stability), not where the cascade goes.
**Answered; bears on `hopen`, which is proved.**

**R7. The deformation from the AP** (E178–E182): every event is a pinch; every simple pinch has a partner at the same
parameter (partial reflection, Lean, held); relocation after a death falls into three exhaustive cases. **Local stability,
proved; not a placement statement.**

**R8. v21 §17E observations, not yet read by M3**: the hard sets' cells are organised by the largest runners'
consecutive laps (`[EMPIRICAL, 28 sets]`); the largest non-multiple of 8 as flank certifies 91,445 of 91,523 v1 sets on
`[1,40]` (`[EMPIRICAL]`; "the largest element as flank", `DoorLargestFlank`, is `[REFUTED]` at orders six and seven,
§16L). **Three answers not done.**

**R9. The reach of `DoubledSlotN`** (E162): 123 of 210,335. Answered (O10): one parametrised instance of the general
mechanism; its narrowness is not a property of the mechanism.

---

## 4. Open questions (map questions; none is a mechanism)

- **Q1 (next).** In each set, why do the rungs `q < q_min` fail: the multiples of `q` not spread, or every unit blocked,
  and in each case by which readings.
- **Q2.** The rung budget's 1,329 failures on `[1,40]`: which blocked units coincide, and whether the link lemma
  (`link_reading`) accounts for every coincidence.
- **Q3.** What in the readings' arithmetic sets `q_min`, and how it grows with the window (E175's 9–11; §17D's 12, 15, 16
  for the seven sets left on `[1,40]`).
- **Q4 (the step, class (c)).** An argument uniform in `q` that some rung has spread multiples and a free unit. The rung
  budget is the uniform tool in view; Q1–Q3 are what it has to handle.
- **Q5. The interim reduction** (owner, 2026-09-30: *"Since we have reduced "any" arrangement to a finite set.  Do we
  need an interim step where we reduce the infinite family to a reduced set too?"*). Yes: the case-list form (v21 §0) is a
  finite list of conditions, jointly exhaustive, and an argument uniform in `q` still has to be told, set by set, which
  `q` to use. What is derivable now, at a **fixed** rung `q` `[derived on paper; not yet checked, not in Lean]`: the
  rung's conditions see a reading only through (a) whether `q` divides it, (b) its residue mod `q`, and (c) its reading at
  `e`'s first opening `1/(8e)`, and see (c) only through which cell it lies in, the cells cut by the walls
  `1/8 − r/q` and `7/8 − r/q` (mod 1) for the residues `r`; `e` being the least multiple is an order condition on (a).
  So at a fixed `q` the infinite family falls into finitely many classes, each certified at `q` as a whole or not. The
  classes are defined by the readings alone, never by loneliness (E145's types failed because they contained it). They are
  cells cut by walls, the kind E123–E124 found natural ("walls, not boxes"); whether they coincide with E124's is not
  checked. **Open:** `q` itself. On the windows measured the least `q`
  keeps growing (9 on `[1,30]`, 16 on `[1,40]`, §17E), so a finite list of `q` is not in view; the reduction has to say
  which classes push `q` up and why (Q1, Q3), or reduce `q` itself.
- **Standing (the author's ruling):** whether `EightResidual` is the obligation or a sufficient route (v21 §17B–C).

---

## 5. Equivalent forms of the obligation: restatements, not steps

Each of these is proved equivalent to, or is by definition, the open statement. Arriving at one is not progress (M2 (a)).
- `LonelyRunnerAt8` / `ExistenceOnArrangements` (the target).
- Theorem 6.15: some candidate scale is clear.
- `doors_agree`: the four doors.
- `lonely_iff_run_ends`: the cascade's run ends.
- `exists_lonely_iff_half`: lonely in `(0, 1/2]`.
- `existenceAt8_iff_residual`: every `EightResidual` set is lonely at `1/8` (difference-set form; sufficient).
- (B) at the target (E187).
- "Repeated separation cannot continue for ever" (E162, E163).
- "Every arrangement has a type" (E145).
- The rung-selection rule, or rungs, with `q` unrestricted (E177; M6).
- The landing at its own `q_c` (E188; M6).

---

## 6. Failed attempts, by methodological class

The point of this register is the class: before a step, check whether it falls in one.

| class | the failure | instances (entry) |
|---|---|---|
| **F1** imported shape: *that* or *when* it stops | a rank, fence, move budget or exhaustion names no place | E170 quantity tests (none strictly monotone; the shape fails regardless); E170 "a non-isolating chain runs a full period"; Props 6.10–6.11 withdrawn (v21 §6, no index bound); `DoorFirstLap`, a cap `d_min·t ≤ 1`, `[REFUTED]` at §6.7's 28-move case |
| **F2** a rate given as the answer | coverage, a share of instants, a reach percentage | E171 coverage and random-instant share (E172); reach percentages (`reach_scheme_dependence_v1.out`: one rule, three schemes, three answers); E84 tallies (owner: imported, not logical) |
| **F3** a majority rule stated as a law | the rule holds on most sets and is taken as the mechanism | E64 "the same word repeats"; E57's block law `13/4` and E66's "every runner sets at most twice" (E68); E126 "the unsettled are captured readings"; E160 "one unresolved pair"; E185's first-interval statement |
| **F4** a restatement taken for a step | an equivalent of the obligation presented as progress | E145 "every arrangement has a type"; E163 "no return"; E173; E187's (B) at the target |
| **F5** a forced fact found after the data | a count the definitions force, reported as a finding | E176's 320/320 (E177); E185's one-slot check; E187's `c` in the host's slot; E188's "never later" |
| **F6** an unrestricted parameter | the statement then describes any instant | E176's "one place, not a rung" and the growth of `q` (E177); E126's control against tautology; E188's `q_c` |
| **F7** the record not read | a step re-derives or re-proposes what is on disk | E184 (E178–E183 re-derived E113–E115); E187's residue form was v21 §15's bridge; E187's host rule was §17E's rung-selection; O10 (E162) recurring through E174–E187 |
| **F8** a false `def … : Prop` | a `Prop` is type-checked, never proved; no gate sees it | `DoorFirstLap`; `Cover8` without the card bound (E170, fixed `3ea9feb`) |
| **F9** a frame error | the statement leaves the framework's objects | a stationary runner (E75 withdrawn; `region_lonely`, E186 flag); pre-registration language on LRC (E172) |
| **F10** a continuation asserted, not derived | "it goes on the same way … which always happens" | E151's retraction |
| **F11** a new vantage in place of reading an exception | exceptions end a line of work instead of informing the map | E174 → E175 → E178–E183 → E185 → E187 (O10); the cycle E188 records |

---

## 7. Coordinates of the next step

Q1 is a map run (M2 (d)). Forced before running (M4): for `q ≤ 8`, only the multiples of `q` are in the way at `i/q`, so
a rung below `q_min` fails either on the multiples (`d mod 8e ∉ [e, 7e]` for some multiple `d`) or on the units (every
unit blocked by some non-multiple at `i/q + 1/(8e)`). Recorded per set and per `q < q_min`: which condition, which
readings, and for blocked units the blocking reading per unit, with the link relation `q ∣ d′ − c·d` between readings
that block the same unit.

---

## 8. Owed

- `compile-diff` of this map against its sources (log E100–E188, v21 §15–§17E), before it is relied on as complete.
  Result goes to the log; a `v2` carries the repairs.
- The three answers for R3's budget failures and for R8.
