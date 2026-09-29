# Order eight — the mechanism map, v2

2026-09-30. **A working map, not the record.** Supersedes `MECHANISM_MAP_v1.md` (retained unchanged). v2 carries the
repairs from v1's `compile-diff` (`MECHANISM_MAP_v1_COMPILE_DIFF_v1.md`; log E191), the owner's rulings of 2026-09-30
after v1, and a new §9 (consequences of proved results that were never drawn). The record is
`docs/n8/RUNNING_LOG_order8_v1.md`; the manuscript of record is `docs/n8/MANUSCRIPT_v21.md`.

**Scope:** log E100–E191, including the second series E36b–E48b that sits physically inside it (log lines 3458–3837;
E106), and v21 §15–§17E. It is not a complete summary of the log: open items in range that bear on nothing here are
listed in the compile-diff report's part (C), not carried. Read the entries after the last one in scope before relying
on this map. `compile-diff` of v2 is owed (§8).

---

## 0. The method (owner, 2026-09-30)

**Owner:** *"This is a much better approach.  We need to learn from the failed attempts methodologically not just about
that proposed statement.  Always understanding the exceptions should always be required"* (E189), approving E188's
method. Occasion (E188): *"we propose a a why, check it against cascade and find an exception that rules it out.  But are
we understanding why the exception happens, are we trying to tie all these hints clues of what is happening together.
Are we mapping  things so we understand before proposing a the mechanisim."* Then (E191): *"We are proving things and
then not thinking about how they may affect the whole proof attempt, that is working harder instead of smarter.  Are
there other opportunities we have been missing."* And: *"Please be careful, we re proved all n=3 to 7 natively with the
framework"*.

- **M1. Map first.** Before a step, name the object (§1) and the open question (§4) it serves; the log entry opens with
  a `**Map:**` line (memory `feedback_n8_map_first_2026_09_30`). A step that places on neither is not started.
- **M2. Classify the step before doing it.**
  - (a) An equivalent restatement of the obligation: **not a step** (§5).
  - (b) A rule the majority of sets obey: **not a proof** (it is data for §3, not a discard).
  - (c) An argument uniform over an infinite family: **a step**. Only (c) moves the proof.
  - (d) A map run: only derivation checks and the oracle check as pass conditions; output to §3 and §4.
- **M3. Every exception is understood, always**: (i) the feature; (ii) what forces the witness where the cascade finds
  it; (iii) the main mechanism in disguise or not. Each answer rests on an artifact. Otherwise §3 says **not
  understood** and nothing is proposed on that ground. Never answer an exception with a new vantage.
- **M4. Derive the forced facts first.** A forced count is a check, not a finding (§6 F5).
- **M5. Failures by method.** Every failed attempt enters §6 under its class.
- **M6. State every restriction.** An unrestricted parameter describes any instant (§6 F6).
- **M7. Draw the consequence (new in v2).** After anything is proved or checked, write what it implies for the whole
  proof before the next step: which §4 question it bears on, which route it shortens, closes or duplicates, which
  standing question it answers, and where else the same move applies. §9 is the register.
- **Standing rules kept.** The place test (memory `feedback_n8_cascade_is_the_oracle`; for a rule that names *a* lonely
  instant, the check is exact loneliness there, not equality with the landing, R4). No rate or density as the answer; no
  pre-registration on LRC; the cascade is the oracle; no stationary runner; the log is append-only. **Tools**: pigeonhole,
  residue counting, covering, and a measure argument inside one window (provisional) are admissible when they arrive
  organically from a step on disk (E101, E112; E131: not withdrawn). **Lower orders**: orders three to seven are proved
  natively in the framework (v21 §17A; author 2026-09-25; owner 2026-09-30); their mechanisms are framework objects, to
  be read as our own proofs.
- **Range caveat (E114, E131; E170's correction).** Larger ranges have turned up what smaller ones did not; every count
  here is scoped to its window.

---

## 1. Objects, in rung coordinates

Readings `d` are the subject's disparities: positive, whole numbers unless stated. Real readings enter through N2 (§2B)
or the path route (§2E).

| object | definition |
|---|---|
| in the way / clear / lonely | `‖d t‖ < 1/8` / `≥ 1/8` / every reading clear |
| opening, closing, slot of `d` on lap `k` | `(8k+1)/(8d)`; `(8k+7)/(8d)`; `((k − 1/8)/d, (k + 1/8)/d)` |
| certificate `(e, k)` (candidate scale `e/(8k+1)`) | the instant `(8k+1)/(8e)`; `e` clear there by construction; lonely iff every `d` has `d(8k+1) mod 8e ∈ [e, 7e]` |
| grid instant `i/q`, `gcd(i, q) = 1` | multiples of `q` read `0`; a non-multiple reads a nonzero multiple of `1/q`. For `q ≤ 8` the readings in the way are exactly `D_q`, the multiples; for `q ≥ 9` residues within `q/8` of `0` are also in the way |
| rung `(q, i, e)` | the instant `i/q + 1/(8e)`, `e = min D_q`. A multiple reads as at `e`'s first opening: clear iff `d mod 8e ∈ [e, 7e]` (residues; E102 retracted the interval form "every multiple in `[e, 7e]`". v21 calls the condition "R1 on the multiples"; it is R1 on the **cofactors** `d/q` at their bound, E190). A non-multiple reads `d·i/q + d/(8e)`. `q = 1`: the bound. `D_q` empty: R6 at `i/q`. `φ(q)` units |
| separation | the readings in the subject's slot leave; the latest exit is the cascade's next move (with the band condition, §2A) |
| the cascade | from the bound; each move the latest next opening among readings in the way; arrives exactly when the subject is lonely. Its landing is the first lonely instant, a by-product (O1, E109), not the obligation |
| move types | sweep, bridge down, bridge up (`SweepBridgeN`) |
| host, last opener | at a landing: the reading opening there; the reading whose opening starts the six others' clear stretch (E187) |
| near-miss of `m` | a closed interval before the landing, six clear, `m` alone in the way throughout (E187) |
| `q_c` | the landing's own rung `h/gcd(h, K)`. Every opening has one: a coordinate, no content (M6, E177) |
| `q_min` | the least `q` whose rung (exact unit test, R6 included) certifies the set; content only because it is small, per window |
| multiples / non-multiples split at `q` | E190: the multiples of `q` are carried by their cofactors (at most six unless all seven are multiples); the non-multiples must fit into that instant pulled back by `q` |
| pinch, death, reflection | events along a deformation of real readings (E178–E181) |

---

## 2. Derived facts and their status

"Tracked" = committed in the nested `LonelyRunner` repo; paths under `LonelyRunner/LonelyRunner/`.

**A. The mechanism** (E162 (1) and (2), **with their conditions**).

| fact | declaration | status |
|---|---|---|
| at a grid through the arrangement's own reading, **one class, any number of readings per edge, under small-deviation conditions**, every runner is clear except those in the subject's slot (E129) | `GridPairLawN.grid_class_clear` | proved, tracked |
| those runners separate; **if every other reading keeps its band**, all are clear there, and that separation is exactly the cascade's next move (E159, E160); the next obstruction is only readings carried over an entering edge | `SeparationN.lonely_of_separation`, `move_eq_separation`, `transport` | proved, tracked |
| a pair of distinct speeds hands over by a sweep on finitely many laps | `SeparationN.sweep_lap_bound` | proved, tracked |
| three move types; between bridges up the setter's rank strictly falls (E183, on paper). **Not a move budget**: a cap is the imported shape (E172; E184 item 3). Observed chains run to 19 moves (Case B) and 17–25 (late shapes) (E170) | `SweepBridgeN` | module proved, tracked |

**B. The chain of reductions, certificates and the case list.**

| fact | declaration | status |
|---|---|---|
| **the conjecture ⇔ every `EightResidual` set lonely at `1/8`, both directions** | `OrderEightCasesN.lonelyRunnerAt8_iff_residual` (line 982; `f32daf4`, 2026-09-25; E104) | proved, tracked |
| N2: real speeds ⇔ whole numbers (rows; merge to at most six; order seven at `1/7`; stepping inside the margin `1/56`) | `RealEightN.existenceAt8_iff_congruence`, `existenceAt8_of_nat`; `RealFiveN.exists_rows`; `MergeSixN.exists_merge_model_all`; `ManyDirectionsN.lonely_of_model_many` | proved, tracked |
| the band at every disparity is the lonely opening `(8k+1)/(8e)` (the bridge) | `OrderEightCasesN.lonely_eight_of_opening` | proved, tracked |
| rational opening `i/N + 1/(8NM)` is the certificate `(e, 8iM+1)` | `rationalOpening_reading` | proved, tracked |
| Theorems 6.15–6.17 (candidate scales) | `Cascade/ScaleCandidates.lean`: `lonely_iff_exists_candidate_scale` (line 82), `candidate_clear_own`, `inWay_at_scale_interval` | proved, tracked |
| **the rung budget**: fewer than `φ(N)` blocked units leaves a unit free; the link lemma `N ∣ d′ − c·d` | `RungBudgetEightN`: `lonely_eight_of_rung_budget`, `card_rungUnits`, `link_reading` | proved, tracked; **uniform in `N`; not a residual field** (v21 §17C) |
| the case list; descent (`q = 8`, cofactors to order seven, shifts by pigeonhole); R8; R6; R1; common factor | `OrderEightCasesN`: `lonely_eight_or_residual`, `lonely_eight_of_descent`, `_fast`, `_no_multiple_of`, `_spread`, `_common_factor`, `_card_le_six` | proved, tracked |
| `EightResidual`: **22 fields in the tree** (E108: 21; E117: `no_one_free` the 22nd; v21 §17C says 19). The positive-arithmetic fields are usable by any proof; the negated certificate families only by a proof that goes through those families (v21 §17C) | `OrderEightCasesN.lean:770` | structure |
| the case list's strong induction on the sum | `lonely_eight_nat_of_residual` | proved; the induction hypothesis is **not passed** to the residual (§9 C2) |

**C. Equivalences to the obligation** (restatements; §5): `Spec/Doors.lean` `doors_agree`; `lonely_iff_run_ends`
(`Cascade/Iteration.lean:772`); `GrandReturnN.exists_lonely_iff_half`; `lonelyRunnerAt8_iff_residual`. **A by-product
fact, not an equivalence:** `first_isolation_of_fixed` (`Cascade/Iteration.lean:213`; E109 O1).

**D. On paper, checked, not in Lean.**

| fact | where | check |
|---|---|---|
| D1: the host is the least reading divisible by `q_c` | first E102 (346,104 of 346,104; its denominators corrected in E105); E188 | 0 of 346,104 |
| D2: the landing is the rung instant `i/q_c + 1/(8h)` | E188 | 0 of 346,104 |
| for `q ≤ 8`, the readings in the way at `i/q` are exactly `D_q` | E188 | derivation |
| a near-miss lies in one slot of its blocker; the first near-misses are pairwise disjoint | E187 | 0 of 971 |
| with one host, the six others are clear on `[c, t*]`, `c` inside the host's slot | E187 | 0 of 949 |
| at `k/m`, the six others are clear iff every other `d` has `d·k mod m ∈ [m/8, 7m/8]` | E187 | 22 two-interval slots |
| at a clear instant the phases blocked at `2t`, `3t`, `5t` are pairwise disjoint (relayed from the parallel session, its files not on disk; about the replacement after a pinch, local stability, not (B)) | E187 | exact |
| the landing is never later than `q_min`'s first certified instant | E188 | forced |
| a multiple of `q` is clear at `t` iff its cofactor is clear at `q·t` (so the rank-one template with the model instant free restates the obligation) | E190 | derivation |

**E. Real readings and the path route.** Tracked: `OneFreeN.lonely_of_one_free_eight`; `PathRouteN.segment_lonely`,
`move_one_strict`, `move_one_period`; `DeformationN.lonely_along_path`; `PathWindowN.lonelyRunnerAt8_of_window`
(**one OWED hypothesis, `WindowBound`**, E115); `PinchOpenN`; `MirrorCentreN.exists_lonely_mirror_meeting`,
`lonely_of_mem_window`; `DoorsN.lonelyAt_add_const`. Untracked: `PinchReflectionN`, `HandoffDriftN`,
`SymbolicWindowTransportN`, `DoubleBacktrackN`, `PartialReflectionN` (this session's, held).
- **Local stability, proved for:** one-runner moves (`segment_lonely`, `move_one_period`; O4, E115); a simple pinch
  under the reflection's hypotheses (`PinchOpenN`; partial reflection requires each other reading to keep its label and
  be strictly clear at `λt`, E181). **Open:** along the straight deformation of E178–E182, multi-pinches and the
  bounded-time half (E178, E180, E181); `pinch_eventually_lonely` needs a common period (E131).
- The window (B) on a move is loneliness at its lattice points (E116, O5) `[reasoned in the text; the pieces cited are
  proved; ⇐ not in Lean]`; at the target it is Theorem 6.15 at the host's candidate scale (E187). The path route
  relocates the obligation to the target; it does not reduce it (§9 C8).
- **OWED Props** (a `def … : Prop` asserted and concluded by no theorem): `WindowBound` (E115); `CaseB8`, `CaseC8`
  (E156; off the path, E164–E166); `Cover8` (E166, E170; whether `Cover8 2 ⇔ NB(15)` is open).

---

## 3. Regularities, their exceptions, and the three answers

**R1. The landing is a named view** (E100; all 346,104 sets `≤ 24`): the bound 200,736; the next opening `9/(8e)` 63,806;
rung R1 37,438; reverse R1 7,847; a ladder rung 1,062. Exceptions 35,215 (E103; E103's correction: "lap 2 or later"
measured the setter's lap, not the displacement). E174: 31,318 one separation from a view; 3,897 misses, of which 3,129
are the stretch at a rung with `q ≤ 8` and 768 (E175) are placed by rungs with `q ∈ {9, 10, 11}` (in 692 of the 768 the
runner that leaves is the only reading in the way at the rung, `place_768_v1.out`). (i) a finer rung, or one separation
later; (ii) grid and separation at that rung; (iii) yes. **Answered in kind; what sets `q` is open (Q1–Q3).**

**R2. The event is in the other six's first clear interval for some mover** (E185): all but 971. (i) every runner has a
near-miss before the landing, the slowest's forced by the bound; (ii) the host's exit at a rung: 970 at E174/E175's
places, 1 in the 768 (E187); (iii) yes. **Answered.**

**R3. The rung-selection rule** (v21 §17E; `LonelyRunner/experiments/nN/rung_selection_v1.out`): certifies 12,309 of
12,309 v1 residual sets on `[1,30]` and 91,523 of 91,523 on `[1,40]`, least `q` 9 and 16 respectively (figures from the
`.out`); on all sets `≤ 24`, `q_min ≤ 9` (E188). **Read with §17E's density premise:** residual sets are lonely on at
least `0.039` of a period, so a family of about fifty or more instants succeeds on most sets by density alone; a family
counts as mechanism only when it beats a same-size null. The rung-selection rule does (2,998 of 3,000 against 2,687 for
uniform instants and 2,837 for random numerators on the same denominators; the `q ≤ 8` family misses 2 of 3,000,
`family_null_v1.out`), and it is so far the only one. The counts are measurements on a window, not progress (§17D).
- The exact rule has no exception in these windows; the needed `q` grows with the window.
- The **budget** form fails on 1,329 of 91,523 on `[1,40]`. **(i)–(iii) not understood** (Q2).

**R4. First isolation against structured isolation** (E188): of the 145,368 blocked-bound sets, the landing is
`q_min`'s first certified instant in 61; its own rung is `q_c = h` in 115,094, `q_c ∈ [2,8]` in 24,039,
`q_c ∈ {9,…,12}` in 6,235 (the 200,736 bound landings include 28,764 with a second, faster host; the script recorded the
fastest host; 520 multi-host blocked-bound sets are classed by it). A map fact. **Consequence for the place test:** a
rule naming *a* lonely instant is checked by loneliness there, not against the landing.

**R5. The restart after a death** (E183) `[VERIFIED — these subsamples]`: pairwise separation controls it exactly when
there is no bridge up; bridges up are residue coincidences `(8k+1)b mod 8a`. E183's target was a cap (E184 item 3): the
result is a record, not a target. **Partly understood.**

**R6. The double-and-backtrack rule** (E186): its window is the cascade's replacement in 61 of 267, 20 of 87, 25 of 532
strict cases. **Answered: local stability, not placement.**

**R7. The deformation from the AP** (E178–E182): every event a pinch. Partial reflection is proved under its hypotheses
(each other reading keeps its label, strictly clear at `λt`); the pairing of deaths and births was verified on
subsamples (1,712 deaths, 1,449 births) `[reasoned]`. The proposal that the protector is an AP class window carried
along is refuted on these samples (E179). After a death a single separation is the minority (E182: 26%, 8%, 31%), and
E182's global half is equivalent to the conjecture as a bare bound. **Open:** multi-pinches, the bounded-time half.
**Local stability at simple pinches; not a placement statement.**

**R8. v21 §17E observations, not yet read by M3**: hard sets' cells organised by the largest runners' consecutive laps
(52% of cells against 18%, `[EMPIRICAL, 28 sets]`; whether the effect is about multiples of 8 or a totient effect is not
settled, v21); the largest non-multiple of 8 as flank certifies 91,445 of 91,523 (`[EMPIRICAL]`; `DoorLargestFlank`
`[REFUTED]` at orders six and seven, §16L). **Three answers not done.**

**R9. The reach of `DoubledSlotN`** (E162): 123 of 210,335. Answered (O10): one instance of the general mechanism. Two
scope caveats: it measures one parametrised instance; it counted doubled slots anywhere on the circle, where only the
subject's slot matters.

---

## 4. Open questions (map questions; none is a mechanism)

- **Q1 (next).** In each set, why do the rungs `q < q_min` fail: multiples not spread, or every unit blocked, and by
  which readings.
- **Q2.** The rung budget's 1,329 failures on `[1,40]`: which blocked units coincide, and whether the link lemma
  accounts for every coincidence.
- **Q3.** What in the readings' arithmetic sets `q_min`, and how it grows with the window (E175's rung `q` = 9–11. v21
  §17D's 12, 15, 16 are rational-opening resolutions `N`, a different parameter).
- **Q4 (the step, class (c)).** An argument uniform in `q` that some rung has spread multiples and a free unit.
- **Q5. The interim reduction** (owner, E189). At a fixed `q` the rung's conditions see a reading only through whether
  `q` divides it, its residue mod `q`, and the wall-cut cell of its reading at `1/(8e)` (walls `1/8 − r/q`,
  `7/8 − r/q`) `[derived on paper; not checked, not in Lean]`; so at fixed `q` finitely many classes, defined by the
  readings alone (never by loneliness, E145). Walls, not boxes, as in E123–E124 (coincidence not checked). **Open:**
  `q` itself (least `q` 9 on `[1,30]`, 16 on `[1,40]`, `rung_selection_v1.out`). E190 adds the split at `q`
  (multiples carried by cofactors; non-multiples to place) as the constraint the reduction exploits.
- **Q6 (new, E190/E191).** The native order-seven proof ends every case at a residue-band certificate at modulus `7P`
  by unit filtering, using only that every nonzero residue mod 7 is a unit (v21 §17A). Mod 8 the non-units are the even
  residues. Does our order-seven architecture carry one order up with the non-units treated separately, and is the
  residual's organisation by multiples of 8 (shapes `(1,6)`–`(4,3)`, one non-multiple `≡ 4 mod 8`) that separation?
  (§9 C5.)
- **Standing question answered:** v21 §17B / the proof-shape review's Finding 1 asked whether `EightResidual` is the
  obligation or a sufficient route. `lonelyRunnerAt8_iff_residual` proves it is the obligation (§9 C1).

---

## 5. Equivalent forms of the obligation: restatements, not steps

- `LonelyRunnerAt8` / `ExistenceOnArrangements` (the target).
- Theorem 6.15: some candidate scale is clear.
- `doors_agree`; `lonely_iff_run_ends`; `exists_lonely_iff_half`.
- `lonelyRunnerAt8_iff_residual`: every `EightResidual` set is lonely at `1/8` (the conjecture itself, both
  directions); `existenceAt8_iff_residual` (the difference-set form).
- (B) at the target (E187).
- "Repeated separation cannot continue for ever" (E162, E163).
- "Every arrangement has a type" (E145).
- The rung-selection rule, or rungs, with `q` unrestricted (E177; M6).
- The landing at its own `q_c` (E188; M6).
- The rank-one template with its model instant free (E190).

---

## 6. Failed attempts, by methodological class

| class | the failure | instances (entry) |
|---|---|---|
| **F1** imported shape: *that* or *when* it stops | a rank, fence, move budget or exhaustion names no place | E170 quantity tests; E170 "a non-isolating chain runs a full period"; E171 waves ("at most seven moves"; E172); E177's reviewed step (flagged, not run); Props 6.10–6.11 withdrawn (v21 §6); `DoorFirstLap` (a cap, `[REFUTED]`); v1 of this map's §2A "at most 7 moves" (compile-diff A1) |
| **F2** a rate given as the answer | coverage, a share of instants, a reach percentage | E171 (E172); reach percentages (`reach_scheme_dependence_v1.out`); E84 tallies; v21 §17E: top-pair mirror meetings (2,994 against a null of 2,991), extra laps ("Not to be pursued as a mechanism") |
| **F3** a majority rule stated as a law | the rule holds on most sets and is taken as the mechanism | E64 "the same word repeats"; E57's block law `13/4` and E66's "every runner sets at most twice" (E68); E129–E130 "the unsettled are captured readings"; E160 "one unresolved pair"; E185's first-interval statement; E111's entering-edge proxy ("the proxy is wrong, not the cascade") |
| **F4** a restatement taken for a step | an equivalent of the obligation presented as progress | E145 "every arrangement has a type"; E159 "'the separations come to rest' renames the conjecture"; E163 "no return"; E173; E137 (the exact block condition *is* loneliness at that instant); O9 (E143's rotation form is Theorem 6.15); E187's (B) at the target |
| **F5** a forced fact found after the data | a count the definitions force, reported as a finding | E136, E143, E150, E152 (each recorded as forced); E176's 320/320 (E177); E185's one-slot check; E187's `c` in the host's slot; E188's "never later"; v21 §17D's last row (§9 C4) |
| **F6** an unrestricted parameter | the statement then describes any instant | E176 (E177); E129–E130's control against tautology; E188's `q_c`; E190's free model instant |
| **F7** the record not read | a step re-derives or re-proposes what is on disk | O2, O3, O6 (the pre-use grep skipped); E172 (E170's correction to E114 already on disk); E184 (E178–E183 re-derived E113–E115); E187's residue form (v21 §15) and host rule (§17E); O10 recurring E174–E187; E190's "the converse is not an `↔` in Lean" (`lonelyRunnerAt8_iff_residual`, E104); v21 §17B and the review still asking what that theorem answers |
| **F8** a false `def … : Prop` | type-checked, never proved | `DoorFirstLap`; `Cover8` without the card bound (E170, fixed `3ea9feb`) |
| **F9** a frame error | the statement leaves the framework's objects | a stationary runner (E75; `region_lonely`, E186); pre-registration language on LRC (E172) |
| **F10** a continuation asserted, not derived | "it goes on the same way … which always happens" | E151's retraction |
| **F11** a new vantage in place of reading an exception | exceptions end a line of work | E174 → E175 → E178–E183 → E185 → E187 (O10; E188) |
| **F12** a range-forced result (new) | a regularity true only because the window is small | O7 ("the slowest runner never leaves its first block", range-forced; again E151, E153) |
| **F13** a consequence not drawn (new, M7) | something proved and used only for the route it was built for | §9 |

---

## 7. Coordinates of the next step

Q1 is a map run (M2 (d)). Forced before running (M4): for `q ≤ 8`, only the multiples of `q` are in the way at `i/q`, so
a rung below `q_min` fails on the multiples (`d mod 8e ∉ [e, 7e]` for some multiple) or on the units (every unit
blocked by some non-multiple at `i/q + 1/(8e)`). Recorded per set and per `q < q_min`: which condition, which readings,
the blocking reading per unit, and the link relation `q ∣ d′ − c·d` between readings that block the same unit. Q6 is read
from our own order-seven modules before any run (source first).

---

## 8. Owed

- `compile-diff` of v2 against v1, the v1 report and log E189–E191.
- The three answers for R3's budget failures and for R8.
- §9's Lean items (C2) and manuscript corrections (C1, C4), each to the owner.

---

## 9. Consequences of proved results that were never drawn (M7 register)

Each entry: what is proved, where; the consequence for the whole proof; status of the consequence.

- **C1. The residual is the conjecture.** `lonelyRunnerAt8_iff_residual` (both directions, `f32daf4`, 2026-09-25;
  E104). v21 §17B still asks the author whether `EightResidual` is the obligation or a sufficient route (review Finding
  1); E190 repeated that the converse is not an `↔`. **Consequence:** nothing about the arrangement is lost by working
  on the residual; the arrangement's gaps, neighbours and other subjects are coordinates computable from the seven
  numbers. The standing question is answered by a theorem. `[PROVED]`; manuscript correction owed.
- **C2. The induction hypothesis is discarded at the residual.** `lonely_eight_nat_of_residual` proves the reduction by
  strong induction on the sum, and at the call to the residual hypothesis every set of smaller sum is already known
  lonely (`ih` in scope); the residual statement does not receive it. **Consequence:** a residual statement that also
  assumes every smaller-sum set lonely is equivalent and strictly more usable; any proved transfer from a residual set to
  a smaller-sum set becomes a case (only the common factor uses it now). `[reasoned from the Lean text]`; small Lean
  change owed; value open.
- **C3. A uniform-in-`q` tool is not a case.** The rung budget is proved for every `N` (`RungBudgetEightN`) and is not a
  residual field, while the list grew one resolution at a time (thirds, fifths, sixths, sevenths, ninths, then
  `D ≤ 64`). **Consequence:** one field, "some `q` with the multiples in band and fewer than `φ(q)` blocked units",
  replaces the per-resolution fields, and the residual becomes the budget's failures (Q2's object). Read with R3's
  density premise. `[reasoned]`.
- **C4. A field whose count is forced.** `ResolutionClears8` has no bound on `j`, and the cascade's landing
  `(8K+1)/(8h)` is itself a clearing resolution with `D = h`, a reading. So on any window with readings `≤ 64` on which
  the cascade arrives, the residual after `no_small_resolution` is empty by construction; §17D's last row records the
  cascade's arrival on the window, not structure. v21 already calls `64` "a case boundary, not a claim". `[derived]`.
- **C5. Our order-seven proof as a template one order up** (owner: orders three to seven were re-proved natively). The
  native order-seven proof uses only that every nonzero residue mod 7 is a unit (v21 §17A, "totients, not primality").
  `BS_TRANSFER_v2.md` (2026-09-18, before the native re-proof) found a **mathematical** break at 8, not an exclusion: the
  pigeonhole core generalises (`single_level_avoid_general`), its `≠ 0` hypothesis is false at `ZMod 8`
  (`single_level_avoid_false_at_8`), and the filtration has no order-8 analogue; it posed "an affine family of
  multipliers at order 8" as the open sub-problem, and left finite-group covering unruled. Since then the covering move
  is part of our own order-seven proof, the tool rulings admit it organically, and the rung budget and link lemma are
  proved. The log has not returned to it. **Consequence:** Q6. `[reasoned; not examined]`.
- **C6. One template across the reductions** (E190): N2, the case list's descent and R8, and the rung-selection rule
  share one shape (merge to at most six readings; order seven; a freedom spent inside the slack). **Consequence:** the
  rank-one cases are instances of the reduction that settled the real case; Q5's reduction is to be sought in that shape,
  with its restriction stated (M6). `[reasoned]`.
- **C7. Earlier maps never cited.** `EXISTENCE_MAP_v1`–`v5`, `WITNESS_MAP_v1`, `DEPTH_MAP_v1`, `CASE_B_MAP_v1` and others
  in `docs/n8/` are cited nowhere in the log (`grep -c "_MAP"` returned 1 before E189). **Consequence:** their content has
  not been checked against this map; owed.
- **C8. The path route duplicates N2.** Both reduce real arrangements to whole numbers; the path route's (B) is the
  whole-number obligation at the target (E116, E187), and its remaining halves (multi-pinches, bounded time) are open.
  E178–E186's work proved local stability along deformations. **Consequence:** the path route adds no reduction beyond
  N2; effort there bears on `hopen`, which N2 does not need. `[reasoned]`.
