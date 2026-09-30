# Order eight — the mechanism map, v3

2026-10-01. **A working map, not the record.** Supersedes `MECHANISM_MAP_v2.md` (retained unchanged; v1 likewise). v3
adds log E192–E219: our order-seven proof read for order eight (E192–E195) and its pause as F14 (E196–E197); the design
phase inside the owner's design (`CASCADE_DESIGN_v1`, `_v2`; E198–E200); the cascade's run mapped from the bound
(E201–E208); the band theorem committed and wired into a route (E209–E212); the Q7 line and its withdrawal (E213–E215);
the re-aimed run and the persistence run (E216–E219); and the owner's direction of 2026-10-01 (§0, §4 Q8, §7). Text
carried from v2 is unchanged except where marked **(v3)**. The record is `docs/n8/RUNNING_LOG_order8_v1.md`; the
manuscript of record is `docs/n8/MANUSCRIPT_v21.md` (the Lean tree leads it; owner, E192).

**Scope:** log E100–E219, including the second series E36b–E48b that sits physically inside it (log lines 3458–3837;
E106), and v21 §15–§17E. It is not a complete summary of the log: open items in range that bear on nothing here are
listed in v1's compile-diff report part (C) (`MECHANISM_MAP_v1_COMPILE_DIFF_v1.md`), not carried. v3's own report,
`MECHANISM_MAP_v3_COMPILE_DIFF_v1.md`, lists what the first draft lost and how it was repaired (marked **(v3, repair)**). Read the
entries after the last one in scope before relying on this map. `compile-diff` of v3 against v2 and log E189–E219 is owed before reliance (§8); it also discharges
v2's owed run.

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
- **M7. Draw the consequence (new in v2; the session's rule, not an owner ruling, E192 (v3, repair)).** After anything is proved or checked, write what it implies for the whole
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
- **(v3) The owner's rulings of 2026-09-30 and 2026-10-01, in order.**
  - E196–E197: *"are we creeping back into trying to derive something that the cascade doesn't do instead of trying to
    figure out why the cascade is a perfect oracle that has never not found an isolation point for any arrangement"*;
    *"We have a perfect oracle and you keep wanting to prove something else"*. The check at the start of a step: does
    it study what the cascade does, or a family it does not use (§6 F14)?
  - E198: *"Maybe we need to spend more time in the design phase … Every step has to be though of, am I trying to fit this
    to another frame to avoid it"*. Steps are designed before they are run, with the checklist in the design.
  - E200: *"I don't like first isolation"* (nothing rests on the landing being first; `first_isolation_of_fixed` is a
    by-product and is not used); *"Each isolation is pushed there by the speed"*; *"we want to develop our proof so there
    is no gaps"*. **"Pieces" withdrawn** (E200): the owner's object is the push; no regions are grown around references
    (v3, repair).
  - E215: *"Stop and think are we chasing the correct target, native framework, are we introducing any density or
    coverage or other things from other frames before we go on"*.
  - **2026-10-01, the direction now in force:** *"We keep proposing mechanisims, testing them and finding exceptions.  We
    should really know and understand what the cascade does in all configurations, not be testing to find out something
    different happens.  I think this is the next major piece of work.  There should be no gaps in what we understand
    should happen"*. So: **M8 (v3). Derive first; a run checks a derivation.** A run's pass condition is that a derived
    statement holds on every case; an exception means the derivation is wrong and is repaired by derivation, not
    answered with a new proposal. Discovery runs (propose, test, find exceptions) are the pattern this replaces (§4 Q8).
- **(v3, repair) Session findings kept with the method** (the session's, not owner rulings): a cover of the gap simplex
  must be built and checked; it cannot be inferred from local stability, which would presuppose that every point is
  lonely (E199, `[reasoned]`). "Almost always" in reports reads as a rate; the content is the listed exceptions and their
  mechanism (E206's review).
- **(v3) The interval check** (memory `feedback_n8_cascade_is_the_oracle`, 2026-10-01): a place is an instant. On any
  statement, question's object, score or pass condition containing an interval of instants: delete the interval clause
  and see whether a place remains; rewrite the interval in `u = d_min·t` and compare with object register v3's rows
  (item 15, the first window; item 4, covering; item 8, set emptiness), not with words; for an owed Prop or a
  data-chosen parameter, find the time bound it implies (E170's NB(X)).
- **(v3, repair) The log audit** (memory `feedback_n8_map_first`): the `**Map:**` audit starts at E191, the
  `**Consequence:**` audit at E192 (E192). E200 and E209 are flagged by it; both cite earlier results and have no new
  consequence (the audit note after E212).

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
| **(v3)** slow part `P`, fast part `F` | split at the largest consecutive ratio, re-split the lower part while its spread exceeds `s` (gapless for every `s` from 1 to 7, E201, E207). At `s = 1` `P` is the slowest reading alone: its clear blocks `[1, 7]`, `[9, 15]`, … in `R = 8·d_min·t` |
| **(v3)** index | which clear interval of `P` holds the landing (E201–E202); inside it only `F` obstructs (D1, from `exists_block_iff_fast_lap`) |
| **(v3)** capture, carry-in | a fast reading in the subject's slot at the bound (grid slot 0 or 7 of the slowest reading's grid); a reading carried over the entering edge during a separation (E202; `transport`) |
| **(v3)** passage, bridge, relay | a lap-`k` cluster (consecutive ratios below `ρ_k = (8k+1)/(8k−1)`) going through the slot in descending speed; the link between passages; a chain of single readings across laps (E203) |
| **(v3)** entering queue, front | the readings outside the slot at a move, ordered by time to the entering edge `T_c = (7/8 − frac(c·t))/c`; the front is the least (E204) |
| **(v3)** copies 0 and 1 | in the band, the slowest reading's window `(7, 9)` splits the range into `[1, 7]` and `[9, 15]`; copy 1 is copy 0 re-arranged by the deviations (E122) |
| **(v3)** junction slack | `J = s_b(8k+1) − s_a(8l−1)`; on the slowest reading's grid it splits exactly into the grid's part (a whole number) and the deviation's part (E208) |
| **(v3)** class instant | the opening of a class's leaving-edge reading `a`, `t = c·n_a/(8a)`: after the pair law's rescaling, the grid through `a` with divisor `n_a`, class `c`, `c·n_a = 8K+1`. Every class instant is an opening, a candidate scale (E217) |
| **(v3)** certificate box, faces | at an opening `(h, K)` with lap `k_d` for each reading, the arrangements lonely there with the same laps: for fixed `h`, each `d` separately in `[(8k_d+1)h/(8K+1), (8k_d+7)h/(8K+1)]`. A face is one reading at its leaving or entering edge (E218). Boxes of different certificates overlap; the landing's region is its box less the boxes of earlier certificates (E219) (v3, repair). Each of E124's cells is a union of boxes, possibly more than one (precision note after E217) |

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

**(v3, repair)** On `grid_class_clear`'s small-deviation conditions: at most lonely openings some interior reading
deviates by more than `1` and is still clear inside its residue band (87,347 of 159,506 lonely openings, every 7-set of
readings ≤ 16; likewise on two other populations) `[VERIFIED — these populations]` (E217; `class_instant_run_v1.out`).

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
  (E156; off the path, E164–E166); `Cover8` (E166, E170; whether `Cover8 2 ⇔ NB(15)` is open); **(v3)**
  `BandRoute.WideStep8` (E212).

**F. (v3) The band and the band route.**

| fact | declaration | status |
|---|---|---|
| the band: `1 ≤ s₁ ≤ … ≤ s₆`, `7 ≤ s₆ ≤ 9`, every real shape lonely (E124's 105 certified cones, re-checked in Lean) | `BandCover.band_lonely` (`BandCoverN`, `BandCoverCoreN`, six `BandCoverTree*N`) | proved, tracked (`388793f`, E210) |
| the route: at most six readings (order seven), spread `≤ 7` (R1), spread 7–9 (`lonely8_of_band`), spread above 9 (`WideStep8 M`) | `BandRoute.lonelyRunnerAt8_of_wideStep8` (every `M`); `wideStep8_of_cover8` | proved, tracked (`edc9ad2`, E212) |
| `GridStep8 S m 1` gives a lonely instant with `1 ≤ 8mt ≤ 7`: a by-product, not the place; through it `WideStep8 1` is a first-lap cap on wide sets (`DoorFirstLap`'s shape) | `BandRoute.gridStep8_one_first_stretch` | proved, tracked; docstrings corrected `6107511` (E215) |
| `Cover8 M ⇒ NB(8⌊7M/8⌋ + 7)`: a uniform step bound is a time bound | E170 | `[reasoned; exact check]` |
| every `GridStep8` certificate names a clear candidate scale; `WideStep8 M` is Theorem 6.15 on wide sets plus a lap structure plus a cap | E217 | `[derived]` |
| `Cover8 2` holds, no set needs `M ≥ 3`, and only band shapes need `M = 2` | E210 (`cover8_check_v1.out`) | `[VERIFIED — these populations]` |
| `WideStep8 1` holds as written on about 140,000 wide sets, including 73,407 at the edge next to the band with a reading blocked at the bound; an adversarial walk found no wide set without a lonely instant in the slowest reading's first window (a truth check, F8) | E212 (`wide_step_check_v1.out`, `_v2.out`, `wide_first_stretch_walk_v1.out`) | `[VERIFIED — these populations]` |
| both `DoorFirstLap` refutations are band sets (spreads 7.469, 7.467) needing `M = 2`, first lonely at `R = 2401/234` and `165/16` | E217 note; memory `feedback_n8_cascade_is_the_oracle` | `[VERIFIED — exact]` |
| strips `[9,10]`, `[10,11]`, `[11,12]` of spread covered by certified cones (131, 168, 255) and independently checked in Python; `[12,13]` generated (308), not checked. Not in Lean; not wired (E209: strip by strip cannot close the unbounded spread; the owner asked for derivation over enumeration, E125); E212: the wiring would take them off the owed domain, not proposed | E125, E207, E209, E212 | `[VERIFIED — computer-assisted, Python]` |

**G. (v3) The cascade's run, derived facts** (on paper; each item's check is named with it) (v3, repair):
- D1: inside the slow part's clear interval only the fast part obstructs (E201). It is a corollary of
  `exists_block_iff_fast_lap` (`SlowBlockN`, `[PROVED, tracked]`, E200), on paper, not itself in Lean (E209). Checked in
  E201–E202, 0 violations.
- The index criterion: index 0 iff the fast part's push ends by `R = 7/σ` (E202; checked there, 0 violations).
- Inside a passage the setters go down in speed; the landing is a cluster bottom's exit (E203; E143; checked in E203).
  "Each cluster obstructs once" is **not** the mechanism: revisits in 4,885 chains to 24 and in every late shape (E203).
- The queue rule: a queue reading is carried in iff it reaches the entering edge before the setter leaves and is still
  in the slot at the move's end (E204, forced; its edge cases counted, not a violation count).
- The junction split `J = grid + deviation` (E208, algebra).
- A certificate's persistence region is a box, one interval per reading (E218 M4-1; checked at about 124,000 sampled
  arrangements, E219).
- Slowing a reading past its leaving face hands the landing to that reading's opening **unless** another reading's slack
  is used up there, or the change clears an earlier instant (E218 M4-3, as derived). Checked in E219: fine shapes, 1,694
  of 1,800 hand-off and 106 earlier; whole-number sets 1,404 hand-off, 153 earlier, **243 other** (a tight reading, or a
  change of order: the moved reading passing another, which M4-3 did not state). By M8 the 243 mean M4-3's derivation is
  incomplete: it assumed the moved reading keeps its place among the others. **To repair by derivation** (v3, repair).
- Speeding a reading past its entering face puts it in the way at the isolation instant; **if the run to that instant is
  unchanged**, the cascade's next move goes to that reading's next exit (E218 M4-4, derived). The 281 of 1,800
  fine-shape crossings that went to an earlier instant are that condition failing (E219). So under a single-reading
  change, the isolation is displaced only when a reading enters `[derived + VERIFIED — E219's populations]`.
- (v3, repair) The fast part's gap at the start is under one of its own laps except for crowds (one to four laps on
  these windows) `[VERIFIED — these populations]` (E205). **Not established:** why a non-crowded fast part's gap is under
  one lap, or how long a crowd's can be. Drift risks named in E206: (a) "the fast part's gap is under one of its laps"
  is a when-at-the-latest shape (F1) if made a lemma on its own; (b) crowds reached four laps on these windows; nothing
  says how far they reach.

**H. (v3) Our order-seven proof read for order eight** (E192–E195; paused as F14, E196):
- the residual is the translated hard branch at the bottom level: every residual set has a crowded level of
  non-multiples of 8 (cost `≥ 8`), with the multiples carried by order seven through their cofactors `[derived]` (E192);
- at `m = 1` the exceptions to `a/64` are the non-unit top level (32,514 of 32,642 orbits) `[VERIFIED — exhaustive mod
  64]` (E194);
- the `(1,6)` shape with the multiple's valuation `V = 3, 4, 5` is lonely at some `a/128` or `a/256`
  `[VERIFIED — exhaustive over residues; not in Lean]` (E195).
(v3, repair) Also: a crowded **interior** level never arises at order eight on this route `[derived]` (E192); freedom
not yet spent: the choice of `τ` among the cofactors' lonely instants, and dilations `[reasoned]` (E192); the
hard-branch tools and their state at 8 are in `docs/n8/Q6_ORDER_SEVEN_READ_v1.md` §3 (E192). At `V = 4`, for every odd
reading `d₀` the subject is lonely at some `a/128` with `a·d₀ ≡ 1 (mod 8)` `[VERIFIED — exhaustive mod 128]` (E196,
recorded as data).
These are case-list certificates the cascade does not produce (E196); they stand at their grades and are not the
cascade's mechanism.

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

**R10 (v3). The index** (E201–E207). With the split at spread `≤ 7`, the landing lies past the slow part's first interval
in 231 sets `≤ 24`, 9 Case C sets and all 5,400 late shapes `[VERIFIED — these populations]`. (i) A slow part of spread
5 to 7 (E202's counts: 7 in 210, 6 in 19, 5 in 2; E201 read its 240 as "7 or just under, 6.7–7", a discrepancy between
the two entries, not resolved (v3, repair)), or a crowded fast part (the late shapes); (ii) the slow part's own top
re-enters and its exit sets the next interval (E201), or the crowd's sweep outlasts the interval (E154, E202); (iii) the
same mechanism, a separation. The first route is an artefact of the split rule: at `s ≤ 3` no set in every set `≤ 24` and
none in the Case C samples lands past the first block, the late shapes excepted `[VERIFIED — these populations]` (E207).
**Answered on these populations**; the second route is the late band shapes (R12).

**R11 (v3). The 97 exceptions to `a/64`** (E193–E195). (i)–(iii) given for the 97 (E193, E194): a non-unit top-level
cofactor, repaired by the 2-adic modulus in 93. **Not understood (v3, repair):** the 4 sets left on the 13-grid and the
128 odd-cofactor orbits mod 64 were to be read by M3 next (E194) and were not; why one extra binary digit suffices is not
read (E195). All of it is case-list certification (§2 H), not the cascade's mechanism (E196).

**R12 (v3). The band** (E121–E125, E154, E207–E208, E210). Spread 7 to 9 is where the late shapes land in the slowest
reading's second block `[9, 15]`, where `Cover8` needs `M = 2`, and which `band_lonely` proves for every real shape.
(i) A crowded six above a single slow reading; (ii) the crowd runs out of shared blocks, the slowest reading sets one
move itself (its exit at `R = 9`), and the crowd lands one to five moves later (E154); in the chain's terms the deviation
bridges every grid gap of copy 0 (E208) `[reasoned from the run]`; (iii) the same mechanism. Every integer band set with
readings `≤ 28` lands in copy 0 (86,470 chains, E208); on E207's `s = 1` run (every set `≤ 24`, the Case C samples),
E208's integer band sets and the late fine shapes, only the late shapes land in copy 1. **Proved** (Lean) as a region; **the reason the 105
cells exhaust it is E125's open question** (§4).

**R13 (v3). The tight wide set** `(27720, 85358, 117495, 140959, 159149, 200880, 258489)` (E212, E214): the extremal set of
a search score, not an exception to an explanation (E215 item 3). Its two clear points are `GridPairLawN`'s mirror classes
3 and 5 on the grid through `117495` with divisor 5 `[VERIFIED — exact]`. Scoped by E217 `[VERIFIED — these
populations; a scoped null]`: beyond the pair law's hypothesis the mirror is lonely at 15,003 of 73,613 mirror
evaluations (70,403 openings) on every 7-set of readings ≤ 16, at 7,459 of 32,736 (28,198 openings) on 2,000 uniform
7-sets ≤ 200, and at 1,831 of 8,547 (7,312 openings) on 1,000 fine shapes. **Answered for that set; not a general
mechanism.** (v3, repair) A two-instant form of the pair law (the pair cannot block both classes) is a candidate lemma,
recorded and not proposed: with "the others clear at both instants" among its hypotheses it is close to a restatement
(E214; F4).

**R14 (v3). The landing under speed change** (E217 B′, E219). Over 10,954 sweep steps the landing's opening changed 16
times: 10 to an earlier opening (the by-product), 6 destroyed each by exactly one reading entering, 3 of those moving to
that reading's own exit and 3 to another's `[VERIFIED — these sweeps; small counts, recorded, not a law]`. Across faces
(E219): leaving faces are hand-offs under E218 M4-3's conditions (§2 G); across an entering face, on 1,800 fine-shape
crossings, the entering reading's next exit is lonely in 746, an earlier instant is cleared in 281, and in 773 one to
three readings are in the way at that exit and the relay continues `[VERIFIED — E219's populations]`. **Derived in kind**
(the move rule); **not understood**: which crossings end at the entering reading's exit.

---

## 4. Open questions (map questions; none is a mechanism)

- **Q1** (v2's "next"; not active, see the status line below (v3, repair)). In each set, why do the rungs `q < q_min` fail: multiples not spread, or every unit blocked, and by
  which readings.
- **Q2.** The rung budget's 1,329 failures on `[1,40]`: which blocked units coincide, and whether the link lemma
  accounts for every coincidence.
- **Q3.** What in the readings' arithmetic sets `q_min`, and how it grows with the window (E175's rung `q` = 9–11. v21
  §17D's 12, 15, 16 are rational-opening resolutions `N`, a different parameter).
- **Q4 (the step, class (c)).** An argument uniform in `q` that some rung has spread multiples and a free unit.
- **Q5. The interim reduction** (owner, E189). At a fixed `q` the rung's conditions see a reading only through whether
  `q` divides it, its residue mod `q`, and the wall-cut cell of its reading at `1/(8e)` (walls `1/8 − r/q`,
  `7/8 − r/q`) `[reasoned; derived on paper, not checked, not in Lean]` (E189's grade (v3, repair)); so at fixed `q` finitely many classes, defined by the
  readings alone (never by loneliness, E145). Walls, not boxes, as in E123–E124 (coincidence not checked). **Open:**
  `q` itself (least `q` 9 on `[1,30]`, 16 on `[1,40]`, `rung_selection_v1.out`). E190 adds the split at `q`
  (multiples carried by cofactors; non-multiples to place) as the constraint the reduction exploits. **Open from E190
  (v3, repair):** the split profile of each set across `q` (how many readings each `q` divides, with their cofactors),
  read against `q_min` (E188) and the residual; and which restriction of the model instant the non-multiples need when
  the split leaves several of them. E192: the positive-arithmetic fields alone reduce the residual to one shape, a
  crowded level of non-multiples of 8 (cost `≥ 8`) `[derived]`.
- **Q6 (new, E190/E191).** The native order-seven proof ends every case at a residue-band certificate at modulus `7P`
  by unit filtering, using only that every nonzero residue mod 7 is a unit (v21 §17A). Mod 8 the non-units are the even
  residues. Does our order-seven architecture carry one order up with the non-units treated separately, and is the
  residual's organisation by multiples of 8 (shapes `(1,6)`–`(4,3)`, one non-multiple `≡ 4 mod 8`) that separation?
  (§9 C5.) **Partial answers (v3, repair):** the architecture carries through the easy branch; its hard-branch mechanism
  rests on T7 throughout and does not carry as it stands `[derived]` (E192). Translated to one prime power it does not
  settle the crowded level even at `m = 1`: order eight's hard branch is multi-resolution `[VERIFIED — readings ≤ 24]`
  (E193). It carries further once the top level is taken 2-adically `[VERIFIED — exhaustive mod 64]` (E194). The line is
  paused as F14 (E196).
- **Standing question answered:** v21 §17B / the proof-shape review's Finding 1 asked whether `EightResidual` is the
  obligation or a sufficient route. `lonelyRunnerAt8_iff_residual` proves it is the obligation (§9 C1).
- **(v3) Status of Q1–Q6.** Q5 and Q6 were taken up in E192–E195 (§2 H) and paused as F14 (E196). Q1–Q4 were not
  pursued after the owner's rulings of E196–E197; they are rung questions (a family the cascade does not use directly)
  and stay recorded, not active.
- **(v3) Q7 withdrawn** (E215): "why the slowest reading's first clear stretch closes only in the band" had the first
  window as its object and covering as its question (§6 F15).
- **(v3) The central open statement, reached from six sides** (E151, E158, E202–E205, E206, E208, E219): **why the
  carrying-in stops inside the block** (`CASCADE_DESIGN_v2` §4; "inside the block" is the place qualifier (v3,
  repair)). In the cascade's objects (`CASCADE_DESIGN_v2` §4): the chain continues exactly while, during each
  separation, some reading is carried over the entering edge; the landing is the first separation that carries no one
  in. In the arrangement's objects (E125, E219): why the certificate boxes (each lap-assignment cell a union of them) exhaust each region of
  the gap simplex. Both are the obligation until a derivation names **where** the readings sit at the last separation
  (a place), not that it stops (§5; F1).
- **Q8 (v3; the owner, 2026-10-01). The complete account of the cascade.** Know what the cascade does in every
  configuration, derived from its definition, with no gaps: the step (every configuration of the crowd and the queue at
  a move), the patterns of steps (passages, bridges, relays, hand-offs, entering-face crossings), and how the run is
  placed by the arrangement (grid plus deviation, the split, the simplex). Each claim is derived first and a run only
  checks it (M8). Design pending: `CASCADE_DESIGN_v3` (§7).

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
- **(v3)** "Some grid-class instant is lonely" with the divisor unrestricted: every opening `(8K+1)/(8h)` is the class-1
  instant of the grid through `h` with `mm = 8K + 1` (E216 M4-6; `RegimeSkeletonN.lean:20`).
- **(v3)** "Every relay started at an entering face ends in a box": the cascade's arrival (E219; `doors_agree`).
- **(v3)** "The boxes exhaust the arrangement space" (each of E124's lap-assignment cells is a union of boxes): Theorem 6.15 read over arrangements; E125's
  question, which a derivation must answer by place (E219).

---

## 6. Failed attempts, by methodological class

| class | the failure | instances (entry) |
|---|---|---|
| **F1** imported shape: *that* or *when* it stops | a rank, fence, move budget or exhaustion names no place | E170 quantity tests; E170 "a non-isolating chain runs a full period"; E171 waves ("at most seven moves"; E172); E177's reviewed step (flagged, not run); Props 6.10–6.11 withdrawn (v21 §6); `DoorFirstLap` (a cap, `[REFUTED]`); v1 of this map's §2A "at most 7 moves" (compile-diff A1); **(v3)** E195 read in the cascade's terms (the landing no later than the first lonely grid instant, E196); `WideStep8 1` as a first-lap cap and `Cover8 M` at any uniform `M` (E215 item 4, E170) |
| **F2** a rate given as the answer | coverage, a share of instants, a reach percentage | E171 (E172); reach percentages (`reach_scheme_dependence_v1.out`); E84 tallies; v21 §17E: top-pair mirror meetings (2,994 against a null of 2,991), extra laps ("Not to be pursued as a mechanism") |
| **F3** a majority rule stated as a law | the rule holds on most sets and is taken as the mechanism | E64 "the same word repeats"; E57's block law `13/4` and E66's "every runner sets at most twice" (E68); E129–E130 "the unsettled are captured readings"; E160 "one unresolved pair"; E185's first-interval statement; E111's entering-edge proxy ("the proxy is wrong, not the cascade"); **(v3, repair)** E214's "140 of 155" leaned this way (flagged, E215) |
| **F4** a restatement taken for a step | an equivalent of the obligation presented as progress | E145 "every arrangement has a type"; E159 "'the separations come to rest' renames the conjecture"; E163 "no return"; E173; E137 (the exact block condition *is* loneliness at that instant); O9 (E143's rotation form is Theorem 6.15); E187's (B) at the target |
| **F5** a forced fact found after the data | a count the definitions force, reported as a finding | E136, E143, E150, E152 (each recorded as forced); E176's 320/320 (E177); E185's one-slot check; E187's `c` in the host's slot; E188's "never later"; v21 §17D's last row (§9 C4); **(v3)** E212's first edge population (bound-clear by construction) and "one pair at both ends"; E214's class `e` (another interval already clear); E217's "the landing is a class instant" (inside the search window); E214's "`R ≥ 9` after closure" (the slowest reading is in the way on `(7, 9)`) (v3, repair); the inverse, a forced fact stated wrongly: E216's M4-3 (caught by its own check) |
| **F6** an unrestricted parameter | the statement then describes any instant | E176 (E177); E129–E130's control against tautology; E188's `q_c`; E190's free model instant |
| **F7** the record not read | a step re-derives or re-proposes what is on disk | O2, O3, O6 (the pre-use grep skipped); E172 (E170's correction to E114 already on disk); E184 (E178–E183 re-derived E113–E115); E187's residue form (v21 §15) and host rule (§17E); O10 recurring E174–E187; E190's "the converse is not an `↔` in Lean" (`lonelyRunnerAt8_iff_residual`, E104); v21 §17B and the review still asking what that theorem answers; **(v3)** E209 read E157's divisor `mm` as `Cover8`'s `M` (E210); E217's "`M` is time" re-derived E170's NB(X); E219 re-arrived at E125's question (a sixth side) |
| **F8** a false `def … : Prop` | type-checked, never proved | `DoorFirstLap`; `Cover8` without the card bound (E170, fixed `3ea9feb`) |
| **F9** a frame error | the statement leaves the framework's objects | a stationary runner (E75; `region_lonely`, E186); pre-registration language on LRC (E172) |
| **F10** a continuation asserted, not derived | "it goes on the same way … which always happens" | E151's retraction |
| **F11** a new vantage in place of reading an exception | exceptions end a line of work | E174 → E175 → E178–E183 → E185 → E187 (O10; E188) |
| **F12** a range-forced result (new) | a regularity true only because the window is small | O7 ("the slowest runner never leaves its first block", range-forced; again E151, E153) |
| **F13** a consequence not drawn (new, M7) | something proved and used only for the route it was built for | §9; **(v3)** `band_lonely` proved (E169) and imported by nothing until E212 |
| **F14 (v3)** an instant family the cascade does not use | pursued in place of the cascade's mechanism, the cascade reduced to an oracle check | E193–E195 (order seven's multipliers at `8·2^V`); E186's double-and-backtrack; the relayed `2t, 3t, 5t` candidates (E196); E217's Part B first form (designed in E216), every lonely opening in a window (v3, repair: the entry is E217, not E214) |
| **F15 (v3)** a proved by-product promoted to the object | a true consequence (often a window or cap) is named "the place" and becomes a question's object, score or pass condition | E211 F-d → E212 ("the place `WideStep8 1` names", graded `[PROVED]` by the place test) → Q7 (E213–E214): register v3 items 15 (the first window), 4 (covering) and 2 (blocking), as E215 cites them; item 8 (set emptiness) is the memory's match, not E215's (v3, repair); the hard-case walk ranked by the widest clear interval (E212); `WideStep8 1` a first-lap cap (E215 item 4). Record: E215; memory `feedback_n8_cascade_is_the_oracle`, recurrence 2026-10-01 |
| **F16 (v3)** a proxy count taken as evidence of the object | a count of words or tokens stands in for the object it is meant to show | E215 item 2 ("the words appear 6, 9 and 10 times": the substring `cover`, all six E212 hits the names `Cover8`, `wideStep8_of_cover8`; withdrawn, log after E217); the gate-count proxy (memory: the 4,749/4,748 count) |

---

## 7. Coordinates of the next step

**(v3)** The next step is **Q8, the complete account of the cascade** (owner, 2026-10-01), designed before any work in
`docs/n8/CASCADE_DESIGN_v3.md` and approved by the owner before it starts. It builds on `CASCADE_DESIGN_v2` (§1–§7: the
owner's design, the move, transport, the grid instant, separation, the recursion, the one question) and on §2 F–H here.
Discipline (M8): derive first; a run checks a derived statement and has no other pass condition; an exception repairs the
derivation. v2's §7 (Q1 as a rung map run) is superseded.

---

## 8. Owed

- **(v3)** `compile-diff` of v3 against v2 and log E189–E219 (it discharges v2's own owed run against v1 and E189–E191).
- The three answers for R3's budget failures and for R8.
- §9's Lean items (C2) and manuscript corrections (C1, C4), each to the owner. **(v3)** The owner has put the manuscript
  behind the Lean tree (E192); the corrections wait.
- **(v3)** The owner's decision on the cap in `WideStep8` (E215, E217): the route holds for every `M`; the native content
  of the owed statement is the lap structure.
- **(v3)** `CASCADE_DESIGN_v3` (Q8), for the owner's approval.
- **(v3, repair)** v21 §17G's pending author's ruling on first-lap clearance (§15I; provisional since 2026-09-25):
  `WideStep8 1` neither uses nor settles it (note after E212).
- **(v3, repair)** `CASCADE_DESIGN_v2` §6's four design questions: questions 1–2 (the carrying-in read on the grid; why it
  stops inside the block) are `CASCADE_DESIGN_v3` §8's gap D2; question 3 (the nest) is gap D4; question 4 (the
  recursion's exceptions, E150's 772) is gap D5. None is answered.
- **(v3)** Other sessions' uncommitted and untracked Lean (`gridStep8_two_bounded` in `RegimeSkeletonN.lean`; `CascadeGridN`,
  `PinchReflectionN`, `PartialReflectionN` and others in `Spec/`): not this map's to commit; recorded so no step rests on
  them unseen.

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
  density premise. `[reasoned]`. **(v3, repair) Refined by E194–E195:** at `m = 1` the per-resolution question becomes
  the top level's 2-adic valuation `V`, then residues at a fixed modulus: closed exhaustively at modulus 128 for `V = 3`
  and `V = 4`, and 256 for `V = 5`. At `V = 3` the modulus `64 = 8·2^V` leaves 128 exceptional orbits (§2 H, §9 C10).
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
  proved. The log has not returned to it. **Consequence:** Q6. `[reasoned; not examined]`. **(v3, repair) Examined in
  E192–E195:** see Q6's partial answers (§4) and §2 H; paused as F14 (E196).
- **C6. One template across the reductions** (E190): N2, the case list's descent and R8, and the rung-selection rule
  share one shape (merge to at most six readings; order seven; a freedom spent inside the slack). **Consequence:** the
  rank-one cases are instances of the reduction that settled the real case; Q5's reduction is to be sought in that shape,
  with its restriction stated (M6). `[reasoned]`.
- **C7. Earlier maps never cited.** `EXISTENCE_MAP_v1`–`v5`, `WITNESS_MAP_v1`, `DEPTH_MAP_v1`, `CASE_B_MAP_v1` and others
  in `docs/n8/` are cited nowhere in the log (`grep -c "_MAP"` returned 1 before E190; **(v3)** corrected from "before E189", E192). **Consequence:** their content has
  not been checked against this map; owed.
- **C8. The path route duplicates N2.** Both reduce real arrangements to whole numbers; the path route's (B) is the
  whole-number obligation at the target (E116, E187), and its remaining halves (multi-pinches, bounded time) are open.
  E178–E186's work proved local stability along deformations. **Consequence:** the path route adds no reduction beyond
  N2; effort there bears on `hopen`, which N2 does not need. `[reasoned]`.
- **C9 (v3). The residual is the hard branch at the bottom level** (E192). Every residual set carries a crowded level of
  non-multiples of 8 with the multiples carried by order seven. **Consequence:** the open statement sits inside the case
  list at one level; the easy branch at eight is inside descent. `[derived]`.
- **C10 (v3). The `(1,6)` shape for `V = 3, 4, 5`** (E195) `[VERIFIED — exhaustive over residues; not in Lean]`.
  **Consequence:** a case of the case list at a fixed modulus; not the cascade's mechanism (E196). **Not closed (v3,
  repair):** `V ≥ 6` (the modulus must grow with `V`; uniformity in `V` is not supplied); the shapes `(2,5)`, `(3,4)`,
  `(4,3)` are not checked; the reason each pattern class has its instant is not read (E195).
- **C11 (v3). The stricter split** (E207): with the slowest reading alone as the slow part, every set in the populations
  tested lands in its first block except the late band shapes, which land in its second (the integer band sets land in
  copy 0, E208) (v3, repair: v3's first draft said "the band"). **Consequence:** E121's target `R ∈ [1, 7] ∪ [9, 15]`
  reached again from the cascade's run. (Read with F15: the first block is a coordinate here, never a requirement.)
  `[VERIFIED — these populations]`.
- **C12 (v3). `band_lonely` wired into a route** (E210–E212). **Consequence:** the owed statement is `WideStep8 M`,
  implied by `Cover8 M` at every `M`; `Cover8` stays registered. `[PROVED]` for the route.
- **C13 (v3). The owed statement's content** (E217; E170). Every `GridStep8` certificate is a clear candidate scale with
  a lap structure, and a uniform `M` bounds its time. **Consequence:** the native content of `WideStep8` and `Cover8` is
  the lap structure; the cap is not native (owner's decision owed). `[derived]`.
- **C14 (v3). Displacement only by an entering reading** (E218–E219). **Consequence:** under a change of one reading's
  speed the isolation is carried across leaving faces by a hand-off, under E218 M4-3's conditions and with its 243
  unexplained exceptions (§2 G), and displaced
  only when a reading enters its slot at the isolation instant `[derived + VERIFIED — E219's populations]`. That the
  relocation then follows the cascade's move rule from that reading's exit is `[reasoned]` (E219). This is the owner's
  *"each isolation is pushed there by the speed"*, stated for single-reading changes (v3, repair).
- **C15 (v3). The persistence boxes make up E124's cells** (E219; each cell a union of boxes, precision note after E217
  (v3, repair)). **Consequence:** asking why the boxes exhaust the
  arrangement space, or why every entering-face relay ends in a box, is E125's question and the obligation (§5). Runs of
  the discover-and-test kind on these objects will keep re-arriving there; the owner's Q8 (derive what the cascade does
  in every configuration) is the response (§4, §7). `[reasoned]`.

---

## 10. (v3, repair) Run artifacts for E192–E219

Under `LonelyRunner/experiments/nN/redo/` unless stated: `crowded_level_v1{,b}` (E193); `crowded_m1_cover_v1.c`,
`crowded_m1_cores_v1` (E194); `crowded_m1_cover_v2.c`, `_v3.c`, `crowded_m1_cover_E195.out` (E195); `crowded_m1_cover_v4.c`,
`_partial.out` (E196); `e151_block_v1`, `_v2` (E201); `e202_index_v1` (E202); `e203_sweep_v1` (E203); `e204_queue_v1`
(E204); `e205_fast_spacing_v1` (E205); `e207_split_v1` (E207); `e208_band_junctions_v1` (E208); `cover8_check_v1` (E210);
`wide_step_check_v1`, `_v2`, `wide_first_stretch_walk_v1`, `wide_first_stretch_pins_v1`, `wide_first_stretch_tight_v1.out`
(E212); `q7_map_run_v1`–`_v3` (E214); `class_instant_run_v1`, `_v2` (E217); `persistence_run_v1` (E219). Lean:
`LRC/Spec/BandCoverN.lean` and its trees (`388793f`), `LRC/Spec/BandRouteN.lean` (`edc9ad2`, `6107511`); build and axiom
logs `experiments/nN/band_lean_build_v1.log`, `band_cover_commit_build_v1.log`, `band_lonely_axioms_v1.out`,
`band_route_build_v1.log`, `band_route_axioms_v1.out`, `band_route_spec_gate_v1.out`. Documents: `docs/n8/Q6_ORDER_SEVEN_READ_v1.md`,
`CASCADE_DESIGN_v1.md`, `_v2.md`, `_v3.md`.
