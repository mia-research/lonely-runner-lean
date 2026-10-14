# Order eight — the mechanism map, v5

2026-10-03. **A working map, not the record.** v5 = v4 unchanged + §11 (log E269–E330). Supersedes `MECHANISM_MAP_v4.md` (retained unchanged); v4 superseded `MECHANISM_MAP_v3.md` (retained unchanged; v2 and v1 likewise).
v4 adds log E220–E268: the complete account of the cascade, Levels A–C (E220–E223, E226); the owner's corrections of the
obligation's form and of imports (E225, E230, E251); Level D re-aimed (E224) and read inside the hole configurations
of `Order8SkeletonN` (E227–E243, with the record of every isolation, E240–E241); the `f = 6` case taken to flank terms
(E244–E253); the re-aim at `EightResidual` and its three routes meeting at one statement (E254–E256); shadowing across
the slow runner's band run (E253, E257–E258); and the flank reading of the C1-shape on `EightResidual`'s members
(E259–E268: the fastest-flank line, its refutation, the slowest flank, the joint cover). Text carried from v3 is
unchanged except where marked **(v4)**. The record is `docs/n8/RUNNING_LOG_order8_v1.md`; the manuscript of record is
`docs/n8/MANUSCRIPT_v21.md` (the Lean tree leads it; owner, E192, E227).

**Two names to keep apart (v4).** "§9 C1" is this map's register entry, *the residual is the conjecture*. "The C1-shape"
(E118; written C1 in the log) is a *configuration*: one slow runner `c` below a six-reading cluster, and the open
statement that sits inside the residual (§4 Q9). The log's `Map:` lines write both as C1; below the second is always
"the C1-shape".

**Scope:** log E100–E268, including the second series E36b–E48b physically inside it (log lines 3458–3837; E106), and
v21 §15–§17E. It is not a complete summary of the log: open items in range that bear on nothing here are listed in v1's
compile-diff report part (C) (`MECHANISM_MAP_v1_COMPILE_DIFF_v1.md`), not carried. v3's report
(`MECHANISM_MAP_v3_COMPILE_DIFF_v1.md`) covers E189–E219. `compile-diff` of v4 against v3 and log E220–E268 is owed before
reliance (§8) and, when run, is recorded in `MECHANISM_MAP_v4_COMPILE_DIFF_v1.md`. Read the entries after the last one in
scope before relying on this map.

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
- **(v4) The owner's rulings of 2026-10-01 and 2026-10-02, in order** (log entries as cited).
  - E220: *"We keep proposing mechanisims, testing them and finding exceptions. We should really know and understand what
    the cascade does in all configurations … There should be no gaps in what we understand should happen"* (already
    in v3 §0). Approved the complete account (`CASCADE_DESIGN_v3` §8) in E221.
  - E222: *"Yes we are not looking at lean until the map is complete"*. **Lean work is on hold**; the scope and end
    condition of "the map is complete" are undefined (memory `project_n8_lean_on_hold_until_map_complete_2026_10_01`).
    The catalogues cite existing Lean declarations as anchors (reading, not building); this supersedes `CASCADE_DESIGN_v3`
    §8.7's clause that Lean follows each derived item.
  - E225: *"So why did you ask rather than read the results we have already documented. Documentation is only good if
    you bother reading it"*. Before any question to the owner: search the log, this map, the catalogues and the Lean tree
    (pre-use check, step 0); a question goes to the owner only for what is not on disk. And: *"First isolation isn't
    needed by the conjecture"*; answered from the record, `first_isolation_of_fixed` `[PROVED]` (§9 C17).
  - E227: *"Remember that lean now outpaces the manuscript, handover and paper documents"*. The Lean tree is the first
    source read for a target.
  - E230: *"Are you sure or are you making additional requirement for what looked like proof in the past?"* **The
    obligation is `∃ (e, k)` on conditions that, with the proved cases, are jointly exhaustive, by any means**
    (`MANUSCRIPT_v20` §0, 2026-09-24). A uniform theorem, naming the instant, and a cap are foreign shapes; an
    existence argument by contradiction or pigeonhole is admissible; a case proved is proof of that case (§9 C18).
  - E232: *"Im lost, we have holes, the cascade does not fail at these holes so then what are we missing. Understanding
    how the cascade approaches these holes so we can figure out the mechanisim?"*. E236: perturb the paths through the
    cascade; E239 (owner): *"we can now construct rather than search to be able to look for the mechanisim"*; E240:
    *"Maybe we should be keeping a record of what other isolations there are other than the one cascade points to"*.
  - E242: *"Can we close that hole and then move to formalise it?"*, with the plan (1 extend the population, 2 construct, 3 read the native reason in flank form, 4 formalise): *"Yes start with step 1 and then 2"*; E247: *"Yes"* to step 3. Step 4 stands under the E222 Lean hold.
  - E251: *"Ok, please check that we are searching for a native object and it is not just a similar shaped object as
    other frames pretending to be helpful"* (the check, and what it excised, is §6 F1 and §2 J's E250 bullet (the drift lemma), §2 K and §6 F1 (`Q` and the blocked stretch as evidence)).
  - E252: *"Yes please and please try to reason and think it through, any time you do not we just end up with another
    attempted import"*. E254: the lower orders' native proofs are the template to read from (§9 C19).
  - E259: *"making sure you are measuring and deriving the framework and not importing anything"*. E263, E265, E267
    approvals (*"yes"*, *"We better figure that out"*, *"yes, run both"*) are for the steps they name.
- **(v4) Session findings kept with the method** (the session's, not owner rulings):
  - *A count on a constructed sample is a count on that sample.* E260's "the fastest flank is free or its near-twin chain
    ends free: 547 of 547" read as a regularity of the C1-shape; under 10 more seeds of the same construction the
    fastest flank was a hand-off in 6 of 5,431 (E264). The test that works is E263 Part 3's: build members of
    `EightResidual` (the fields satisfied by integer adjustments) while holding the structure in question fixed; if the
    construction reaches membership with the structure intact, the statement is false there (271 of 348 runs in E264;
    287 of 480 in E268). The control (the same climb without the constraint) is part of the test.
  - *Say which object a count is about.* E264 wrote "the landing is at rank 1 or 2" from counts of which flanks are free;
    the landing is a different object and is at ranks 1–6 (E266). The correction is in §6 F16.
  - *An independent re-reading of an exception comes before it is carried.* The six hand-off members of E264 were
    re-checked by direct `circDist` (not the residue test) before being logged.

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
| **(v4)** setter, crowd, wall | the setter of a move is the crowd member with the latest exit; the crowd is the readings in the slot; a wall is a hyperplane `b(8k+1) = a(8j ± 1)` in the speeds (edge forms; E221–E223) |
| **(v4)** core, block, `f` | in a hole of `Order8SkeletonN` the `7 − f` slowest readings (core, largest reading `m`) below a block of `f` readings with `x₁ ≥ 9m`; `ArrBlockRule8 f 9` (E231) |
| **(v4)** core stretch `S_k`, entry instant, `g`, `b₀` | `S_k`: the core's `k`-th lonely stretch from `τ_C`, the core's own landing; entry instant `t₀`: where the cascade enters a stretch (`τ_C`, or the start of `S₁`); `g`: the block's relay landing from `t₀`, the least clear block-flank opening at or after `t₀`; `b₀`: the end of `S₀`, where a core reading reaches its entering edge (E233, E237, E239) |
| **(v4)** flank, walker, band run | a reading `e` as a flank: openings `u = 8k+1` (`d·u/e`); a walker is any other reading, in the way iff `d·u mod 8e ∉ [e, 7e]` (Theorem 6.14). `c`'s band run at `e`: the openings with `c` in `[1, 7]`, `u ∈ [e/c, 7e/c]` (E252) |
| **(v4)** line reading | at flank `e` and opening `u` a walker's reading is `ρ_j = A_j + ε_j·u (mod 8)` with `x_j/e = A_j + ε_j`, `A_j` whole, `|ε_j| ≤ 1/2` (E253; exact on every opening of 5,978 members, E266) |
| **(v4)** near-sharer, twin below, near-harmonic | a walker that stays in the way across `c`'s run: `|ε|·(u_hi − u_lo) < 2` and `A mod 8 ∈ {0, 1, 7}` with the block-keeping sign (`(1, −)`, `(7, +)`, `(0, ±)`) (E253, E266). The twin below is `(1, −)`: a reading just under the flank. A near-harmonic is one at `A ≥ 7` |
| **(v4)** hand-off, segment | a flank shadowed across the run by several walkers in turn, none at all of it; a segment is a stretch of openings with one occupant (greedy, E257) |
| **(v4)** C1-shape, cluster, rank | `c` the least reading, six others (the cluster) at least `9c` (E118's members at least `25c`); the cluster's flanks ranked 1 (slowest) to 6 (fastest); `EightResidual`'s members of this shape are E118's constructions (E118, E256) |
| **(v4)** isolation record | every core stretch of `(0, 1/2]`, which hold isolations, and the block relay landing `g_k` of each (E240–E241) |

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
  **(v4) Repaired by E223 (C.4, C.5):** E219's exceptions are effects of moving a reading a finite distance across other
  walls; at an infinitesimal crossing the leaving face is a hand-off and the entering face's next move is the entering
  reading's next exit, unless the face is also a face of an earlier box `[derived; checked in E223: 0 failures after
  two repairs; 300 + 300 + 300 sets]`.
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

**I. (v4) The complete account of the cascade, Levels A–C** (E221–E223; catalogues `docs/n8/CASCADE_ACCOUNT_LEVEL_A_v1.md`,
`_B_v1.md`, `_C_v1.md`; crosswalk to the record `CASCADE_ACCOUNT_CROSSWALK_v1.md`, E226). Each item is derived from the
definition and checked exactly (M8); **all are forced and none is progress on the obligation** (§5; F5). E226: most of
Levels A–C restates v21 §6.1–§6.6, §6.9–§6.15, Theorems 6.2–6.3, 6.19, 6.23–6.24 and E142–E143, E178–E183; what the
greps did not find, so the account's additions, are B.4, B.8, C.3, the resolution of E219's exceptions as finite-travel
effects, and the count of landings by pass-through.

| item | statement | status |
|---|---|---|
| A.1–A.2 | the move advances and no lonely instant lies inside it; every cascade instant after the bound is an opening, a candidate scale | `[PROVED]` |
| A.3–A.5 | the setter is the crowd member with the largest remaining distance to its leaving edge relative to its speed; the step is a rotation of every position by its own speed read at the setter's exit; the next crowd is the arrivals and the re-entries (a re-entry needs `D > (7 − x_c)/(8c)`) | `[derived]`; `SeparationN.transport` is the centred case `[PROVED]` |
| A.6–A.7 | three move types; the setter is never in the way at its own exit | `[PROVED — SweepBridgeN]` |
| A.8, A.10 | the landing's certificate; the setter is the slowest of its lap-`K` cluster; the bound's captures are grid slots 7 and 0 | `[PROVED]` / `[derived]` |
| A.9 | **the landing is the first isolation**: `bound_le_of_lonely`, `move_le_of_lonely`, `iterate_le_of_lonely`, `first_isolation_of_fixed` (`Cascade/Iteration.lean:198, 107, 184, 213`; v21 Theorem 6.2); independently the landing equals the earliest lonely instant in 6,436 of 6,436 sets (`cascade_first_check_v1.out`) | `[PROVED; VERIFIED]` (E225) |
| B.1–B.3 | the setter is the latest exit; at the setter `a`'s exit on lap `k`, reading `b` is in slot `l` iff `s_a(8l−1) < s_b(8k+1) < s_a(8l+1)`; the slower readings in the slot form an unbroken run within ratio `ρ_k` below it | `[derived]` |
| B.4–B.6 | a sweep step jumps to the bottom of that run; passages descend through consecutive ratios below `ρ_k` to the lap cluster's bottom or end at a bridge; bridges up or down | `[derived]` |
| B.8 (gap B4 closed) | the next setter is the queue front iff the front is in the next crowd and no member exits later; an arrival outlasts it iff its entry lag exceeds the difference of their stays, unless the front itself lapped. *Corrections before commit:* the first draft said "only by being slower" (false for a faster arrival entering late); the check found 35 moves where the front had lapped | `[derived; checked]` |
| B.9 | the chain ends iff nobody is in a slot at the exit: a gap in the arrivals or the front passing through (landings by each: 27,213 / 1,102 on sets ≤ 20; 515 / 30 fine; 2,927 / 2,473 late shapes; data, not laws) | `[derived; checked]` |
| C.1–C.2 | a finite chain is decided by the signs of finitely many forms, linear and homogeneous in the speeds, all **edge forms** `b(8k+1) − a(8j ± 1)`; off every wall nearby arrangements have the same chain | `[derived; checked: 2,301 perturbations]` |
| C.3 | a tie wall is an edge wall on the leaving side; at an intermediate move crossing it relabels, at the final move it is the landing's leaving face, a hand-off. *Repair:* the first draft said a tie never changes the landing; 54 final-move crossings did | `[derived; checked]` |
| C.4 (gap C2 closed) | crossing a wall at an intermediate move changes the route, never the landing, unless the wall is also a face of the landing's box or of an earlier certificate's box: the routes rejoin at the landing at the latest | `[derived; checked: every changed landing is also a face of the landing's box]` |
| C.5 (gap C2a resolved) | at an infinitesimal crossing of the landing's faces: leaving face is a hand-off; entering face's next move is the entering reading's next exit; neither makes an earlier landing unless the face coincides with an earlier box's face. *Repair:* 4 crossings were coincident faces, read on `(1,3,4,5,6,7,8)` (reading 4 at `21/5` is on the entering face and on its own leaving edge at the earlier instant `15/56`) | `[derived; checked: leaving faces all hand-offs (317, 324, 225); entering faces go to the entering reading's exit (278, 51, 233 lonely there)]` |

Checked populations (exact): every 7-set of readings ≤ 20 (77,520 sets, 60,742 moves), 1,000 seeded fine shapes, the 5,400
late band shapes (Levels A, B); 300 + 300 + 300 sets, crossings at relative distance `10⁻⁹` (Level C) `[VERIFIED — these
populations]`, 0 failures on every item after the repairs. Re-entries are real but rare (162 in 106,735 moves of the late
shapes). Edge cases counted as derived (A.11): 1,729 readings exactly on an edge in the whole-number sets; tied setters 23
and 1. **Consequence in E223:** with Levels A–C the isolation moves continuously except when a reading enters at it, and is
then carried by the cascade's ordinary moves; what is left is *where the relay started by an entering reading lands*
(Level D, §4 Q8).

**J. (v4) Level D read in the hole configurations, and the lower orders' template** (E227–E243, E254–E256).
- **Level D as cases is `Order8SkeletonN`'s five holes** (E231): `lonelyRunnerAt8_of_arrangement_holes` gives
  `LonelyRunnerAt8` from `ArrBlockRule8 f 9` for `f = 3, 4, 5, 6` and `ArrBoundedCovered8 9` (`f = 1, 2` proved: R8, the
  fast pair) `[tracked, Lean]`. For `f = 3`, from proved lemmas, a core of four at `θ = 1/5` below a block with
  `x₁ ≥ (35/3)·m` is lonely, leaving the strip `9m ≤ x₁ < (35/3)m` `[derived from proved lemmas; no Lean instance (E222)]`.
  For `f ≥ 4` nesting equal speeds is invalid (`x·needT_{f−1} = (2^{f−1} − 1)/4 > 3/4`).
- **The cascade inside a hole is two lower-order cascades composed** (E233, E235; 2,000 configurations at `f = 3`, 1,000
  each at `f = 4, 5, 6`; scripts `hole3_cascade_v1`–`v3`, `holef_cascade_v1`) `[derived from A.1; checked F1, F2, C1; 0
  failures]`: before `S₀` the core relays (406 of 411 moves); inside a core stretch only block readings set moves; from the
  path's first instant in a stretch the path is the block's own relay; the landing is the block relay's landing in the first
  stretch where it lands before the stretch closes. Order 5 (core of four) and order 4 (block of three) are native.
  Overruns (landing in `S₁`): 28 of 2,000 at `f = 3`, 2 of 1,000 at `f = 4`, 0 at `f = 5, 6`.
  Exceptions read (M3): the 28 overruns are `S₀` shorter than the block relay, the core relaying from the gap to the start
  of `S₁`; the 5 not passing through `τ_C` have a block reading in the way at the core's last move whose exit is later; the
  single-point stretch for the core `(70, 490, 729, 1000)`; same mechanism in all.
- **Perturbation through the cascade** (E236–E237; 403 one-reading walks, R0 at every grid and bisection point, 0
  failures): the full set lands in `S₀` exactly when `g ≤ b₀`, and the landing leaves `S₀` only at the wall
  `h(8k+7) = c(8K+1)`; E1′ (moving `h` alone reaches the wall exactly when every other block reading is clear at `b₀`);
  late entries change the route, not the landing (T1, 6 of 6). The first run's 14 C1 failures were a float in the check
  (`hole_perturb_v1`), fixed in `v2`.
- **`g` in the block's readings** (E239; 5,030 relays, G1–G3 0 failures) `[derived from A.9 and Corollary 6.24]`: `g = t₀`
  if the block is clear there, else the least clear flank opening `(8K+1)/(8h)` over the block's readings: v21 §6.10's
  sort and scan from the entry instant. The index `j` of the winning opening is 0 in most paths and reaches 26 at `f = 6`
  wide (records). **The `f = 3` regularity "the landing is a first exit" is not forced** for three readings (3,830 of 9,880
  triples ≤ 40 have a start at which no first exit is clear; the least spread of a failing triple falls with height).
- **The isolation record** (E241, E243; `hole_isolations_*.jsonl.gz`, regenerable, the subset committed) `[VERIFIED — these
  populations; I1–I3 0 failures]`: stretches holding no isolation: 28,615 of 1,090,481 at `f = 3`, 4,280 of 574,420 at
  `f = 4`, 2,490 of 574,192 at `f = 5`, 0 of 500,000 at `f = 6`; at `f = 6` every arc of `c` holds an isolation
  (1,000,000 of 1,000,000 over both populations). "A stretch holding none is followed by one that holds" fails (runs of 2
  and 3).
- **The `f = 6` case, taken apart** (E244–E246, E248; `six_gap_v1`–`v3`, `hole6_mech_v1`): the longest blocked stretch of a
  six-block grows with height (about `a/10` laps of `a₁`, consecutive blocks), but `c`'s first arc is `[s, 7s]` (E245's correction of E244's placement condition, which was necessary but not the condition) and no
  reduced six-set ≤ 32 has `Q > 7` (greatest `Q` 3.05; constructed families to `a = 300`, greatest 3.33)
  `[VERIFIED — exhaustive ≤ 32; constructed to 300]`. Its derived piece, "closed when `g ≥ 4c/3`", is contained in
  E60 (`lonely_of_off_lattice`, E252). What remains is W6(7): six whole-number readings have a joint clear instant in every
  `[s, 7s]` with `9/(8x₁) ≤ s < 1/(6g)`; scale-free, window-shaped and flagged as a cap (E246, E251; the owner's ruling on `c`'s first arc as the place is pending, §8). `sync_block` (tight blocks) and nested windows (separated blocks)
  reach none of the 1,629 `f = 6` configurations E248 left (K0 settles 191 and 180; K1/K2 0; nested windows were excluded by construction, E242, so for them this is not a finding). The cascade's own
  statement is a flank question: some block flank has an opening in `c`'s first arc at which its five walkers are clear.
- **E250's nested actual stretches** (`4x_{k+1}λ_k ≥ 2.18` at every level) are kept as data, a covering measurement, and
  **not a mechanism**; the drift lemma built on them was excised (E251).
- **Every hole configuration mapped is already closed by `lonely_eight_or_residual`** (E255; `hole_residual_v1.out`; 0
  failures; `f = 3, 4, 5, 6`, `f = 6` wide): none is in `EightResidual`, so E60 was never reached. Which rule fires first is
  bookkeeping for the sample (`c = 1000` makes R6 at 5 and 8 impossible). **The open content of the holes is hole ∩
  `EightResidual`.** The re-aim at `EightResidual` was done on 2026-09-27 (E117–E118; E256): the three routes meet at
  the C1-shape.

- **D3, the pinned pair** (E228–E229; `d3_pinned_pair_v1`) `[VERIFIED — these populations]`: a captured reading with both edges occupied
  (`GridNudgeN` and the pair law do not apply): 86,301 sets of readings ≤ 24 and 3,000 seeded sets ≤ 64; 0 failures on F-2 (the first
  move from `1/8` is the slowest captured reading's exit), F-3 (every landing is `λ/8`, `λ = (8K+1)/h`) and C1. Whose exit holds the
  isolation (sets ≤ 24): the entering-edge reading 33,069, interior 40,019, captured 9,583, leaving edge 3,630 (records, not a rule).
  `[derived]` At each landing the condition is Theorem 6.14 at the flank `h`: D3 yields no new kind of rule; it is the record's "fourth
  rule" (`PROOF_REQUIREMENTS_v2` §7), the `L₀` ladder (§9 C23).
- **Sampling scope of the `f ≥ 4` holes** (E235): block consecutive ratios in `(1, 2)`, `x₁/m` in `[9, 60]`, `c = 1000`; only nested
  windows fired among the exclusions (1,384, 87, 3 draws removed); so this is the hole for blocks of consecutive ratio below 2. At
  `f = 6` the core is the one reading `m`, `S₀ = [1/(8m), 7/(8m)]` and its length `(3/4)(x₁/m) ≥ 27/4` laps of `x₁` by derivation
  (least 6.85 in the output).
- **Record's open items at the holes** (E231, E248): "bounded shapes by window constants" (E30; `WindowConstantFive`, its order-five form,
  registered OWED); `SyncBlockN` reduces a synchronised block to an `N`-free question, open (true on 288,288 cases); the f=3 strip's remainder.
- **E255's target** `[reasoned]`: the order-8 counterpart of unit filtering, a residue-band certificate at a modulus read off the set's
  multiples-of-8 structure; what shadows a flank across a run (a near-sharer, `A ≡ 0` or `±1 mod 8`) is the near form of a reading `≡ 0
  (mod 8)` relative to the flank (Theorem 6.27: an exact block is colliding).
- **Level A–C, what is not said** (A.12, B.11, C.6, C.7): C.6, the landing's region is its box less earlier boxes, its boundary made of
  faces; C.7 and A.12/B.11 list what each level does not say. E225: the "laps" are the first isolation beyond the slowest reading's first
  lap, bridges up to faster readings' later laps, and fast readings lapping within one move (A.5 re-entries); none skips a lonely instant.

**K. (v4) The flank at the C1-shape** (E252–E268). Native objects: flank, walker, band run, line reading (§1).
Derived, in order of reliance:
- **R1–R5 of E252** `[derived from Theorems 6.8, 6.9, 6.12–6.14, 6.18; v21 §6.9–§6.11]`: the case at flank `e` is some
  opening in `c`'s band run with every cluster walker clear; `c` is a slow walker (`ĝ_c = c/e ≤ 1/9`) and never blocks
  inside its run (it is in the way for at most `e/(4c)` consecutive openings; the run has at least `(3/4)(e/c) − 1`
  openings); so a flank fails across the run only if its cluster walkers shadow every opening. The record's exact shadowing
  structures are the sharer (Theorem 6.8, `A ≡ 0 mod 8` and its edge forms) and the half-integer pair (§6.11); every shadowing configuration found exhaustively has `max ĝ ≥ 1/3` (§6.11; register item 30), and the shadowing triples with small denominators are `(2,4,4)`, `(3,3,3)`, `(3,6,6)`, `(5,5,5)`.
- **Persistent classes** (E266) `[derived from the line reading]`: a single walker shadowing a flank across the whole
  run needs `|ε|(u_hi − u_lo) < 2`, hence `|ε|u_lo < 1/3` and `A mod 8 ∈ {0, 1, 7}` with the block-keeping sign. At the
  slowest flank all walkers have ratio `≥ 1`, so a single-walker shadow is a **near-harmonic with `x_j/e₁ > 7`**; at
  every other flank the commonest is the twin below `(1, −)`. Checked: 5,978 members and 12,000 random clusters, 0
  violations; single-walker shadows by rank 1…6: 10, 95, 133, 129, 119, 123 (members); 22, 418, 428, 410, 409, 384 (random);
  hand-offs level across ranks (members 11, 12, 10, 7, 8, 6; random 20, 40, 33, 41, 31, 26).
- **A single walker shadowing the fastest flank is a near twin within `(9/19)c`** (E260) `[derived from
  TwoWalker.bad_run_le, in experiments/n8/TwoWalker_v1.lean, a development file outside the gated tree (v21 l.1879); the step from it to the near twin is not in Lean]`
  (corrected from `9c/23` the same day).
- **(b), (c)** (E260): (b) = the fastest cluster flank is not shadowed across `c`'s band run by a hand-off; (c) = the near twin's own flank is free or continues the chain to a free flank. **(c) reduces to (b)** (E261) `[derived]`: if the fastest flank is shadowed throughout by a near twin, the set is
  lonely at an `x_{m−1}` opening inside `c`'s arc exactly when the set without `x_m` is lonely there. The recursion is automatic only for chains of up to three twins (total gap `< 6c/7`); deeper chains need the cumulative check; the data's chains have depth at most 2.
- **Tight cluster ⇒ the slowest flank is free** (E268) `[derived]`: if `x₆ − x₁ ≤ 3c` (with `x₁ ≥ 9c`) the slowest flank
  is free at the first opening of `c`'s run (`ρ = 1 + (r − 1)u*`, `(r − 1)u* ≤ 3 + 24c/e₁ < 6`). A chain of twin-below
  shadows through flanks 2–6 has spread `< 5c/3`, so it cannot cover rank 1. Checked on 0, 1, 24, 527, 32,749 constructed
  sets with flanks 2–6 all shadowed (chain lengths 1…5): rank 1 free in all.
Measured:
- **Shadowing across `c`'s band run** (E253; `hole6_shadow_v1`, `v2`; the E235/E243 generic class): never more than 2 of the
  6 flanks; 62 of 83 shadowed flanks are **near-sharers** (one walker, `|x_j − A·e| < 0.3c`: `A ≡ 1, ε < 0` 50, `A ≡ 7,
  ε > 0` 6, `A ≡ 0` 6), 21 are hand-offs; the record's small-denominator structure does not appear
  (`q > 1000` in 21,618 of 21,865 (E235) and 25,495 of 25,706 (E243) blocked openings; `q ≤ 16` in 6 in all). The derived condition agrees with exact coverage for every walker, 0
  disagreements. **Conditional derivation** (E253): if only near-sharers could shadow, not all six flanks could be
  shadowed (the fastest flank's near-sharer is a twin below; the chain stays within `2c`); the 21 hand-offs falsify the
  hypothesis, so this is not a proof.
- **The 21 hand-offs** (E258): `s = 2` in 5 (a persistent near-sharer, then another; the owner's *"two runners in the same slot … the runners need to separate from each other"*, E256–E257, twice), the
  others mix alternation (119 segments of 1–2 openings); every segment is within its occupant's persistence `1/(4|ε|) + 1`
  (137 of 137, nearly forced); alternating occupants against the exact uniform null: only the `q = 2` class exceeds it (36
  against 8.5; part of the `q = 2` excess is selection: a walker that blocks every other opening steps by about half a lap; the reading before the null, "near small-denominator ratios" in general, is withdrawn, E258); perturbation (504 moves): all 8 freeing moves move the flank reading itself. **Reading `[derived from the
  counts, with the null]`:** shadowing across a run is a near form of the sharer (persistent, `≈ 1/(4|ε|)` openings) or of the
  half-integer pair (alternating).
- **E118's construction under 10 more seeds** (E264): 5,431 members, fastest flank hand-off in 6 (verified by direct
  `circDist`); with E118's own 547, 5,978 members: every member has a free cluster flank, the slowest (rank 1) free in
  5,957 and rank 2 free in the other 21; the cascade lands at rank 1: 864, 2: 920, 3: 942, 4: 1,050, 5: 1,085, 6: 1,117,
  never at `c`.
- **E262** (`fastest_flank_check_v1`; residue test vs direct `circDist`, 0 disagreements): of 588,559 six-sets ≤ 30 with gcd 1, 58 have
  their largest flank shadowed at every opening at threshold `1/8`; each gives a C1-shaped set `(1, K·six)` whose fastest flank is
  hand-off-shadowed (`s` = 31 to 139); the cascade lands at `c`'s own flank in 32 and at a slower cluster flank in 26; **all 58 are closed
  by §17C** (first rule: R6 `q = 8` 30, free flank 19, R6 `q = 6` 5, rational opening 4; corrected from a partial view, 32/14/5/5/2), none
  in `EightResidual`. Those counts are the order of `classify`'s rules, not a mechanism (E264).
- **The restricted (b) is refuted** (E264) `[VERIFIED — constructed]`: the 58 shapes of E262 built toward membership with
  the fastest flank held a hand-off: 271 of 348 runs reach all 16 predicates (57 of 58 shapes); control 264 of 348. The
  fields do not exclude it, and no single field accounts for the 58: all fail `rational N|8`, `6,7,9`, `small resolution`,
  `one free`; `5,6,7,8` (the slot-sharer) 35, `free flank` 22, `first lap/-7` 32, `thirds/fifths` 51.
- **Ranks 1 and 2 both shadowed on `EightResidual`** (E268) `[VERIFIED — constructed]`: 287 of 480 runs (49 of 80 starts)
  reach all 16 predicates with ranks 1 and 2 held shadowed; the cascade lands at rank 3: 83, 4: 99, 5: 65, 6: 40; control
  289 of 480. So the fields do not force rank 2's witness; a random counterexample outside `EightResidual` also exists
  (seed 24: rank 1 a hand-off, rank 2 shadowed by `e₁` as a twin below, landing at `c`'s own flank).
- **What a joint cover needs** (E268): rank 1 needs a near-harmonic of ratio `> 7` or a hand-off, so the spread exceeds
  `3c`; a flank `i ≥ 2` needs a twin below with gap `< c/3`, a near-harmonic, or a hand-off; one walker is a near-harmonic of
  two flanks only as a near common multiple of both. Shadowed flanks per set: members 0: 5,372, 1: 551, 2: 53, 3: 2; random
  0: 10,042, 1: 1,670, 2: 272, 3: 16; no set with all six in any population read in E268 (members, random clusters, the twin-chain builds). No search aimed at six was run.
- **The 21 rank-1 exceptions** (E266): 10 single-walker near-harmonics of `e₁` (`A₁` = 7, 8, 8, 8, 9, 15, 16, 17, 24, 8), none
  in a persistent class at `e₂`; in 9 the walkers whose shift frees rank 1 are exactly `{e₁, the shadower}`; 11 hand-offs
  (critical sets of 2–6 walkers). **What forces rank 2's witness: not explained.**
- **Hand-off occupants** (E268): by openings covered `|ε| < 0.05` carries about 90%; by segments (members) 0–0.05: 68,
  0.05–0.15: 21, 0.15–0.35: 56, 0.35–0.45: 11, 0.45–0.50: 30.
Not derived (open): why a run of 6 to 100+ openings is not covered, at every cluster flank at once, by hand-offs and
persistent shadows together (§4 Q9).

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

**R15 (v4). The hole configurations** (E233–E243). (i) A hole configuration lands in the first core stretch in 1,972 of
2,000 at `f = 3` (866 at `τ_C`), in `S₁` in 28; 998 / 2 at `f = 4`, 1,000 / 0 at `f = 5, 6`; (ii) the core relays to `τ_C`,
then the block relays inside the stretch, and the landing leaves a stretch only where `g = b₀` (E237) or where `g` or `τ_C`
jumps (7 changes, all classified); (iii) the same mechanism in every exception (M3 in §2 J). **Answered on these
populations**, and then **moot as open content**: every one is closed by `lonely_eight_or_residual` (E255, §2 J).

**R16 (v4). Shadowing across the slow runner's band run** (E253, E257–E258; §2 K). (i) One near-sharer (62 of 83) or a
hand-off of near-sharers and alternations (21); (ii) the near twin / near harmonic persists for `≈ 1/(4|ε|)` openings,
the alternation near half-integers lasts as the deviation allows; (iii) near forms of the two exact shadowing structures
on record. **Answered in kind, on the E235/E243 hole configurations (all closed by §17C, E255; not on `EightResidual` members).** *Not understood:* why a run's hand-off coverage never extends to all flanks at once.

**R17 (v4). The C1-shape's flanks** (E259–E268; §2 K). (i) Every member (5,978 + 287) has a cluster flank with a free
opening in `c`'s run; the slowest flank is free in all but 21 of 5,978, and shadowed there only by a near-harmonic of ratio
`> 7` or by a hand-off; (ii) the persistent classes are derived; a twin chain through flanks 2–6 forces rank 1 free; (iii)
**not understood**: ranks 1 and 2 can both be shadowed on `EightResidual` (287 members), so the fields do not exclude a
cover of two flanks; why hand-offs and persistent shadows never cover more than three (members) is open. **Partly understood.** *E260's generalisation from "547 of 547" (the count stands as a count on that sample) and E262's
restricted (b) are retracted (§6 F17).*

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
- **(v4) Q8 status.** Levels A–C are complete as derived and checked, and are mostly a restatement of v21 §6 (E226,
  §2 I). Level D was re-aimed (E224, approved E225) at the entering-face relay, restated by E230 as `∃ (e, k)` on cases,
  read inside the holes (§2 J: two lower-order cascades composed; `g`; the isolation record), and then re-aimed again
  (E255–E256) to `EightResidual`, where it is the C1-shape (Q9). The design `CASCADE_DESIGN_v4` (E227) is superseded by
  E230's restatement of D1; a v5 carrying it is owed to the owner's call. Lean is on hold (E222).
- **Q9 (v4). The C1-shape: some cluster flank has a free opening in `c`'s band run** (E118, E148, E256, E268). For `c`
  the least reading and six cluster readings at least `9c` with the other fields of `EightResidual`, some cluster flank
  has an opening `u = 8k + 1 ∈ [e/c, 7e/c]` at which every cluster walker is clear (the cascade then lands at the
  earliest such opening over the flanks, at any rank 1–6; `c` is never the landing flank in the members). Three of the
  record's routes meet here: the `f = 6` hole's W6(7) (E246), `EightResidual`'s constructed members (E118), and Cases B
  and C taking this as their mechanism (E148). Measured: 0 failures on 5,978 + 287 members and on 12,000 random
  clusters. **Derived pieces (§2 K):** the persistent classes; a single-walker shadow of the slowest flank is a
  near-harmonic of ratio `> 7`; a twin chain through flanks 2–6 forces rank 1 free. **Open:** why hand-offs, near-sharers
  and near-harmonics together cannot shadow all six flanks (the fields of `EightResidual` do not force rank 2's witness:
  287 members, E268); the 21 rank-1 exceptions' rank-2 witness (not explained, E266). Also open (E266): whether the statement needs `EightResidual`'s fields. Random clusters (not in `EightResidual`) have the landing at `c`'s own flank in 2,493 of 12,000 and no member does; every datum here is at cluster `≥ 25c` while the statement is stated at `≥ 9c`. What would close it is a
  derivation that names, for a set of the C1-shape in `EightResidual`, a flank and opening with its walkers clear
  (a place), not that one exists (F1), and the owner's form (E230) accepts existence by any admissible argument on a
  condition.
- **(v4) Withdrawn or superseded questions.** E264's "rank 1 free, or rank 2 free" (E266, E268: false in general and on
  `EightResidual`); E260's "the fastest flank is free or its twin chain ends free" (E262, E264); E246's `c`'s first arc as
  the case's place (moot for the sampled holes, E255; the owner's ruling stays pending); E250's drift lemma (excised, E251).

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
- **(v4)** "The block's relay from the bound lands in `c`'s first arc" for the `f = 6` hole (E243) and "some cluster flank
  has a free opening in `c`'s band run" for the C1-shape (E256: the same statement with a cluster of six): the case's own
  statement, not a restatement of the whole conjecture.
- **(v4)** "The cascade's landing is the first isolation" (A.9): a proved by-product, not an equivalent (E225).
- **(v4)** The `∃ (e, k)` on every case of a list jointly exhaustive over the captured configurations (E230): the
  obligation in the owner's form.

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
| **F17 (v4)** a constructed sample's regularity stated as a law of the family | a count on members built by one construction, 547 of 547, becomes a derived-looking statement and the next step's target | E260 (fastest flank free or twin chain free, 547 of 547), E262's restricted (b), E263's design; refuted by 6 in 5,431 and by the constrained construction (271 of 348) in E264; E264's "rank 1 or rank 2 free", refuted by 287 constructed members (E268) and a random counterexample (E266) |
| **F18 (v4)** the owner's form of the obligation replaced by a stricter one | an added requirement (a rule, a named instant, a uniform theorem, a bound) taken for what a proof must be | E229's "the obligation is a fourth rule `(D, a)`" and design v4's D1, E229's `PROOF_REQUIREMENTS_v2` §4 read as the statement (superseded by `MANUSCRIPT_v20` §0); E230's five withdrawals (1 "cover every captured configuration uniformly"; 2 "and name its instant", design v4's D1; 3 an existence argument with no bound as falling short; 4 the `D ≤ 64` small-resolution case as falling short; 5 "no intermediate theorem sits between D and the conjecture"); `memory feedback_n8_obligation_is_loneliness_2026_09_24` unread |

**(v4) New instances of existing classes.**
- **F1** (imported shape): E224's D3 second half ("which band shapes reach copy 1") and D2/D4/D5 (the interval check caught
  them: item 15 and item 8; "the chain ends" is the obligation); E249–E250's nested actual stretches and the drift lemma
  (blocked-time proxies, the `Q(F)` family; excised in E251; E59, E61 had tried and classified the route, F7); E246's `Q`
  and "margin of about 2" (a refutation statistic, withdrawn as evidence of a mechanism, E251).
- **F2** (a rate): the role counts of E229 (records, not a rule); E243's 1,000,000 of 1,000,000 arcs (a record, scoped).
- **F3** (a majority rule): the f = 3 "the landing is a first exit" (1,149 of 1,149; not forced, E239); "a stretch holding none
  is followed by one that holds" (E241, refuted by runs of 2 and 3); E233's "no block reading set a move in a gap" (0 of 41,
  not forced).
- **F4** (a restatement): E229's D3 as "the fourth rule"; E245's Part A object measuring a necessary condition only.
- **F5** (a forced fact): Level A–C items (stated as forced, E221–E223); E253's "`c` never in the way" (R4); E235's
  "R8, the fast pair, the block split and the train collapse never fired" (they cannot with consecutive ratios below 2).
- **F7** (the record not read): **E225** (asked the owner a question the record answered, first isolation); **E226**
  (Levels A–C mostly restate v21 §6; the manuscript of record not opened); **E227** (design v4's first draft re-proposed
  proved Lean work); **E229** (`PROOF_REQUIREMENTS_v2` §7 read after the run); **E230** (the memory of the obligation's form
  unread); **E252** (E246's derived piece is E60, in Lean, not read first); **E256** (the re-aim approved in E255 had been
  done on 2026-09-27, E117–E118); E259's design repeating E253's flank reading on closed populations (E255 showed they were
  already closed).
- **F9** (a frame error): E251's flag, `SplitChainN` (nested windows, the classical nested-intervals method): proved, kept,
  its nativeness the owner's call.
- **F16** (a proxy count standing for the object): **E264's "the landing is at rank 1 or 2"**, a count of which flanks are
  free used as a statement about the landing (measured at ranks 1–6, E266); E263's reading of the 58 first-rule counts as a
  mechanism (the order of `classify`'s rules, E264).

---

## 7. Coordinates of the next step

**(v3, superseded by the v4 status below)** The next step is **Q8, the complete account of the cascade** (owner, 2026-10-01), designed before any work in
`docs/n8/CASCADE_DESIGN_v3.md` and approved by the owner before it starts. It builds on `CASCADE_DESIGN_v2` (§1–§7: the
owner's design, the move, transport, the grid instant, separation, the recursion, the one question) and on §2 F–H here.
Discipline (M8): derive first; a run checks a derived statement and has no other pass condition; an exception repairs the
derivation. v2's §7 (Q1 as a rung map run) is superseded.

**(v4) Status.** The active line is **Q9, the C1-shape** (§4), reached after Levels A–C (E221–E223), Level D inside the holes
(E227–E243), `EightResidual` (E255–E256) and the flank reading (E259–E268). No design for the next step is approved; the
pieces proposed in E268 are: (i) read the hand-offs per flank as sweeps and half-integer structures to see what a joint cover
of the six flanks needs beyond §2 K's derived classes; (ii) the 21 rank-1 exceptions' rank-2 witness. The owner's
"is the cover needed for the cascade mechanics?" question (2026-10-02) is answered below in §8, as owed.

---

## 8. Owed

- **(v3)** `compile-diff` of v3 against v2 and log E189–E219 (it discharges v2's own owed run against v1 and E189–E191). **(v4)** Run in E220: `MECHANISM_MAP_v3_COMPILE_DIFF_v1.md`.
- The three answers for R3's budget failures and for R8.
- §9's Lean items (C2) and manuscript corrections (C1, C4), each to the owner. **(v3)** The owner has put the manuscript
  behind the Lean tree (E192); the corrections wait.
- **(v3)** The owner's decision on the cap in `WideStep8` (E215, E217): the route holds for every `M`; the native content
  of the owed statement is the lap structure.
- **(v3)** `CASCADE_DESIGN_v3` (Q8), for the owner's approval. **(v4)** Approved E221 (*"yes approved, start with the Level A catalogue"*); `_v4` (E227) approved E228 and superseded in part by E230.
- **(v3, repair)** v21 §17G's pending author's ruling on first-lap clearance (§15I; provisional since 2026-09-25):
  `WideStep8 1` neither uses nor settles it (note after E212).
- **(v3, repair)** `CASCADE_DESIGN_v2` §6's four design questions: questions 1–2 (the carrying-in read on the grid; why it
  stops inside the block) are `CASCADE_DESIGN_v3` §8's gap D2; question 3 (the nest) is gap D4; question 4 (the
  recursion's exceptions, E150's 772) is gap D5. None is answered.
- **(v3)** Other sessions' uncommitted and untracked Lean (`gridStep8_two_bounded` in `RegimeSkeletonN.lean`; `CascadeGridN`,
  `PinchReflectionN`, `PartialReflectionN` and others in `Spec/`): not this map's to commit; recorded so no step rests on
  them unseen.
- **(v4)** `compile-diff` of v4 against v3 and log E220–E268 (it discharges v3's own owed run's edge; `MECHANISM_MAP_v3_COMPILE_DIFF_v1.md`
  covers E189–E219).
- **(v4)** `CASCADE_DESIGN_v5`, carrying E230's restatement of D1 and E255–E256's re-aim; the owner's decision on
  `CASCADE_DESIGN_v4`'s status.
- **(v4)** The owner's rulings still pending: whether `EightResidual` is "the obligation or a sufficient route" is **answered**
  (`lonelyRunnerAt8_iff_residual`, §9 C1; E256's correction of E255); first-lap clearance (§17G, provisional since 2026-09-25);
  `c`'s first arc as a place (E246; moot for the sampled holes, E255); whether `SplitChainN`'s nested windows are native
  (E251's flag); Lean's end condition (E222: "until the map is complete").
- **(v4)** The crosswalk's next version owes the Lean modules (E227): for example the untracked `CascadeTransportN`,
  `CascadeGridN` and others against Levels A and B.
- **(v4)** `TwoWalker_v1.lean` (`experiments/n8/`; `bad_run_le`) is a development file outside the gated tree (v21 l.1879);
  E260's derivation of the near twin rests on it.
- **(v4)** E231's derivation of the `f = 3` strip's remainder; E233's "the block's relay from an arbitrary entry instant, in
  its own readings" (answered by `g`, E239); E239's "`j > 0` at every `f`" (a proof of any hole has to deal with it);
  E258's alternating structure at the fastest flank (superseded by E264).
- **(v4)** Not run: a search aimed at all six flanks shadowed (E268); a derivation of why the hand-offs at different flanks
  do not combine (§4 Q9).
- **(v4)** Owed in the record, carried (E231, E248): bounded shapes by window constants (`WindowConstantFive`); `SyncBlockN`'s `N`-free
  question; the `L₀` ladder's justification by place (§9 C23).
- **(v4) Whether cover exclusion is needed (the owner's question, 2026-10-02):** see the reply recorded at E269 (the log
  entry cutting this map).

---

## 9. Consequences of proved results that were never drawn (M7 register)

Each entry: what is proved, where; the consequence for the whole proof; status of the consequence.

- **C1. The residual is the conjecture.** `lonelyRunnerAt8_iff_residual` (both directions, `f32daf4`, 2026-09-25;
  E104). v21 §17B still asks the author whether `EightResidual` is the obligation or a sufficient route (review Finding
  1); E190 repeated that the converse is not an `↔`. **Consequence:** nothing about the arrangement is lost by working
  on the residual; the arrangement's gaps, neighbours and other subjects are coordinates computable from the seven
  numbers. The standing question is answered by a theorem. `[PROVED]`; manuscript correction owed. **(v4)** E256 restated: the
  question is answered, and E255's wording "whether `EightResidual` is the obligation or a sufficient route (§17B)" as
  still pending was wrong. The open content inside the residual is the C1-shape (§4 Q9).
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
  unexplained exceptions (§2 G; **(v4) resolved in E223**, §2 I), and displaced
  only when a reading enters its slot at the isolation instant `[derived + VERIFIED — E219's populations]`. That the
  relocation then follows the cascade's move rule from that reading's exit is `[reasoned]` (E219). This is the owner's
  *"each isolation is pushed there by the speed"*, stated for single-reading changes (v3, repair).
- **C15 (v3). The persistence boxes make up E124's cells** (E219; each cell a union of boxes, precision note after E217
  (v3, repair)). **Consequence:** asking why the boxes exhaust the
  arrangement space, or why every entering-face relay ends in a box, is E125's question and the obligation (§5). Runs of
  the discover-and-test kind on these objects will keep re-arriving there; the owner's Q8 (derive what the cascade does
  in every configuration) is the response (§4, §7). `[reasoned]`.
- **C16 (v4). Levels A–C are the cascade's local and semi-local account, mostly restating v21 §6** (E221–E226). **Consequence:**
  every question about a chain is a question about the sequence of the A.4 rotations; the dependence on the speeds is a
  hyperplane arrangement of edge walls; most walls change only the route; the landing changes only on its own box's faces
  and on earlier boxes' faces. The account's own additions are B.4, B.8, C.3, the finite-travel resolution of E219's
  exceptions and the pass-through landing counts; nothing else is cited as new (E226). The gaps D2–D5 of the design contain the
  obligation (E223). `[derived; checked]`.
- **C17 (v4). The cascade's landing is the first isolation** (E225). `first_isolation_of_fixed` and its three
  lemmas (`Cascade/Iteration.lean`), v21 Theorem 6.2; E223's flag is withdrawn. **Consequence:** describing the oracle by
  first-ness (C.4, C.5) is sound because proved; nothing in an argument rests on it (E200). `[PROVED; VERIFIED 6,436 of 6,436]`.
- **C18 (v4). The obligation's form** (E230; `MANUSCRIPT_v20` §0). **Consequence:** any admissible argument for `∃ (e, k)` on
  a condition counts, and each proved condition is progress; "a rule that produces `(D, a)`", "a uniform theorem" and a
  named instant are not required. Propositions 6.10–6.11 were withdrawn for their covering statement form, not for being
  existence arguments. Withdrawals 4 and 5 of E230: the `D ≤ 64` small-resolution case is a proved case (`ResolutionClears8`, v21 §17C), and only the verified-not-proved remainder of the `L₀` ladder is not proof (C23); "no intermediate theorem sits between D and the conjecture" is misleading, since every proved case and every reduction shrinks what remains. `[owner's text; derived from the manuscript]`.
- **C19 (v4). The lower orders' template already closes every hole configuration mapped (E233–E243's samples)** (E254–E255; `OrderEightCasesN`, v21
  §17C). **Consequence:** the hole route and the residual route are two case lists for one target; the residual route is
  ahead; the open content is hole ∩ `EightResidual`. `[VERIFIED — these populations; each rule proved in Lean]`.
- **C20 (v4). Three routes meet at the C1-shape** (E256): the `f = 6` hole's W6(7) (E246), `EightResidual`'s constructed
  members (E118) and Cases B and C (E148). **Consequence:** the next map work sits at §4 Q9, not at the holes. `[reasoned
  from the record; E117–E118, E148]`.
- **C21 (v4). `lonely_of_off_lattice` (E60) closes the off-lattice cases** (E252–E253). A configuration with a reading not
  divisible by the gcd of the others is closed (proved in Lean, axiom-clean); E246's derived piece `g ≥ 4c/3` is contained
  in it. **Consequence:** the generic class is every six coprime readings. `[PROVED; E60]`. E253's counts of E60's reach (90 and 105 configurations closed, almost all through `h = 2`; 719 and 715 left in the generic class) are partly a sampling artefact (`c = 1000` in every configuration; E253, E254).
- **C22 (v4). The cascade's loneliness at the C1-shape is two events, the persistent shadows and the hand-offs** (E253,
  E258, E264–E268). **Consequence:** the persistent classes are accounted for by derivation (§2 K); the joint cover is
  excluded for a chain of twins and open for mixed covers; the fields do not force rank 2's witness. `[derived + VERIFIED —
  constructed; open]`.

- **C23 (v4). The `L₀` ladder** (`PROOF_REQUIREMENTS_v2` §7; E229–E231, E255): the first live lattice, then the next, as a fourth rule
  producing `(D, a)` when some differences are divisible by `8g`. `[VERIFIED — 31,066 of 31,066 runners]`, **not proved**. The cascade's
  landing is almost never the ladder's resolution (E4), and the ladder is "a divisibility device, not a scale-invariant one" (E11); `D ≤ 64`
  is a proved case (v21 §17C `ResolutionClears8`, "a case boundary, not a claim"). Map v3 C4: the landing `(8K+1)/(8h)` is itself a clearing
  resolution with `D = h`. **Consequence:** an open rule whose relation to the cascade is by place (when `(h, K)` is `(D, a)`), not yet read.
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


## 10a. (v4) Run artifacts for E220–E268

Under `LonelyRunner/experiments/nN/redo/` unless stated. Level A–C: `cascade_level_a_check_v1`, `_b_`, `_c_` (E221–E223;
catalogues `docs/n8/CASCADE_ACCOUNT_LEVEL_A_v1.md`, `_B_v1.md`, `_C_v1.md`, `CASCADE_ACCOUNT_CROSSWALK_v1.md`,
`CASCADE_DESIGN_v3.md`, `_v4.md`). D3: `d3_pinned_pair_v1` (E228–E229). Holes: `hole3_cascade_v1`–`v3` (E233), `holef_cascade_v1`
(E235), `hole_perturb_v1`, `v2`, `hole_perturb_regions_v1`, `hole_perturb_e1_read_v1`, `hole_perturb_e1_refined_v1` (E237),
`hole_g_flank_v1`, `first_exit_three_v1`–`v3`, `first_exit_three_spread_v1`, `hole_g_three_control_v1` (E239),
`hole_isolations_v1`, `hole_isolations_runs_v1` (E241; the full `.jsonl.gz` regenerate), `hole6_wide_v1` (E243), `six_gap_v1`–`v3`
(E245–E246), `hole6_mech_v1` (E248), `hole6_flank_v1` (E250), `hole6_shadow_v1`, `v2` (E253), `hole_residual_v1` (E255),
`hole6_handoff_v1`, `v2` (E258). The C1-shape: `residual_members_C_list_v1` (`experiments/nN/`; E259–E260),
`hole_C1_flanks_v1`, `hole_C1_chain_v1` (E260), `fastest_flank_check_v1` (E262), `restricted_b_v1` (its Part 3 hung in the pool; superseded by `restricted_b_p3_v1`),
`ce6_verify_v1`, `ce6_read_v1`, `free_ranks_v1`, `rank1_exc_v1` (E264), `slow_flank_mech_v1` (its Part 3 perturbation filter and landing-rank definition superseded by `_v2`, E266), `_v2`, `one_both_v1`,
`members_5978_v1.json` (E266), `both_shadowed_v1` (+`both_shadowed_members_v1.json`), `handoff_joint_v1` (E268). Lean: none built
(E222); `experiments/n8/TwoWalker_v1.lean` (a development file, E260).


---

## 11. (v5) Log E269–E331: the cascade's landing and path; outcome classes; the window trees

**Status.** DRAFT, not promoted. `compile-diff` was run on the first draft of this section against log E269–E330 (report: `MECHANISM_MAP_v5_COMPILE_DIFF_v1.md`): it found 44 of 62 entries with nothing carried and 12 statements stronger than their source. This text is the revision: statements corrected (§11.1–11.6), the dropped withdrawals, rulings and open items added (§11.8). v4 remains the map until a second `compile-diff` pass on this revision clears. Grades: [LEAN] = theorem in `LonelyRunner/LRC/Spec/`, axioms checked `[propext, Classical.choice, Quot.sound]` (2026-10-03: `ZoneLink.slower_lap_le`, `faster_lap_lt`, `equal_not_inZone`); [TESTED n/N] = exact Fractions, n violations of N; [TREE] = exhaustive in the stated window, floating-point LP (threshold 1e-9, thin cells could be pruned) with exact checks, not certificates. Readings are written ρ_k (speed minus the subject's, units of d_min; every runner has positive speed; nothing is stationary); E308's presentation rule (speeds s, s+1, ...) governs prose for the owner.

### 11.1 The cascade's landing and path, in its own objects
- Start R = 1; reading y blocks R when R lies in an open zone ((8j-1)/ρ_y, (8j+1)/ρ_y); the move goes to the largest exit among blocking zones; the landing is the first unblocked R. (Definition.)
- **Landing = the least unblocked R ≥ 1** [TESTED 0/72,000: 52,000 (E325) + 20,000 survey; E327: 8,400/8,400 starts]. This is the right end of the union component containing 1; it is a statement about what the iteration reaches, and it is not offered as a covering argument (E269: covering as a question's object has been an imported shape). Owner E287: nothing in the conjecture or the framework needs the first isolation; first-ness here is a property of the iteration only.
- **Step 0:** a move happens iff some reading lies in a strip (8j-1, 8j+1), j ≥ 1; the first setter is the strip reading with the largest (8j+1)/ρ [TESTED 0/20,000, this session; log E331].
- **Setter** = the blocker with the largest exit; pairwise (8j_a+1)ρ_b > (8j_b+1)ρ_a [TESTED 0/152,170 steps, E326]; no exit tie among blockers occurred in those steps. Exit ties across zones occur (E325: 9 tie rows; zones with a common exit are nested; the setter is the one with the smallest entry, then the highest rank). "Lowest-rank blocker sets" holds when blockers share a lap and fails in 6–7% of steps, always as a faster blocker on a higher lap with the later exit [TESTED].
- **Next state depends on the previous setter's zone only** (R2 = its exit): a zone-pointer chain reproduces every (setter, lap) sequence and landing [TESTED 0/80,000, E326].
- **Link rule** (slower: lap ≤ the setter's; faster: lap ≥ the setter's + 1; equal readings cannot link) [LEAN `ZoneLinkN`]; the other clauses (setter never blocks its own exit; a reading's lap never decreases; the same reading never sets twice in a row) [TESTED 0/136,199, E326]. Within any J=1 word a recurring rank always recurs on a strictly higher lap [TREE 0/9,651, E323].
- **Hop** = birth or death of a lonely component [TESTED 1,716/1,716]; effective-crossing rule [TESTED 598/600 + 2 unobservable; locality 170/170]; inert readings [TESTED 61,752/61,752] (E311–E316). Hops do not land on frozen edges only (E311's statement withdrawn, E313). The one-runner catalogue is not a predictor for three movers: it predicts the landing in 229, the landing is lower in 625 and higher in 129 (E316).

### 11.2 Outcome classes (E325, E328, E330)
- Fourteen classes by (moves 0/1/≥2, opener lap 1/≥2, strip opener, closer equal to the opener's own reading, zero-width window) on 52,000 sampler arrangements; an independent labeller agrees in all [TESTED 0/52,000]; 12 classes are populated. The conditions of the four closer-equals-opener classes (K1s1, K1s2, K2s1, K2s2) are stated approximately and were checked only through the labeller's direct closer computation (E325, Not verified). K2a is empty by argument (an opener of a ≥2-move cascade never has its own zone containing R = 1; 0/4,491 independent). K2s1 (≥2 moves, opener lap 1, closer = the opener's reading): no hit in 271,802 cascades; the lap ≥ 2 strip-blocker case is unclosed by hand; (superseded in §11.9: proved empty).
- **Samplers and the tree reach different classes.** Sampler arrangements (E325): 72% have 0–1 moves. Tree-cell members (E328): 99.8% have ≥2 moves with opener lap ≥ 2. These two sets are NOT comparable as frequencies (a tree is a partition by path, not a weighting; E328). Reading 1 sets a move in tree members (opener (1,1), landing exactly 9; 3,205 of 24,000 exact perturbations of the extremal vertex, E326 check). Sampler maximum R 5.03 and longest path 12 describe the samplers' reach (E326); E315 and E317 record a 13-move rational arrangement and hill-climb paths of 28 moves, R* ≈ 11.95.
- **Outcome openers (rank, lap) among exact members:** 40 at ρ_7 ≤ 9 → 44 at ρ_7 ≤ 17 (adds (6,10), (7,2), (7,12), (7,18); loses none). Members exist for 9,197/9,652 and 110,081/117,084 cells; the opener sets are lower bounds. K2s2 (closer = the opener's reading, lap ≥ 2) is absent at ρ_7 ≤ 9 and appears at ρ_7 ≤ 17 (198 members); 11 zero-width, 58 lap-1 openers there (E330).

### 11.3 The window trees (E319–E324, E330)
- ρ_7 ≤ 9: 9,652 terminals; ρ_7 ≤ 17: 117,084; ρ_7 ≤ 25: 747,487 (earlier run; truncation defect below; corrected full set with stored cells in progress). Supremum of the landing 26433/2209 = 11.966048 in all three windows [TREE]. The supremum is a value at a closure vertex (E319 caveat ii): no arrangement is recorded as reaching it; the largest exact-member landing is 11.5925. The vertex is tangent to d_min's second clear-window edges R = 9 and R = 15 [derived from the vertex; the general statement is not proved, E321]. Partition/soundness check: 0 violations on 256 exact arrangements. Threshold sensitivity: identical at 1e-6, 1e-9, 1e-12 [CHECKED]; a cell thinner than 1e-12 would be missed by all three (certificates owed, E322). The window is ρ_7 ≤ 8J+1 only (E319 caveat iii).
- Lap compression fails: 4,922/31,585 pairs (largest excess 2.53); the window J cannot be reduced to J-1 by removing laps (E320 [CHECKED]).
- **Landings above 7 occur with ρ_7 > 9** (59 members at ρ_7 ≤ 17, ρ_7 up to 16.19, R* 9.34–9.58); landings above 10 only with ρ_7 ≤ 8.52 among members, ≤ 8.70 among nodes [TREE]. The earlier "no landing above 7 with ρ_7 > 9" was the searches' reach (corrected in `CASCADE_ACCOUNT_v1.md` §4).
- J=1 words (E323): 6,705 distinct, 17,399 prefixes, lengths 2..29; not Markov in the last letter (42 of 47 last-letters have several successor sets) [TREE].
- At the landing the readings are pressed against their exit edges: 12,897 positions in [1,1.25) against 1,066 in (6.75,7] (J=1 members); 154,772 against 7,186 (J=2). Cell members, not frequencies. The width of the window after R* is by definition min over readings of (7 - position)/ρ_y (E329 correction).

### 11.4 Equivalences and look-alikes (E327)
- A change to reading y keeps the state sequence when y and its image are both clear at every visited state (+8m: 21,781/21,781; moved within its inert component: 47,391/47,391). The closer is not preserved under in-component moves (27,183/47,391); the rank-labelled path is not preserved under +8m (ranks reorder); ρ → ρ + 8k/R* keeps S in 10,205/15,843 when y or its image blocks earlier. Every failure has y or its image blocking at a visited state. Smallest +8m counterexample [1,3,7,8,9,12,13] with ρ_3 = 7 → 15 (checked exactly). Uniform scaling with the natural start is exact; reflection preserves block status only at R with 2cR ∈ 8Z.
- Path classes are not boxes in reading space: 52 same-path pairs of J=1 cells have all six reading ranges disjoint (24 families); 79 identical 7-range boxes carry 2+ paths; 635,433 pairs inside opener (7,9) have disjoint ranges and different paths.

### 11.5 Failures by class (to §6)
- *Absence claimed from a sampler or search* (E326 rank-1 inert, longest path 12, sampler R ≤ 5; E330 no late landing with ρ_7 > 9): the check that settles it is the tree's exact members.
- *A proxy the argument does not use:* the LP witness point. A float max-slack point lies outside thin cells: 2,939 of 9,652 witnesses give a different exact path (this session; log E331); replaced by exact members (jitter + exact path match). Owner E293: the map goes on hold when it maps proxies.
- *Truncation in the tool:* `frontier()` in `path_tree_par3.py` dropped terminals at depth < levels: J=1 lost 1 terminal, J=2 14; sup unaffected; `path_tree_par5.py` keeps them.
- *Framing a mapping run as a proof obligation* (the E324 account; the owner asked on 2026-10-03 whether what was run and recorded aimed at understanding the cascade and at categories of arrangements by outcome; the supremum, certificate and finite-list counts are proof-obligation framing).
- *Absence claims from headers or partial reads, coalescence, hops-on-frozen-edges, the partial `EightResidual` tag* — see §11.8 withdrawals.

### 11.6 Consequences (to §9)
- The pointer-chain form says the path is an orbit of a map on zones (rank, lap); the outcome of an arrangement is where that orbit ends.
- The second lap adds four openers and 59 late landings with ρ_7 > 9, none above 10, among members; the opener set grows slowly while the cells grow 12-fold. Whether the opener set is finite across windows is open (it is a lower bound).

### 11.7 Owed (to §8)
J=3 full terminal set, members, profile; the taxonomy on J=2/J=3 members; K2s1 proof or construction; exact certificates for pruned LP branches; whether the opener set is finite across windows; Lean statements of the pointer chain, landing = least unblocked R, the step-0 law and the five crossing types (E312); `Cover8 M` (the one owed statement for `lonelyRunnerAt8_of_cover8`, E269–E270, v4 §2 F); `WindowBound` and its lattice-point finding (E296: the window is not uniform at lattice points, T ~ P/(4a)); statement (T) of E280; the tail-update rule (E312); R* ≤ 12 always (E318: not derived; the first surviving odd-class event is 12 or 14); Window Lemma W6 (tested, not proved).

### 11.8 Carried from E269–E310 (added after the compile-diff)
**Owner rulings that govern the mapping** (quotes in the log entries named): E270 the finite-cover direction (a finite set of arrangements; `1…7, 10¹⁰` is not a new arrangement from `1…7, 17`); E272 from the AP/grid view there are only so many arrangements, clumps too evenly spaced become AP + grid to capture the outlier; E273 the mechanism is the same for any arrangement (the cascade reduces them instantly); E275 the deformation from the AP is the route; E278 translate the shape of Tao's reduction without importing parts; E279 no evenness is needed, only that any arrangement can be locally arranged in an AP/grid style; E281 existence may not be necessary, ask whether walls and hand-off are imported; E282 existence is the grid's global isolation (φ(8)) and an arrangement is a deviation from it; E284 "bad reading" and mover/exit are proxies; E287 the first isolation is not required; E288 isolation is individual for each runner; E289 isolation binds only the two neighbours, the others need only be within the other 6/8; E291 ask "is it needed" of everything added; E293 the map goes on hold when it maps proxies, and no two speeds are ever the same; E295 "is it actually needed or are we importing it"; E300 Lean requires a correct statement and code, not what it looks like; E306 the AP has four global isolations; E308 owner looks at speeds, not gaps (present speeds s, s+1, …); E309 moving one runner leaves the frozen runners' isolation points unchanged; E312 no arrangement change whose cascade effect is unknown; E315 categorise arrangements by RESULT; E316 exhaustion acceptable with a log of look-alikes; E317 autonomous aims (a) a definitive finite list and (b) a complete understanding of the cascade: **neither is reached**; E318 the owner's suspicion R = 12 is the maximum (not derived).
**Withdrawals** (the text of each is in its entry): E269 reply about the finite list (Cover8 is that statement); E274 E273's K design (K grows with the scale ratio by definition) and the drift quantity is a coordinate, not a requirement; E278–E279 E278's dichotomy and evenness branch; E281 E279's "the conjecture itself" bullets; E284 E283's closing paragraph; E287 E286's comparison columns and "not the first, only a witness"; E288 the 14-formula test; E289 E288's requirement to bound the entering-face jumps; E293 "the conjecture itself" for the owner's route; E294 E290's "Not in Lean" section and E293's "No argument is on disk" (full read of the separation / transport / ideal-reading / pair-law modules); E295 E292's "the missing statement is the grid-selection rule"; E296 E295's coalescence claim; E299 E297's "rule not obtained" for this displacement; E301 D = 1 is the cascade's grid only when d_min = 1; E304 E303's "residual" tag (partial field set; the current `EightResidual` has no 7-subset of [1,40]); E311/E313 hops land on frozen edges only; E316 the catalogue as predictor; E329 its Consequence sentence; E330/E326 the samplers' reach statements.
**Open items from E269–E318** (each "Not done" stays open): E271 the finite-cover design (`FINITE_COVER_DESIGN_v1.md`) was never approved or started; E274 the finiteness scope does not by itself cover the residual (generators mostly outside `EightResidual`); E275 the relay condition is unproved, and the literature search (E276, Rosenfeld arXiv:2509.14111 and others) is not imported; E280 6 tied events per case unread and statement (T) [VERIFIED readings ≤ 24]; the first-order criterion holds exactly and every read event has a margin window, so **v4's "Open: multi-pinches and the bounded-time half" (v4 ~line 235) is bounded by E280 and not closed**; E283 the type at the bound does not fix where the isolation lands; E286 the complete grid's named instant stays lonely to q ≈ 61.7 against a proved radius q ≤ 0.5 (this fact stands; the comparison columns were withdrawn in E287); E296 the window fails to be uniform at lattice points and the path route reduces real speeds to integer speeds without saying anything about the integer case; E297 no rule gives the instant (which (e, K) or modulus) from R; E299 the displacement of an entering-edge runner as a general theorem; E300–E303 the next move and its composition to a certificate (b, k); for every `EightResidual` set the iteration from 1/(8·d_min) reaching a fixed point; why the chain ends at 5; E305 why no third reading's zone fills the first gap, for every residual member; E306 that the real members are near a grid in the sense of `pair_law`'s c/20; E307 the same tracking along a real member's path; E308 whether (ii) and (iii) are one family of gaps; E309–E310 deformation of more than two runners (why some component of the frozen set's lonely set stays unblocked is the existence statement again; 0 empty steps in 4,898 is a measurement); E311 the carried blocker at moves ≥ 2 as a zone of the chain; E312–E314 the tail-update rule, non-linear deformations, the catalogue for two deformed runners and for grids with extra laps; E315 the defining inequalities of a result class.
**Lean artifacts of E296–E307** (built clean, axioms `[propext, Classical.choice, Quot.sound]` per the entries): `SegmentWindowN`, `IntegerGridN`, `IntegerDisplacementN`, `ClassDeviationN`, `ZoneLinkN`; docs: `EXHAUSTION_PLAN_v1.md`, `EXCEPTIONS_LOG_v1.md` (X1–X8), `ARRANGEMENT_EQUIVALENCES_v1.md`, `FINITE_COVER_DESIGN_v1.md`, `ARRANGEMENT_CONDITIONS_v1.md`, `MOVEMENT_INGREDIENTS_v1.md`.

### 11.9 Updates after the draft (2026-10-03, E332–E333)
- **K2s1 is empty** [proved by hand, two proofs; E333]. L1: the closer is the opener's own reading only if the opener is the fastest reading, since a faster reading y has its next entry (7 − q_y)/ρ_y ≤ 6/ρ_y < 6/ρ_s after the landing (q_y ≥ 1 because y is clear) [TESTED 1,593/1,593, opener always rank 7]. With the opener rank 7 on lap 1 a previous setter cannot exist, so ≥2 moves is impossible. The 14-class table has 11 populated classes (K2a, K2s1 empty by proof).
- Local transition types (rank direction, lap change): 16 at J=1, 22 at J=2; the sign pattern is the link rule; the lap magnitude grows with the window, so it is not a finite local type (E332). Per-lap rank sequences are strictly decreasing in 372,642/372,642 (lap, word) pairs (the exit order).
- Window width after the landing = min over readings of (7 − position)/ρ_y; the closer minimises it (E333).
- **Staircase of lower bounds (E334).** The first k+1 setters distinct ⇒ ρ_{7-k} > 7(7/9)^k (7, 49/9, 343/81, 2401/729, …); derived from the step ratio ≤ 9/7 and the setter condition ρ > 7/R_k [proved by hand; tested 0 violations in 119,278 members and in 400,000 random arrangements per window at W = 9, 17, 40, 100]. A recurring setter breaks it: ρ_5 = 3.671 < 343/81 at W = 40 (setters (7,6,7)). Infima of the multi-move class: 7, 49/9, 343/81, 2401/729 (1715/459 for ≥10 moves), 735/289, 3381/2125 for ranks 7..2 (LP vertices; float optimality, no dual certificate). Upper bounds depend on the window (no formula).
- **The d_min gate (E340)** [proved by hand; TESTED 110,081/110,081 members]: a reading with ρ > 1 has zones of width < 2, so only reading 1's zone (7,9) spans states ≤ 7 to exits > 9; landing > 7 ⇔ reading 1 sets a move (always lap 1, from a state in (7,9)) ⇔ a state equals 9 ⇔ landing ≥ 9. No landing lies in (7,9). The cascade is a chain that either breaks inside [1,7] or crosses d_min's zone to 9 and continues; landings in [9, 11.97] are the second phase. Why the second phase stays below 12 is not derived.
- Outcome groups by the closer (E340): G1 gate crossed (4,939 members), G2 closer slower than the opener, G3 closer faster, G4 closer = opener (rank 7 only, proved L1).
- **Phase rotation and mirror centres (E342)** [exact identities; TESTED 0/12,000 per m]: p_y(R+8) = p_y(R) + 8 frac(ρ_y); if mρ_y ∈ Z for all readings the blocking status is symmetric about R = 4m (centres of d_min's clear windows for odd m: 4, 12, 20), so the first clear point is ≤ 4m. Integer readings: 66,000 arrangements, maximum landing 3.769, none above 7. Gate-crossing members have a reading ≥ 0.1804 from an integer (member list). 12 = mirror centre of d_min's second window; the bound 12 for generic arrangements is not derived (symmetry broken by the rotations).
- **The extremal cell (E344)** [exact, verified in Fractions]: six tight equalities form a chain "exit of one zone = entry of the next" along readings 3-5-7-6-4-2 anchored at the gate (9ρ_5 = 47); inside the cell R* ≤ 9·(8·11+1)(8·4+1)/(8·6−1)² = 26433/2209 from rows 33ρ_7 = 47ρ_5 and 9ρ_5 = 47 (same-reading lap ratio of reading 7, laps 6 → 11, and the exit/entry lap ratio of reading 5). Pivot walk over 1,485 fine cells: maximum 26433/2209, next 11.6965. Window at the supremum: right end 12 + 3/47; R* + width/2 = 12 + 33/2209; no exact mirror relation. R* < 12 is not derived: why the opener has an earlier blocking state R_a with R_a(8j_o+1)/(8j_a−1) ≤ 12 is open.
- **Correction (E347–E349, 2026-10-03).** The window trees' stored terminal cells were the leaves only; landing regions at internal nodes were not recorded (98% of sampled arrangements with ρ_7 ≤ 17 land at an internal node). Statements in §11.2–11.3 and §11.9 that were counted over tree cells or members before E348 (cell and terminal counts, the 40 → 44 openers, lap-free classes, pair sets, the 99.8% class share, gate-crossing counts, position/window statistics, the per-rank infima 735/289, 3381/2125, 1715/459 and the upper-side values of E334, the 8 members landing at 9) describe the deepest paths and are lower bounds for sets and upper bounds for infima; they are superseded for J=1 by E348 (19,679 regions: 9,652 leaves + 10,027 stop regions; 46 openers; 66 lap-free classes; 38 of 49 pairs among members; 7,567 gate-crossing members), and J=2/J=3 with stop regions are pending. Not affected: the gate lemma, the closer lemma, K2s1, the staircase derivation D1–D4, the symmetry identities, the extremal-cell analysis and the supremum (taken over every node). 43 of 49 (opener rank, closer rank) pairs occur (E347); the six diagonal pairs are impossible.
- **Stabilisation (E357, 2026-10-03).** On all outcome regions (members, lower bounds): J=1 and J=2 each give 66 lap-free classes (opener rank, closer rank, window A/B) and 38 of 49 (opener rank, closer rank) pairs; (rank, lap) openers grow 46 → 49. Exhaustive lattice families (integer 7-subsets with gcd 1, smallest element s = 1, 2, 3; 3.26M, 5.19M, 5.24M sets): 37 pairs in every family and no landing above 7, maximum landing 49/13, 33/7, 17/3 (below 4s); path words, landing values and lap-carrying classes keep growing (s = 1: 48 → 38,381 path words for a_7 ≤ 12 → 40). 43 of 49 pairs occur overall; the six diagonal pairs are impossible. Not a proof of finiteness; J=3 pending.
- **Corrections and additions (E359, 2026-10-04).** (i) The bound L ≥ 2/(7ρ_6) of the six-reading clear set K6 on [1,7] is false: exact tuple (1, 6559/2279, 26236/6779, 231/47, 26236/4115, 7) has L = 135/3748 < 2/49; so ρ_7 ≤ 7ρ_6 for gate crossers is not established through the first window (R8 untouched). (ii) The claimed pair-law avoidance in the window sets is an artefact of stored points with ρ_7 ≥ 7; the exact rule: a window holds {1,7} and {3,5} instants iff it contains [x, x+2], x ∈ {1,5,9,13,17,21}, which forces ρ_7 < 3 and R* = 1. (iii) Pins: at a vertex of a cell's rho_7 (or rho_6) maximum the tight binary rows form a spanning tree reaching reading 1, and a row at reading 1 has state height 1, 7 or 9, so pins have the form (8j±1)/h, h ∈ {1,7,9} [proved from P1; P1 checked on 7,003 cells]. (iv) Single-point windows: [R0,R0] is a window iff all positions are in [1,7], one is 1 and one is 7; classified (E359).
