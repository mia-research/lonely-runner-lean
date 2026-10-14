# Order eight — how the cascade works: a design document (v4)

2026-10-01. **Design phase.** v4 replaces v3's §8.5–§8.9 (Level D) with Level D re-aimed and built from the record
(owner, E225: *"1. Yes"* to E224's re-aim; E226 placed it on the record's flank and grid-class programme; owner: *"Yes"* to
reading v21 §6.7, §17 and handover v10 first; then *"Remember that lean now outpaces the manuscript, handover and paper
documents"*, so the Lean `Spec/` tree was surveyed as the primary record of what is proved, E227). It removes v3 §8.7's clause "Lean follows each derived item" (owner,
E222: *"Yes we are not looking at lean until the map is complete"*). §1–§7 and §8.0–§8.4 are v3's, unchanged (v3
retained). Levels A–C are done (`CASCADE_ACCOUNT_LEVEL_{A,B,C}_v1.md`, log E221–E223); their citations to the record are
`CASCADE_ACCOUNT_CROSSWALK_v1.md` (E226): mostly restatement of v21 §6 and E142–E183.

---

## 1. The owner's design, in the owner's words

- *"Cluster of speeds and some outliers is AP with some grid … The only hard problem in this is two runners in one slot,
  but that is resolved."* (E139)
- *"if you prove cluster with outliers works at one point you prove it for all"* (E141): the configuration repeats as
  rotations around the circle.
- *"the conjecture itself is a limitation to the arrangements that can happen; once you add scale invariance and infinity
  to it, plus mirror effect and circle effect that just displaces the arrangement, you are not left with a whole lot."*
  (E146)
- *"As the gaps get bigger, they just fall into larger grid positions; we shouldn't need thousands of certificates, we can
  already prove grids globally isolate and then it's just a deviation from grid"*; *"It will be because there are two
  runners in the same slot, which just means it delays the isolation event because the runners need to separate from
  each other"*; *"It's the same mechanism over and over."* (E156–E158)
- *"You have an oracle that tells you exactly the answer … We had a process where you test with the cascade and perturb
  if you need."* (E155)

**The design, stated once:** an arrangement is a grid plus a deviation. At the arrangement's own grid instant every
runner is clear except those the deviation has put in the subject's slot. The cascade separates them, one move per
separation; the isolation is where the separations leave the slot empty. There is one mechanism, repeated at every
scale (clusters nested at well-separated scales, E155) and at every lap (rotations, E141).

---

## 2. What the cascade does, step by step

**2.1 The move.** At an instant `t`, the readings in the subject's slot are the crowd. The cascade moves to the latest
exit among the crowd. `[PROVED — Cascade/Iteration.lean]` No lonely instant lies between (the latest leaver is in the
slot throughout), and the fixed point is the first lonely instant (`first_isolation_of_fixed`, line 213).
*Frame check:* this is the definition. The cascade looks only at the slot, and at time in order. It never looks at all
instants at once, which is what covering and measure do.

**2.2 Who is in the slot after a move.** `[derived]` A reading in the slot at the new instant `τ` entered it after `t`:
if it had been in the slot at `t` it was in the crowd, and its exit is at or before `τ`. So **the next crowd is made
only of arrivals during the separation.** This is the transport lemma's content: *the next obstruction is only readings
the shift carried over an entering edge* (`SeparationN.transport`, `[PROVED]`).
*Frame check:* the cascade's own object (who arrives while the crowd separates). Not a covering: a covering asks whether
every instant is blocked; this asks who arrives during one separation.

**2.3 The grid instant.** `[PROVED — GridPairLawN.grid_class_clear]` At a grid through the arrangement's own reading
(one class, any number of readings per edge, under small-deviation conditions), every runner is clear except those in
the subject's slot. So at a grid instant the only obstruction is the captured readings, and everyone else sits away from
the slot.
*Frame check:* the grid is the arrangement's own grid (through its own reading), read at an instant the cascade passes.
The trap here is to take a family of grid instants and test them apart from the cascade (E193–E195, F14).

**2.4 Separation from a grid instant.** `[PROVED — SeparationN.lonely_of_separation, move_eq_separation]` If, while the
captured readings separate, every other reading keeps its band, the subject is lonely at the separation's end, and that
separation is exactly the cascade's next move. When a reading does not keep its band, it is carried over the entering
edge (2.2), and it is the next crowd.
*Frame check:* this is the owner's "two runners in one slot … delays the isolation event because the runners need to
separate". It is one cascade move.

**2.5 Who can be carried in** `[derived]`. During a separation of duration `δ`, a reading `d` moves by `d·δ`. It is
carried over the entering edge only if its distance to that edge is less than `d·δ`. At a grid instant the others sit at
their grid positions with the deviation added, so their distance to the entering edge is set by the grid and the
deviation. So what is carried in is decided by the reading's speed against the separating crowd's (through `δ`) and by
its place on the grid. The move types say the same in the cascade's order `[PROVED — SweepBridgeN; E142]`:
- **sweep:** the next setter is slower, same lap; it continues only while consecutive ratios stay below
  `ρ_k = (8k+1)/(8k−1)` (`sweep_lap_bound`, `[PROVED]`: a pair hands over by sweeps on finitely many laps);
- **bridge down:** slower, earlier lap;
- **bridge up:** faster, later lap: a faster reading carried in. Between bridges up the setter's rank strictly falls.

*Frame check:* the rank fall is a fact about the move types. Using it as a move budget ("at most seven moves per run") is
the imported shape (E172, E184). It stays a description of the order in which the crowd separates.

**2.6 The landing** `[PROVED]`: an exit after which nobody is in the slot; its exit is a certificate `(h, K)` (host `h`,
lap `K`), and the host is the slowest member of its lap-`K` cluster (E143, forced). Whether it is lonely is read from the
others' positions at that exit, `d·(8K+1)/(8h)` (whole numbers), the band condition (`lonely_eight_of_opening`).
*Frame check:* the certificate is how the landing is *checked*. Searching certificates directly is the trap (F14).

---

## 3. The recursion: the same mechanism at every scale

**3.1 The split** `[VERIFIED — E147, E148, readings ≤ 24]`: split the readings at the largest gap into a slow group `S`
and a fast group `G`. The cascade's landing is `G`'s own landing (the cascade run on `G` alone) inside `S`'s common
block, in 42,013 of 42,013 band sets and 102,583 of 103,355 wider Case B sets; the rest are `S` leading, the grid nudge,
or a forced delay of one group by the other (E150: 260, 51, 169, 292 of 772).

**3.2 The reduction** `[PROVED — SlowBlockN]`: on `S`'s common block, the whole question is exactly `G`'s
(`block_iff_fast`, `exists_block_iff_fast`, and on any lap `exists_block_iff_fast_lap`); real readings.

**3.3 What the recursion means in the cascade's terms** `[derived]`: `S` is one unit at its own scale (an R1 group at
`d_min`'s scale), clear on its common block; inside the block the cascade is `G`'s cascade. `G` has at most six readings,
so its isolation exists by the native lower order; its **position** relative to `S`'s block is what the lower order does
not supply (E149). And `G` itself splits at its own largest gap, so the landing is a nest: blocks inside blocks, down to
single readings (E155: clusters at well-separated scales, nested; `nested_clear` `[PROVED]` for ratios `≥ 7/3`).

**3.4 Where it was left.** The owed statement (E151, corrected E152): *the fast group has its own point before the slow
group's common block (on its lap) ends.* E153–E154: from a start inside the block, a six-crowd's own chain can need the
slow runner's second block; in every such case read through the cascade the chain is the same: the crowd runs out of
shared blocks, the slow runner sets one move itself (its exit at `9A`), and the crowd lands 1–5 moves later inside the
second block `[VERIFIED — the 10 of 112 starts that needed it]`.
*Frame check:* E153's hill climbs and worst-start scans were searches for extremes; the owner stopped them (E155). What
the cascade showed in E154 (the slow runner sets a move and carries the crowd) is the mechanism; the search was not.

---

## 4. The one question, stated in the cascade's objects

The owner's design leaves one question (E158): **separating one pair cannot keep putting another runner into the slot
for ever.** In the objects of §2 and §3 `[derived]`:

- By 2.2, the chain continues exactly when, during each separation, someone is carried over the entering edge.
- By 2.5, what is carried in is a faster reading at a later lap (a bridge up) or a slower one at the same or an earlier
  lap (sweep, bridge down); sweeps are limited by `ρ_k`, so the chain is sustained by bridges up.
- By 3.3, inside the slow group's block the question is the fast group's own chain: the same question, one scale down.

So the one question is: **why the carrying-in stops inside the block**, in terms of where the readings sit on the
arrangement's grid when each separation happens. The owner's answer on record is that it cannot keep going because the
arrangement is a grid plus a deviation, and a deviation can put only so much in the slot before the grid's own spacing
takes over (*"three runners involved … it starts to apply AP again"*, E139).

*Frame check on the question itself:* "it stops" is the imported shape only when it is argued by a decreasing quantity
or a count of moves. Argued by **where** the readings are at each separation (their grid positions and deviations), it
is a place statement: the landing is the end of the first separation that carries nothing in, and that separation is
named by the grid and the deviation.

---

## 5. What the oracle gives that no other frame has, and how to use it

For every arrangement the cascade gives the whole chain: every crowd, every separation, who was carried in, over which
edge, from which grid position, and the landing. Perturbing one reading shows how each of these moves (E67, E74, E102,
E155: *"test with the cascade and perturb if you need"*). No other frame has this: covering and measure see only whether
every instant is blocked; certificate families see only whether some instant is clear.

**Use:** the questions in §6 are answered by reading chains and perturbing, one arrangement at a time, never by counting
how often something happens (rates) and never by testing an instant family apart from the chain.

---

## 6. Design questions (for discussion before any step)

1. **The carrying-in, read on the grid.** At each separation in a chain, the reading carried in: its grid position at
   the preceding grid instant and its deviation, against the separation's length. Is "carried in" always "a reading whose
   deviation has moved it to within one separation of the entering edge", and does the deviation needed grow at each
   step? This is 2.5 made into the chain's own record.
2. **Why it stops inside the block.** In E154's ten chains the slow runner set one move and the crowd then landed. What,
   at that move, stopped the carrying-in: the grid spacing (*"it starts to apply AP again"*) or something else? Read
   through the cascade and by perturbing the deciding runner.
3. **The nest.** Is the landing always the innermost point of the nest (§3.3) on the first compatible laps, with each
   level's delay a separation? If so the landing is named by the gaps (the nest) and the laps, which is the owner's
   finiteness (*"not a whole lot"*) in the cascade's terms: finitely many nest shapes, each a grid plus deviation.
4. **The exceptions of the recursion** (E150's 772: `S` leading, the grid nudge, forced delays) through the three
   questions (map v2 M3), as places in the nest.

**What will not be done** (the traps, each with its record): testing instant families apart from the chain (F14:
E193–E195, E186); covering, measure or density as the answer (F2: E171); move budgets or ranks as the argument (F1:
E170, E171); another proof's architecture as the object (E192 onward); searches for extremes (E153; the owner, E155);
restating the conjecture as a question and calling it progress (F4: E163, E187).

---

## 7. The owner's proof breakdown (E199), checked step by step

**Owner:** *"For n=8 proof, we need to prove existence or exhibit - double check that.  The proof is that for 8 runners
any arrangement eventually, each runner becomes lonely.  For our framework, we should lonely is proven for AP and grid -
so for that we already have existence/exhibit - that works for ap/grid but not every arrangement.  Next step is any
arrangement is not infinite.  We prove that for 8 runners there are only so many arrangements.  Then we should those
arrangements can be reference to the ap/grid arrangement and that for those finite arrangment they are simply ap/grid
plus divation.  Cascade works because it shows the map of where that displacement is relocated to."*

**7.1 Existence or exhibit** `[checked]`. The target `LRC.Spec.LonelyRunnerAt8` (`Spec/Target.lean:401`): for every
injective `v : Fin 8 → ℝ` and **every** runner `k`, there **exists** `t > 0` with every other runner at circle-distance
`≥ 1/8`. Existence is required; the proofs here are classical (`Classical.choice` is in the axiom list), so a witness
need not be constructed. In the framework the two coincide: `doors_agree` (lonely ⇔ the cascade arrives) and
`first_isolation_of_fixed` (its landing is the first lonely instant), so any existence proof yields the exhibit, the
cascade's landing.

**7.2 AP and grid** `[PROVED, tracked]`, with deviation neighbourhoods, not only at the exact references:
`APNeighbourhoodN` (the AP with every speed deviated by `|eᵢ| ≤ 1/32` of the gap: every runner lonely at a named
instant; *"the deviation only relocates the isolation, between the class-1 instant and its mirror class 7"*);
`GridNeighbourhoodN` (every complete grid, residues mod 8 all different, deviation `|eᵢ| ≤ ρ`: named instants);
`GridNudgeN` (one blocked reading pushed out by its own deviation); `GridPairLawN.grid_class_clear` (per-reading
conditions: interior residues `2…6` within `1/c`, the edge residues one-sided within `6/c`); `NestedBlocksN.nested_clear`
(consecutive ratios `≥ 7/3`: some instant clear). So the base already has the owner's form: **a reference plus a
deviation, with the isolation relocated to a named instant**.

**7.3 "Only so many arrangements"** `[derived; the owner's idea made precise]`. Up to the proved symmetries, shift
(`lonelyAt_add_const`) and scale (`lonelyAt_const_mul`), an arrangement of eight speeds is its seven consecutive
**gaps**, normalised to sum 1: a point of a **closed simplex**, which is compact. That is the precise sense in which
*"speed arrangements may be continuous but they are not infinite"* (E139): a continuum, but a compact one. Its
boundary faces (some gaps zero or relatively tiny) are coincident or clustered speeds: the lower orders (native since
2026-09-25) and the near pair (E140), and a far outlier (*"8 million and 7"*) is a point near such a face (seven gaps tiny
against one). The mirror (`v ↦ −v`) and the eight choices of subject (paired by the mirror) cut the work to four subject
positions on one simplex.

**7.4 The proof this gives** `[derived]`: cover the compact simplex by **finitely many explicit pieces**, each a reference
(the AP, a grid) plus a deviation region, each proved lonely at a named, relocated instant (as `APNeighbourhoodN` and
`GridNeighbourhoodN` already are), with the boundary faces covered by the lower-order and separated-scale pieces. By
compactness a finite cover exists **if every point has such a piece around it**; so the cover must be **built**, piece
by piece, and checked, not inferred (inferring it from local stability would presuppose that every point is lonely,
which is the conjecture).

**7.5 The cascade's role** `[derived; the owner's "the map of where that displacement is relocated to"]`: at any point
of the simplex the cascade gives the relocated isolation exactly, and how it moves as the deviation grows (continuously,
until an event where it relocates by a separation, E178–E182). So the cascade tells, for each region, which reference it
belongs to, what the relocation rule is, and where the region ends (the next event). The pieces are read off the
cascade's map; the proof checks each piece.

**Frame checks.** (a) Compactness here is the owner's own idea (E139, E146), and it is a tool the framework already
uses (`lonelyAt_of_limit`); the covering is of **arrangement space by proved mechanisms**, not of time by blocked sets
(the other frame, F2). (b) E145's trap is avoided only if each piece is defined by its reference and deviation region,
never by "lonely here": a piece whose definition contains loneliness makes the cover the conjecture again. (c) The
pieces must be the cascade's relocations (separations), not instant families it does not use (F14).

**7.6 Questions for the owner before any step.**
1. Is 7.3 (the gap simplex, compact, faces = lower orders) the sense of "only so many arrangements" you mean?
2. The pieces: the existing neighbourhoods have small radii (`1/32` of the gap). The cover needs larger regions: a
   reference plus a deviation carried as far as the cascade's relocation stays of one kind. Is that the intended size of
   a piece (a reference and its relocation rules up to the next event), or something else?
3. Which reference first: the AP (the barycentre of the simplex, where every gap is equal) and its neighbourhood grown
   along the cascade's map, or the grids?

---

## 8. The complete account of the cascade (map v3 Q8) — for the owner's approval before any work

**Owner, 2026-10-01:** *"Yes I was just thinking the same thing.  We keep proposing mechanisims, testing them and finding
exceptions.  We should really know and understand what the cascade does in all configurations, not be testing to find
out something different happens.  I think this is the next major piece of work.  There should be no gaps in what we
understand should happen"*.

**8.0 What "no gaps" can mean, stated plainly.** The cascade arrives exactly when the subject is lonely (`doors_agree`).
So an account with no gaps anywhere, including why every run ends, is the proof itself. The design therefore does two
things. It closes every other gap by derivation: what each move does, what patterns moves make, how the run changes with
the speeds. And it isolates the one gap that is the obligation, in the form most likely to be derived: a statement about
**where** the readings sit when the last separation happens (a place), never that the run stops (§4's frame check; map
§6 F1). Everything is graded: `[PROVED]`, `[derived]` (on paper, then checked), or **gap** (stated exactly, not yet
derived). An observed pattern is data awaiting derivation, never understanding.

**8.1 The discipline (map v3 M8).**
1. **Derive first.** A statement enters the account with its derivation from the definition, the proved lemmas, or
   earlier derived items.
2. **A run checks a derivation.** The pass condition is that the derived statement holds on every case of an exhaustive
   or seeded-uniform population, with the oracle check (C1). There are no survival criteria, rates or majorities.
3. **An exception means the derivation is wrong.** Read that chain move by move, perturb through the cascade if needed
   (the owner's tool), find the step of the derivation that fails, and repair the derivation. Never re-scope the
   statement to exclude the exception without a derived reason (sharpen-and-narrow; map §6 F3, F11).
4. **Reading a chain in full is understanding, not discovery.** A single chain, explained move by move from positions, is
   a derivation on one instance and is encouraged. Running a population to see what happens is what 8.1 replaces.
5. **Frame check on every item** (§ header test; map v3 §0's interval check; F14's question: does it study what the
   cascade does?).

**8.2 Level A: the step** (complete by derivation; the catalogue to write out in full with each item's derivation and
its Lean anchor).
- A1 The move `[PROVED — Cascade/Iteration.lean]`. From `t`, the crowd is the readings in the way; the next instant is
  the latest next opening among them. Moves strictly increase; no lonely instant lies inside a move.
- A2 Who is in the way after a move `[PROVED — SeparationN.transport; derived]`. The next crowd is exactly the readings in
  the way at the setter's exit. Each is an **arrival** (outside at `t`, entered during the move and still in) or a
  **re-entry** (a fast crowd member that left and came back). Nothing else is possible.
- A3 The arrival condition `[derived]`. With positions in eighths, `p_q(t)` for reading `q` and move length `D`, `q` is
  in the way at `t + D` iff `(p_q + 8qD) mod 8 ∈ (−1, 1)`. Every position advances linearly at its own speed; the step is
  that rotation, read at the setter's exit.
- A4 Move types `[PROVED — SweepBridgeN]`: sweep (slower, same lap), bridge down (slower, earlier lap), bridge up (faster,
  later lap). Exhaustive for the next setter against the current one.
- A5 The landing `[PROVED — lonely_eight_of_opening]`. An exit with nobody in the way is a certificate: setter `h`, lap
  `K`, and a lap `k_d` for every other reading. That the setter is the slowest of its lap-`K` cluster is `[derived]`
  (E143; checked in E203), not part of the Lean statement.
- A6 The bound and its captures `[derived]`. At `R = 1` the readings in the way are those with `d/d_min mod 8 ∈ (7, 9)`:
  grid slots 7 and 0 of the slowest reading's grid (E202).

**8.3 Level B: patterns of moves** (derived items, each with its exact conditions; observed items listed as data).
- B1 Passages `[derived; checked E203]`. A lap-`k` cluster (consecutive ratios below `ρ_k`) goes through the slot in
  descending speed and ends at its bottom's exit (E142–E143).
- B2 Bridges `[derived]`. A passage's end is a landing unless some reading is in the way there, and by A2 it arrived
  during the last move.
- B3 The junction condition `[derived — E125, E208]`. Consecutive setters `(a, k)`, `(b, l)` join iff
  `s_b(8k+1) > s_a(8l−1)`. On the slowest reading's grid this splits exactly into the grid's part plus the deviation's.
- B4 Relays and the conveyor (E203–E204): **data, not yet derived.** When is the next setter the queue front? Not
  forced (several carried in: the latest exit sets the move). Gap B4: the exact condition, from A3.

**8.4 Level C: the run as a function of the arrangement** (the wall structure; derived, with its local rules).
- C1 Walls `[derived, for a chain of finite length]`. A chain's sequence of setters and laps changes only where some
  reading sits exactly at an edge at some move's instant: `(8K+1)·d = (8k ± 1)·h`, one linear equation in the speeds, a
  hyperplane through the origin. Between walls a finite chain is constant, the landing certificate included. (That every
  chain is finite is the obligation, `doors_agree`; every chain the oracle has run is finite.) E124's cover is this structure for the
  band's landing ("cut only along walls").
- C2 The local rule at each kind of wall `[derived in part]`:
  - a setter swap (two crowd members' exits coincide): continuous;
  - the landing's leaving face: a hand-off to the slowed reading's opening, unless another reading's slack is used up or
    the change clears an earlier instant (E218 M4-3, derived). E219: fine shapes 1,694 of 1,800 hand off and 106 go
    earlier; whole-number sets 1,404 hand off, 153 go earlier and **243 are other** (a tight reading, or the moved
    reading passing another). M4-3's derivation assumed the moved reading keeps its place: **gap C2a**, repair it;
  - the landing's entering face: if the run to the landing is unchanged, one more move to the entering reading's exit
    (E218 M4-4, derived), then the chain from there. 281 of 1,800 fine-shape crossings cleared an earlier instant instead
    (the condition failing, E219);
  - an arrival flip at an intermediate move: a reading at its entering edge exactly at a setter's exit arrives on one
    side and not the other, so the chain gains or loses that reading's passage. **Gap C2:** the rule for where the chain
    rejoins, derived from A2–A3.
- C3 The persistence box (E218): at the landing, the chain's cell is inside its certificate's box. The box is where the
  certificate holds; the cell is where the cascade uses it.

**8.5 Level D, re-aimed and built from the record (v4).**

*Sources, in order of authority (owner: Lean outpaces the documents):*
- (1) the Lean `Spec/` tree, surveyed module by module (E227): every module's stated content, with commit dates and
  other sessions' untracked modules marked;
- (2) the log and map v3;
- (3) v21 §6.7, §6.9–§6.11, §17;
- (4) handover v10.

Where they differ, Lean governs what is proved.

**The form** (v21 §6.7, amendment 2026-09-20; Theorem 6.15): exhibit `(e, k)`, a candidate scale, as a function of the
arrangement, through rules with conditions shown exhaustive. No bound on `k`.

**The rules already proved in Lean** (the base; each names its instant):
- **Exact form at a scale.** `TwoBlockN.lonely_eight_of_blocks`: at the scale `e/(8K+1)`, every reading in a block
  `[8k+1, 8k+7]` gives lonely. `lonely_eight_of_pairwise_laps` is the same with no flank chosen: pairwise lap
  compatibility, 1-D Helly. This is the exact band condition at a class instant, so v4's first draft's "D-a" is
  **already proved**.
- **Near a grid or the AP, by radius:**
  - `GridNeighbourhoodN.grid_nbhd_exists`: every complete grid, deviations `2ρ(14W + 21) ≤ 1`, every runner at a named
    instant; the radius shrinks as the laps `W` grow;
  - `APNeighbourhoodN`: the AP, `|eᵢ| ≤ 1/32` of the gap;
  - `GridPairN`, `GridPairLawN`: the pair law; within `1/56`, or `1/C` after rescaling;
  - `GridClassN`: class 3 when the class-1 neighbour slot is doubled; one neighbour missing.
- **Two in one slot:** `DoubledSlotN` (the doubled-slot family, exhibited) and `DoubledNbhdN` (under deviation
  `≤ 1/(512(m+1))`, every runner at a named instant; `DoubledNbhdCoreN`'s relocation lemma).
- **A captured reading:** `GridNudgeN` (the largest reading alone in the slot, pushed out by `±1/(8·w)`; fails exactly
  at the pinned pair); `RungR1N` (multiples of `q ≤ 8` captured at a rung `a/q`, carried by R1 among the multiples;
  231,052 of 231,062 sets ≤ 32 in E88's map).
- **Scale structure:** `SlowBlockN`, `NestedBlocksN.nested_clear` (consecutive ratios ≥ 7/3), `SplitChainN`, `CoreDriftN`,
  `OneFreeN` (one reading off the others' period lattice), `TwoBlockN.lonely_eight_of_two_block`, the three-block rule.
- **The case list and the band:** `OrderEightCasesN` (v21 §17C's cases), `BandCoverN.band_lonely` (spread 7–9, every real
  shape), `BandRouteN`.
- **Transport along deformations:** `DeformationN`, `PathRouteN`, `PinchOpenN`, `WindowPinchN`, `PinchTransportN`,
  `MixedLapOverlapN`, `LapDeadlineN`.
- **Another session's work, untracked on 2026-10-01** (read, not ours to commit; cite only when committed):
  - `CascadeTransportN`: a sole blocker determines the next move; a reading active again has a strictly higher lap;
  - `CascadeGridN`: grid certificates bound the actual cascade;
  - `DeadlineRelabelN`, `BidirectionalReplacementN`, `DoubleBacktrackN`, `HandoffDriftN`, `HandoffResonanceN`,
    `PinchReflectionN`, `PartialReflectionN`, `SymbolicWindow*N`, `ArrangementShapeN`.

  Each states that it is local and does not assert coverage.

**What Lean does not have: the targets.** The rules above are each a neighbourhood (a radius) or a family (a pattern).
What is missing is the passage from an arbitrary arrangement to one of them, with no uniform cap:
- **D1. The selection.** From the readings, name a reading `a`, a grid (its divisor), a class `c` and a lap for every
  reading, such that `lonely_eight_of_pairwise_laps` applies. The grid must be a function of the readings, not a uniform
  bound (E215, E217: a uniform step bound is a cap on time). This is handover v10 §4's open step in Lean's terms:
  `lonely_eight_of_pairwise_laps` is the proved rule, and its hypothesis is what is not yet produced.
- **D2. Beyond the radii.** The neighbourhood rules hold for deviations up to `1/(2(14W+21))`, `1/32`, `1/56` or
  `1/(512(m+1))`. Arrangements whose deviation from every grid exceeds these are the open ground. The cascade's
  relocation (Level C: a reading entering at the isolation instant moves it to that reading's exit) is how the isolation
  crosses out of one neighbourhood. Derive, in the grid's terms, where it goes: which neighbouring grid, class or nudge.
- **D3. Captured readings beyond the proved families.** `GridNudgeN` (the largest reading alone), `RungR1N` (multiples
  at rungs `q ≤ 8`) and the doubled-slot family are proved. Owed: several captured readings, or a captured reading that is
  not the largest, at a general grid. `GridNudgeN`'s failure, the pinned pair, is the named obstruction.
- **D4. Transport.** Coordinate with the other session's `CascadeTransportN` and `CascadeGridN` once committed, rather
  than re-derive local transport.

**Not to be re-derived:** handover v10 §4's twelve routes; order seven's multiplier families as the object (F14); the
first window, covering and set emptiness (register items 15, 4, 8); and anything in the Lean list above (cite it).

**8.6 Gap register (v4).**

| gap | statement | builds on (Lean) | checked by |
|---|---|---|---|
| C2a | resolved (E223) | — | `cascade_level_c_check_v1` |
| D1 | the selection of reading, grid, class and laps from the readings, no uniform cap | `lonely_eight_of_pairwise_laps`; the neighbourhood rules | exact: the selected assignment is pairwise compatible on every set tested |
| D2 | where the isolation goes when it leaves a grid's neighbourhood, in grid terms | `GridNeighbourhoodN`, `GridPairLawN`, `GridNudgeN`, Level C | exact crossings (E223's construction) at the radius |
| D3 | several captured readings, or a captured reading not the largest | `GridNudgeN`, `RungR1N`, `DoubledNbhdN`; the pinned pair | exact |
| D4 | transport, with the other session | `CascadeTransportN`, `CascadeGridN` (untracked) | — |

The obligation is D1: a selection whose conditions are exhaustive is Theorem 6.15 by exhibition. It is open.

**8.7 Order of work (v4).**
- First: D3's pinned pair. `GridNudgeN` names it as the exact failure of the nudge. It is the smallest object where a
  proved rule stops, and the cascade's move there is Level A–C's entering-face rule.
- Then D2 at the radius of `GridNeighbourhoodN`.
- Then D1.
- Nothing in Lean until the map is complete (owner, E222). The Lean list is read and cited, not extended.

**8.8 Frame checks (v4).**
- Every rule names an instant and its condition is on the readings (v21 §6.7).
- No uniform cap (D1).
- No window of instants as an object (the interval check).
- Lean first, then the log, then the documents; cite what is there (E225–E227).

**8.9 Questions for the owner:** none at the design stage.
