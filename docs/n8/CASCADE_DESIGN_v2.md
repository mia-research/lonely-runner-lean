# Order eight — how the cascade works: a design document (v2)

2026-09-30. **Design phase: reasoning only, nothing run.** v2 adds §7 (the owner's proof breakdown, log E199); §1–§6 are v1's, unchanged. Owner: *"Maybe we need to spend more time in the design phase.
Thinking and reasoning through how the it works.  But also think and reason all parts along the way.  Every step has to
be though of, am I trying to fit this to another frame to avoid it.  We have a perfect oracle that is so much an
advantage that others don't get and we seem to be wasting it because it doesn't look like other frames"* (log E198).

This document works inside **the owner's design as it stands on record** (log E139–E163), not a design of mine. Every
step carries a **frame check**. The test used for it:

> **Would this step make sense to someone who had never seen the cascade?** If yes, it is probably another frame
> (covering, measure, certificate families, multipliers, termination ranks, density), and the cascade has been demoted
> to a check. The step must study what the cascade does: its moves, the readings in the subject's slot, their
> separation, and where the isolation lands and moves.

Grades: `[PROVED]` (Lean, with the declaration), `[VERIFIED — scope]` (exact computation on a stated population),
`[derived]` (on paper here), `[owner]` (the owner's statement, quoted).

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
