# The finite cover: design v1 (for the owner's approval; nothing run)

2026-10-02. Written after E270. A design, not a result. Every statement of the record below is quoted to its entry or Lean
file; every proposal is marked **[proposal]**.

## 0. The owner's statement, in the owner's words

- E146–E147: *"the conjecture itself is a limitation to the arrangements that can happen; once you add scale invariance and
  infinity to it, plus mirror effect and circle effect that just displaces the arrangement, you are not left with a whole
  lot."*
- E166: *"because of scale invariance and infinite grid the spread of 7–24 is irrelevant."*
- E270: *"while there are continuous ability of speeds to change there are only a finite set of arrangements of runners.
  This is due to several things, first the conjecture itself means that runner 2's speed can not increase more than runner
  3's speed without becoming runner 3. The scale invariance … and then the fact grid goes on forever. When you logically work
  your way through all the conditions, there aren't an infinite set of arrangments."*
- E270: *"1...7,10000000000, is not a new arrangement from 1...7,17."*

## 1. What is proved in Lean (read, not rebuilt; E270)

| statement | where | status |
|---|---|---|
| order, drift and scale removed exactly: any arrangement is `A + D·s`, `s` an ordered shape `0 = x₀ < … < x₇ = 7`; the target is equivalent to the claim for bounded shapes, "no finite time bound or grid-cover premise added" | `ArrangementShapeN.reduction_iff` (untracked, another session's) | proved |
| the slowest runner alone suffices | `EndRunnerN.lonelyRunnerAt8_of_slowest` | proved |
| a lap assignment with pairwise-compatible laps gives a lonely instant (1-D Helly): the grid regime is sufficient | `TwoBlockN.lonely_eight_of_pairwise_laps`; `RegimeSkeletonN.lonely_of_gridClass8` | proved |
| the AP and every complete grid carry an open neighbourhood in which the isolation is relocated and named | `APNeighbourhoodN`, `GridNeighbourhoodN`, `GridPairLawN` | proved |
| a single fast reading: `V > 7s` for every other `s` | `FastRunnerN` (R8); `blockRule8_one` | proved |
| the band, spread 7 to 9, for every real shape | `BandCover.band_lonely` (105 certified cones) | proved |
| **`Cover8 M → LonelyRunnerAt8`, every `M`, no case split** | `RegimeSkeletonN.lonelyRunnerAt8_of_cover8` | proved |
| **`Cover8 M`: every set of at most seven readings is lonely at the bound, or at a class-1/3/5/7 instant of a grid through one of its own readings `e`, step `e/mm ≥ m/M`** | `RegimeSkeletonN.Cover8` | **owed** (a `Prop`; verified on populations) |
| the scale-free hole `ArrBoundedCovered8 9` | `Order8SkeletonN` | **owed** ("the finite cover not built") |

The step bound `M` is a cap (`Cover8 M ⇒ NB(8⌊7M/8⌋ + 7)`, E170); without it the covering is the conjecture renamed
(every opening `(8K+1)/(8h)` is a class-1 grid instant with `mm = 8K+1`, E216 M4-6, map §5). So the finite cover has
content only if its finiteness is derived without a cap.

## 2. What the record already did on exactly this question

- **E145 (the owner's types).** Type = cluster composition (runs of consecutive ratio below `ρ_k = (8k+1)/(8k−1)`, `k` the
  landing lap), the landing cluster, each outlier's eighth-slot at the landing; laps and in-slot deviations dropped. Finite by
  construction (`≤ 64·7·6⁶`). **Graded `[reasoned]`: the type is defined by the landing, so "every arrangement has a type"
  is the conjecture and the count is not a test.** The test the owner confirmed is predictability from the speeds.
- **E146.** The lap-1 cluster composition alone predicts the landing cluster in at most 55.17% (spread 7 to 24).
- **E147, the recursion.** Split at the largest consecutive gap into a slow group `P` and a fast group `G` (at most six
  readings: a lower order, native and proved). For every landing not at the bound, the full landing **is `G`'s own landing**:
  42,013 of 42,013 (band), 102,652 of 103,355 (spread above 9; the other 703 are delayed by `P`, one blocker in 676, two in 27).
  The one condition left: **`P` is clear at one of `G`'s lonely instants. That is E118's C1 statement**, "now the mechanism of
  Case B as well as Case C"; `FastPair8`, `BlockSplit8`, `OneFreeEightN` are its proved cases.
- **E148–E166.** The regime skeleton: `Cover8`; the spread split retired (E166).
- **E233–E243.** Inside the holes of `Order8SkeletonN` the cascade is two lower-order cascades composed (core relay, then block
  relay inside the core's lonely stretches); `g`, the block's relay landing, is the least clear flank opening after the entry
  (v21 §6.10). Every hole configuration mapped is closed by `lonely_eight_or_residual` (E255): the open content is hole ∩
  `EightResidual`.
- **E256.** Three routes meet at one statement, the C1-shape.

**So the finite-cover work, as the record has reduced it, is the C1 statement: a slow group is clear at a lonely instant of
the fast group (a lower order), with the argument uniform in how far apart the two groups are.** E259–E268 (the flank reading
of the C1-shape) is part of it, done flank by flank. It is also not yet connected to the grid/AP view or to the two ends
(`1…7, 10¹⁰` closed by R8; `1…7, 17` in the scale-free hole).

## 3. The two examples, as the Lean has them (E270)

`S₁ = {1,…,7, 17}` and `S₂ = {1,…,7, 10¹⁰}`: `P = {1,…,7}` (an AP at scale 1), `G = {X}`. Both split at the same gap
(ratio above `ρ₁ = 9/7`), so by E145 they have the same cluster composition (an AP cluster and one outlier); only the
outlier's slot differs, and the slot is grid data (`X mod 8` at the AP's instants). Lean treats them in different cases:
`S₂` by R8 (`V > 7·7`), `S₁` as scale-free. The owner's statement is that this difference is not real: **[proposal] the work
is to derive, from the grid's periodicity and the AP's scale invariance, that the argument for `P` clear at a lonely instant
of `G` depends on `G`'s distance from `P` only through finitely many grid data (residues), so that `S₁` and `S₂` are covered
by one argument.**

## 4. What is to be proved (derive first, M8)

**[proposal]** Three statements, each in the framework's own objects, none with a cap:
1. **Types from the speeds alone.** A classification of arrangements by the largest-gap recursion (E147) and the position of
   each group's readings on the grid (residue classes and the sign of the deviation relative to the neighbour), **not by the
   landing**. To be derived: that it is finite once ordering (runner 2 cannot pass runner 3), scale and the infinite grid are
   used; that `S₁` and `S₂` fall in one type; that nothing in it depends on the cascade's route.
2. **The recursion step.** For a type, `P` is clear at a lonely instant of `G`. This is Q9 (v4 §4) in full generality. Known
   pieces: the persistent classes at a flank (E266); the AP/grid neighbourhoods (Lean); `FastPair8`, `BlockSplit8`,
   `OneFreeEightN`, R8 (separated cases); the cascade's two relays inside the holes (E233–E237).
3. **Exhaustiveness.** Every arrangement has a speed-only type (this is the reduction that the owner's three conditions give,
   stated as a lemma in Lean beside `ArrangementShapeN.reduction_iff`).

## 5. Order of work **[proposal]**

1. **Read the one-parameter family, by the cascade** (a map run, M2 d; derivation checks and the oracle check only).
   `{1,…,7, X}` for `X` from 8 to a few thousand and for `X` near `10¹⁰`: for each, the landing (setter, residue, lap), the
   relay's route, and which grid datum of `X` (its residue mod 8, mod 56, the sign of its deviation from the grid) decides it.
   The owner's claim is tested directly: what varies with `X`, what does not.
2. **Derive the recursion step for a block of one**, `G = {X}`, uniformly in `X` above `P`'s top: `P`'s clear windows (an AP's
   are periodic, scale-invariant) against `G`'s lonely instants (a single reading's clear arcs). R8 is the far end; the near
   end is where the windows' lengths and `G`'s period are comparable. State where the argument stops being uniform, if it does.
3. **Extend to blocks of two, three, …, six**, using the lower orders (native) for `G`, and the holes' mapped relay structure.
4. **Write the classification and the exhaustiveness lemma**, then put Q9 (the C1-shape) inside it as one type.
5. Lean follows the map (E222: not before the map is complete).

## 6. Decisions for the owner

- Whether the classification in §4 item 1 is the right object: speed-only types by the largest-gap recursion plus grid
  residues (the E145 definition without the landing), or another.
- Whether to begin with §5 step 1 (the family `{1,…,7, X}` read through the cascade).
- Whether the hand-off reading (E268's next step) is dropped, or kept as part of §5 step 2.
