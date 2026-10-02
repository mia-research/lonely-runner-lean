# What restricts the arrangement space: a derivation from the conditions (v2)

**v2 (2026-10-02, after E274).** v1 is retained unchanged. v2 changes one thing: the drift quantity `|ε|L` is a **coordinate** (the deviation read at an instant of lap `K`), not a requirement the proof has to bound. The owner asked whether it flows from the conditions or was added; E274 answers it (below, §2 and §5). The corrected places are marked **(v2)**.

2026-10-02. Written after E271, at the owner's instruction (*"Ok, lets start again. I want you to logically think of the
conditions that restrict the arrangement space … You need to reason this through"*). This is reasoning, not a result:
**[Lean]** = proved in the Lean tree (read, E270); **[record]** = on disk in the log or manuscript; **[reasoned]** = derived here
from those, not checked, not in Lean. No run was made. The owner's text is quoted where it is the premise.

## 1. The conditions, in the order they cut the space

1. **Order (the conjecture itself).** Runner 2 cannot pass runner 3 without becoming runner 3. So an arrangement is an ordered
   set; the readings from any subject are increasing and the lap vector of a lonely instant is monotone (every landing lap vector
   measured is monotone with `k₀ = 0`, E120). **[Lean]** `ArrangementShapeN.exists_sorted`; relabelling and mirror
   (`lonely_relabel`, `EndRunnerN`).
2. **Scale.** `v` and `λv` are the same arrangement with every instant divided by `λ`. `0.000001…0.000008`, `1m…8m`, `1π…8π`
   are one arrangement. **[Lean]** `ArrangementShapeN.lonely_affine`, `reduction_iff`: six free values in `(0, 7)` remain.
3. **The circle (mirror, drift).** A common speed added to all runners changes nothing; reversing the speeds swaps the slowest and
   fastest. **[Lean]** same file; `EndRunnerN`.
4. **The grid goes on for ever.** A reading's clear set is the comb `‖d·t‖ ≥ 1/8`: period `1/d`, duty `3/4`, identical on every
   lap. At an instant only the reading's **residue mod 8 against the instant's scale** and its **deviation** matter; the lap is
   invisible. At the class-1 grid instant `1/8` a whole reading is blocked **iff it is `≡ 0 (mod 8)`** (a reading in the
   subject's own slot); residues `1` and `7` are exactly on the edge and are clear (BSM's strict inequality).
   **[Lean]** `GridNeighbourhoodN`, `GridClassN`, `TwoBlockN.lonely_eight_of_blocks`; **[record]** v21 §6.8 and §6.14.
5. **Tightness at eight.** The threshold `1/8` equals the spacing of the regular octagon, which is the AP at its class-1
   instant: every runner exactly `1/8` from its neighbours. So the AP (and every complete grid, an AP with extra whole laps) is
   the one configuration with **no slack**; every other arrangement has some slack at some level. **[reasoned]** from 4 and
   `GridNeighbourhoodN` (the AP's open neighbourhood).

After 1 to 3 the space is the six-dimensional simplex of gaps. Nothing in 1 to 3 makes it finite. 4 and 5 are what make the
*structure* finite, as follows.

## 2. A reading against a scale: free, or locked, and one real quantity decides which

Fix an instant scale (a grid through a group of readings, step `e/mm`). Take one other reading `x` (a runner, or a group
treated as one). Along the window where the rest are clear, at its successive openings `x` reads `A + εu (mod 8)`
(`x/e = A + ε`; E253). Two things are discrete and one is not:

- **discrete:** `A mod 8`, the residue (the slot `x` is captured into by the grid), and the sign of `ε`;
- **continuous:** `|ε|`, the drift per opening, against `L`, the number of openings the window holds.

A walker is in the way for at most about `1/(4|ε|)` consecutive openings (a mover blocks at most half its period; **[record]**
`card_allowed_two_mul`, Theorem 6.18, E260). So:

- **free:** `|ε|·L ≳ 1/4`. The window outlasts the walker's block, so it is clear at some opening. A far reading (`ε` not
  small, or `L` large) is free. This is R8 for one fast reading and the nested relays for blocks; the lonely instant is
  *constructed* by the walker's own opening. **[Lean]** `FastRunnerN`, `blockRule8_one`, `SplitChainN`. **[reasoned]** that this
  is the whole of "far".
- **locked:** `|ε|·L ≲ 1/4`. The walker keeps one slot for the whole window; which slot is the residue `A mod 8`. A locked walker is
  harmless unless the slot is 0 (captured, "two runners in the same slot": the owner's *one mechanism that delays the
  isolation*, E115, E256) or the slot is an edge it drifts across (the sharer's edge forms, `A ≡ 1, ε < 0` and `A ≡ 7, ε > 0`).
  **[record]** E253 (62 of 83 shadows are one such walker), E258.
- **between:** the walker is neither: it sweeps part of a slot, then another walker takes over (the hand-off). This is the only
  place a continuous quantity survives, and it is bounded on both sides by the two cases above.

**(v2) Status of `|ε|L`.** It flows from condition 4 as a coordinate: at an instant of lap `K` a deviation `δ` (in grid steps) displaces a reading by about `K·δ`, and it is what the Lean neighbourhood radius `2ρ(14W + 21) ≤ 1` bounds. v1 turned it into a regime split (free, locked, between) with the middle a hole to be covered. That split is the bookkeeping of the per-opening walker view (Theorem 6.18, the flank proxy, E120), not something the cascade pays for: in E274, over about 22,000 arrangements with whole laps up to `10⁶`, deviations up to `0.45` of a grid step and scale ratios up to `10⁹` (clump hierarchies to `10¹²`), the cascade used at most 13 moves and landed with `R* = 8·d_min·t* ≤ 5.02`; neither number grew with the laps, the deviation or the ratio. So the proof is not required to bound it; the deviation is the continuous parameter and the cascade relocates the isolation along it. The earlier statement of a bounded interval `(0, 1/4)` as the one real quantity is kept as a description of the proxy, not as a hole.

So a reading's relation to a scale takes **finitely many discrete values (residue, sign)** and **one real parameter confined to
a bounded interval** `|ε|L ∈ (0, 1/4)`, plus the free case. That, and not the size of the speeds, is why `X = 17` and
`X = 10¹⁰` are not different arrangements: the size of `X` only enters through `L` and `ε`, and past the point where
`|ε|L ≥ 1/4` it is free; below it, it is locked in a residue slot, and there are eight.

## 3. The types

Read from the subject. Group the readings into **clumps** (readings within a small ratio of each other, relative to the scale
that matters for the instant) with gaps between clumps.

- **(a) Evenly spaced: the AP.** If the readings are evenly spaced (speeds `a + i·g`), the subject's readings are `j·g`,
  `j = ±1, ±2, …`: an AP at scale `g`. Small or large `g` is scale. It is the octagon at `1/(8g)` with no slack. Evenly spaced
  **with whole extra laps** (the readings' residues mod 8 all distinct and nonzero) is the same octagon at the same instant
  (the lap is invisible): the complete grid. **[Lean]** `GridNeighbourhoodN`, `APNeighbourhoodN`: each carries an open neighbourhood
  in which the isolation is relocated, named, not lost. The radius shrinks as the laps grow (`2ρ(14W + 21) ≤ 1`), which is a
  property of the neighbourhood and not a restriction on the type.
- **(b) A clump of at most six, with outliers.** The clump is a lower order (native, proved): `j ≤ 6` readings are lonely at
  `1/(j+1) ≥ 1/7`, so at `1/8` it has slack `≥ 1/56`, which gives windows of positive length around its lonely instants. An
  outlier is then a single reading against a window of `L` openings of the clump's flank: free or locked as in §2.
- **(c) A clump that is too evenly spaced.** If the clump is close to an AP at its own scale, it has no slack to spare (it is the
  case (a) at its own scale), and its outliers are **captured by the grid**: each takes the residue slot its ratio to the
  clump's step gives. The outlier's slot, not its size, is the datum. This is "AP plus grid to capture the outlier"; the
  AP's grid is the clump's own. **[reasoned]**
- **(d) A clump that is not evenly spaced.** It has slack (lower-order lonely windows) in proportion to its irregularity, and
  that slack is what a nearby outlier needs in order to be free. **[reasoned]**
- **(e) Several clumps.** Apply (b) to each pair of adjacent scales, from the slowest up: the slow group is a window source, the
  fast group an outlier (the largest-gap recursion, E147).

## 4. The two examples

`{1,…,7, X}`: the clump is the AP `1…7` (case (a) at scale 1, a complete octagon at `1/8` for the subject at 0), and `X` is the
outlier, captured by that grid.
- `X = 17`: `17 ≡ 1 (mod 8)`, the leaving edge. Lonely at `1/8`. The slot is an edge, harmless.
- `X = 10¹⁰`: `10¹⁰ ≡ 0 (mod 8)`: captured, with the AP's own readings `≡ 1` and `≡ 7` on both edges: the pinned pair
  (E228–E229). `X` is an exact multiple of 8, so `ε = 0`: locked, for every class instant of the AP's grid, **for ever**
  (`X·t ∈ ℤ` at every `t = (8K+1)/8`). The isolation has to leave the AP's grid for another scale (`e = 7`, `e = 6`, … as the
  cascade does) where `X`'s residue is no longer 0.

So they are one arrangement in the sense of §3 (an AP and an outlier captured by its grid) and two cases in the sense of the
residue (`r = 1` or `r = 0`). The statement to prove is that the residue cases are finitely many and each has an instant, and
that the size of `X` never adds a case. **[reasoned]**

## 5. What is finite, and what is not yet shown to be

Finite, **[reasoned]** from 1 to 5: the number of clumps (at most seven readings), each reading's residue slot and drift sign
against each scale (eight residues, two signs), the grid kinds through each clump (class `c ∈ {1,3,5,7}`).

**(v2)** What is not shown, and is the remaining content: that **the relocation along the continuous deviation never fails**: from an exact type (an AP or a grid) the isolation moves as the deviation grows (hand-off across a leaving face, one move to the entering reading's exit across an entering face: Levels A–C, C.4, C.5) and the sequence of relocations reaches every arrangement. The deformation route of the record is this (E178–E182, `DeformationN`, `PathRouteN`): local stability is proved for one-runner moves and a simple pinch; open are multi-pinches and the bounded-time half. The flank-by-flank statements (the places where several walkers lock and unlock in turn, the hand-off) are this relocation seen through the proxy. The proof needs, for a clump and its outliers, that **some instant has
every walker either free or locked in a harmless slot**. In the record that is E118's C1 statement (E147, E256), and the work of
E253 to E268 is its flank-by-flank form: the persistent classes (a locked walker: near-sharer, twin below, near-harmonic) are
derived (E266); the free case is the nested relay; the hand-off is open. A joint cover of all flanks would need the hand-offs to
chain across the whole window at every scale at once, and E268 found at most three of six flanks shadowed in any population read.

## 6. What this changes about the next step **[proposal]**

- Take the classification of §3 as the object (speed-only: clumps, and for each outlier its residue and drift against each
  group's scale), not the landing.
- The recursion step is a statement about **two groups at adjacent scales**: the slow group's clear window, the fast group's
  residue slots and drift. State it first for a block of one (`G = {X}`) and prove it for every `X` above the clump with the
  residue as the only datum.
- **(v2)** Then state the relocation rule per type (how the isolation moves with the deviation, and where a new type takes over), and read the open items of the deformation route against it, instead of reading the hand-off flank by flank.
