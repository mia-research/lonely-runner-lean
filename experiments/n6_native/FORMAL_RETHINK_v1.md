# Order six: what the formal proof uses, and what today's results could replace — v1

2026-10-16. Owner: *"lets rethink about our proof formalisation and think if any of this can supersede any of it"*.
Facts from the tree (`LRC/Spec/OrderSixWholeN.lean`, `lonely6_of_lt`) and this log; candidates are labelled as such.

## 1. The proof of record at order six, by part

| Part | Module (lines) | Source of the argument | Status after E58 |
|---|---|---|---|
| Real speeds → whole numbers | `RealSixN` + `SteppingN`, `MergeSixN` | framework (rows, merge, pigeonhole stepping) | native; the reduction is BHK Lemma 8's shape (E59) |
| Dispatch | `lonely6_of_lt` | BHK's case split | BHK's; the cascade does not split this way (E57) |
| §8 (v₃ ≤ 3v₁) | `OrderSixEightN` (828) | BHK §8 in framework form | reformulated |
| §5 (D ∣ v₁) | `OrderSixSecFiveEN` (1,976) + Prop 11 modules | BHK §5 / Prop 11 at named instants | reformulated |
| §6 (D ∣ v₃, D ∤ v₁) | `OrderSixSixN` (1,487) | BHK §6 | reformulated |
| §7 and §2 | `OrderSixSecSevenNativeN` (1,020) | native route (2D global isolation, window lemma, G₄/G₇ boxes) | **native, in the dispatch** |

## 2. What today's results add (all [PROVED] unless marked)

- `ap_plus_one` (every order): AP 1..n−2 plus any runner — lonely at 1/n or at the fold 1/n + 1/(nX). Generalises R6
  (no multiple of n → 1/n) by the fold case.
- `knot_other_side` (every order): when a box dies at a knot, the knotted pair is satisfied in the next box iff
  2a ≤ (n−2)b + n − 3.
- `k2a_empty`, `closer_same_forces_fastest`, `fastest_lap_one_first_jump` (every order): the two empty outcome classes.
- Observations (not proofs): every isolation is a unit fold of ℤ/q (E66); deaths relocate by a chain of knots (E68);
  window-and-fold by slack depth (E75–E76); twelve outcome classes from order 4 on (E77–E78); long cascades come from
  a run ending on a multiple of n (E79).

None of these replaces §5, §6 or §8 as it stands: none is a statement about all sets of one case.

## 3. Candidates that could replace a part (not yet attempted)

1. **§8 by a slow-block window and the two-runner window lemma** [candidate]. With v₃ ≤ 3v₁, runners 1–3 are clear
   across [1/(6v₁), 5/(6v₃)] (length ≥ 1/(9v₁)); E7 found §8's cascade walk equals the walk of {v₁, v₄, v₅} in 3,710 of
   3,716 sets (runners 2, 3 inert). `window_two_uniform` (proved, sharper than BHK Lemma 4) closes runners 4, 5 when the
   window is long enough relative to v₄ (v₄ ≥ 6v₁ suffices for the first window). Owed: the sets where v₄ < 6v₁ or a
   slow runner blocks (E7's 6 exceptions, E8's 88 to 60); test first, on the §8 sets, which window and lap closes each.
2. **§5 and §6 natively** [candidate]. These are the collapsed orbits (E57): at the meeting times k/D runner 1 (§5) or
   runner 3 (§6) sits on the subject, so `s7_main_route` has nothing to work with. The fold picture suggests the shifted
   meeting instants (k + 1/2)/D or the next lap; not tested.
3. **Replace BHK's core by Renault's in framework form** [reformulated track; owner's decision]. Renault 2004's moves
   (residues mod 6, sixth shifts that fix multiples, scaling λ ≤ 5, an order-five seed) are the order-five core's
   mechanisms one order up (E62). Chen's Lean formalisation is Apache-2.0 (licence file checked), so a port with
   attribution is permitted; it would replace §5, §6, §8 and the dispatch by one argument whose objects match order
   five. This serves the one-framework paper; it is not native in the sense of the cascade.

## 4. Suggested order

Candidate 1 first (closest to existing proved lemmas; test then prove), then 2; 3 is a separate decision.
