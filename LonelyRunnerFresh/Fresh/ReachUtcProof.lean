import Fresh.M4CertSound
import Fresh.M4CertRung2_1_1_3_4_5_5_7

/-!
# ReachUtcProof: the discharge of OWED (b)'s PROOF side — reach_utc's no-completing-state
verdict certifies no (zone-form) `ChainRealized` continuation

Written 2026-11-21.  New file; nothing existing is edited.

## What is proved here

`Fresh.M4CertSound.DfsPruneDom`'s per-prune-leaf condition is the [P] conclusion of the
`reach_utc` state-graph abstraction: from a leaf's state `(frontier-sup P, rank a)`, the
explored `(frontier-sup, reading-rank)` state set contains no completing state, and a real
completing chain would force one.  This file isolates that projection as a general lemma
(`reachWalk` / `no_zone_chain_of_reach_utc`) and discharges it for the pilot box
`b1 = (1, 1, 3, 4, 5, 5, 7)`'s first reach leaf (node 2) from explicit verdict literals.

**The term-by-term edge mapping (all proved, box-free):** a realized chain's window position
`R = Aex / (ρ a / ρ 0)` (readings normalized by the base row) satisfies, at each step
`⟨b, A, B⟩` from a state whose frontier sup `p` covers the position (`R ≤ p`):

* seam 1 (`ρ a / ρ b < Aex / A`) forces the reading `ρ b / ρ 0 · R` past the tooth entry
  `A` (`seam1_mul` / `seam1_reading`), and the envelope domination `ρ b / ρ 0 ≤ dfsHi n U b`
  then gives the graph's edge condition `A / dfsHi < p` (`seam1_entry_lt`);
* the terminal exit bound (`ρ b / ρ 0 < B / 7`) forces the new position past 7
  (`exitB_gt7`), and the domination `dfsLo n U b ≤ ρ b / ρ 0` gives `7 < B / dfsLo`;
* seam 1 + the exit bound + the coverage give the completing inequality
  `7 · A < p · B` (`comp_ineq_lt`): `7A < 7·(reading) < B·R ≤ B·p`;
* a self-step (`s.b = a`) contradicts the zone forms: the seams read `A < Aex < B` with
  `A = 8j−1`, `B = 8j+1`, `Aex = 8m+1`, forcing `j ≤ m < j` (`selfStep_no`);
* a step to the base row (`s.b = 0`) with the zone form (`A = 8j−1 ≥ 7`) forces the
  position past 7 mid-window (`row0_gt7`), contradicting the verdict's 7-bound.

**Two findings banked here (both machine-checked):**

1. **The strict push condition `p < x` is not implied by a real step.**  The artifact's
   `reach_utc` pushes `(x, b)` only when the tooth straddles the frontier sup
   (`e < p < x`); a real chain's step gives only `e < p` (the frontier sup can overshoot
   the true position, putting the exit-sup `x = B / lo'_b` of the next tooth below `p`).
   The projection therefore consumes the RELAXED edge (`e < p` alone): `reachWalk`'s
   verdict record banks the relaxed closure.  For the pilot leaf the dumped strict
   explored set (3 states) is NOT relaxed-closed; the relaxed closure is the 11-state set
   `S2` below (computed from the same banked node table by the relaxed semantics; still
   completing-free).
2. **`DfsPruneDom`'s unrestricted form is FALSE at the pilot leaf** (`unrestricted_false`):
   the state graph only models envelope comb teeth, while a realized continuation may use
   non-teeth zone edges.  Concretely `ρ = ![1, 11/10, 3, 9/2, 547/100, 549/100, 701/100]`
   realizes `tbl2` exactly (all 42 bounds) and realizes the one-step continuation
   `⟨row 1, A = 2, B = 8⟩` with the exit bound `ρ 1 / ρ 0 < 8/7` — while the verdict
   `no_completing_state_reachable` is true.  The prune is sound against ZONE-FORM chains
   (`ZoneTooth`: `A = 8j−1, B = 8j+1, j ≥ 1`) — exactly the form `DfsSoft`'s `dfsZone`
   conjunct carries for the E810 covering chains (`zone_of_dfsSoftAdm`).  Consequently the
   per-leaf condition consumed by `dfsWalk` must be the zone-form `DfsPruneDomZone`; this
   file provides the adjusted walk (`dfsWalkZone`) and the forest composition
   (`m4CertSound_of_forest_zone`), drop-in for `dfsWalk` / `m4CertSound_of_forest` with
   the prune-dom hypothesis strengthened — the soft-admissible chains carry the zone form
   they already have (`zone_of_dfsSoftAdm`).

All arithmetic exact; every theorem carries `#print axioms`; accepted profile is the
standard three (`propext`, `Classical.choice`, `Quot.sound`) — `sorryAx` is failure.
-/

namespace Fresh.M4Cert

open Fresh FilterAssembly UClosure Fresh.MechDataBatch

/-! ## 0. General ordered-field helpers (ℝ) -/

/-- Multiplying by a positive on the right converts between an inequality and its
multiplied form (division present). -/
theorem lt_mul_div {X Y Z W : ℝ} (hX : 0 < X) (hZ : 0 < Z) :
    W < Y * (Z / X) ↔ W * X < Y * Z := by
  constructor
  · intro h
    have h1 : W * X < (Y * (Z / X)) * X := mul_lt_mul_of_pos_right h hX
    rw [mul_assoc, div_mul_cancel₀ Z (ne_of_gt hX)] at h1
    exact h1
  · intro h
    refine lt_of_mul_lt_mul_right ?_ hX.le
    calc W * X < Y * Z := h
      _ = Y * (Z / X * X) := by rw [div_mul_cancel₀ Z (ne_of_gt hX)]
      _ = (Y * (Z / X)) * X := by ring

#print axioms lt_mul_div

/-- Cancelling a positive divisor accumulated across a product. -/
theorem div_mul_mul_cancel {X Y Z : ℝ} (hY : 0 < Y) : (X / Y) * Z * Y = X * Z := by
  rw [mul_right_comm (X / Y) Z Y, div_mul_cancel₀ X (ne_of_gt hY)]

#print axioms div_mul_mul_cancel

/-- Dividing by the same positive denominators: `X / Z ≤ X / Y ↔ Y ≤ Z`. -/
theorem le_div_div {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    X / Z ≤ X / Y ↔ Y ≤ Z := by
  rw [div_le_iff₀ hZ, div_mul_eq_mul_div, le_div_iff₀ hY]
  exact mul_le_mul_iff_right₀ hX

#print axioms le_div_div

/-- Dividing by larger positive denominators shrinks: `Y ≤ Z → X / Z ≤ X / Y`. -/
theorem div_le_div_of_pos {X Y Z : ℝ} (hX : 0 < X) (hYZ : Y ≤ Z) (hY : 0 < Y) (hZ : 0 < Z) :
    X / Z ≤ X / Y := (le_div_div hX hY hZ).mpr hYZ

#print axioms div_le_div_of_pos

/-! ## 1. General position arithmetic (no box data) -/

/-- The comb-tooth zone form of a step's edges (`A = 8j−1`, `B = 8j+1`, `j ≥ 1`) — the
`∃`-part of `dfsZone`, table-independent. -/
-- STANDING: DEFINITION
def ZoneTooth (A B : ℚ) : Prop :=
  ∃ j : ℕ, 1 ≤ j ∧ A = ((8 * j - 1 : ℕ) : ℚ) ∧ B = ((8 * j + 1 : ℕ) : ℚ)

/-- The zone-exit form of an exit numerator (`Aex = 8m+1`) — the form every tree node's
`Aex` carries (start tooth / step exit). -/
-- STANDING: DEFINITION
def IsZoneExit (Aex : ℚ) : Prop := ∃ m : ℕ, Aex = ((8 * m + 1 : ℕ) : ℚ)

/-- The window position of a state `(exit numerator Aex, last reading row a)` under the
readings `ρ` (base-row-normalized). -/
-- STANDING: DEFINITION
noncomputable def WinPos (ρ : Fin 7 → ℝ) (a : Fin 7) (Aex : ℚ) : ℝ := (Aex : ℝ) / (ρ a / ρ 0)

/-- The two seams of a realized self-step (`s.b = a`) contradict the zone forms: they read
`A < Aex < B` with `A = 8j−1`, `B = 8j+1`, `Aex = 8m+1`, forcing `j ≤ m < j`. -/
theorem selfStep_no {ρ : Fin 7 → ℝ} (hpos : ∀ k, 0 < ρ k) {a : Fin 7} {Aex A B : ℚ}
    (hA : 0 < A) (hAex : 0 < Aex)
    (htooth : ZoneTooth A B) (hAexE : IsZoneExit Aex)
    (sat1 : BHolds true (ρ a / ρ a) (Aex / A))
    (sat2 : BHolds true (ρ a / ρ a) (B / Aex)) : False := by
  have s1 : BHolds true (ρ a / ρ a) (Aex / A) := sat1
  have s2 : BHolds true (ρ a / ρ a) (B / Aex) := sat2
  simp only [BHolds, Rat.cast_div] at s1 s2
  rw [div_self (ne_of_gt (hpos a))] at s1 s2
  have k1 : (A : ℚ) < Aex := by
    rw [one_lt_div (Rat.cast_pos.mpr hA)] at s1
    exact Rat.cast_lt.mp s1
  have k2 : Aex < B := by
    rw [one_lt_div (Rat.cast_pos.mpr hAex)] at s2
    exact Rat.cast_lt.mp s2
  obtain ⟨m, hm⟩ := hAexE
  obtain ⟨j, hj1, hAeq, hBeq⟩ := htooth
  rw [hAeq, hm] at k1
  rw [hm, hBeq] at k2
  have z1 : ((8 * j - 1 : ℕ) : ℤ) < ((8 * m + 1 : ℕ) : ℤ) := by exact_mod_cast k1
  have z2 : ((8 * m + 1 : ℕ) : ℤ) < ((8 * j + 1 : ℕ) : ℤ) := by exact_mod_cast k2
  omega

#print axioms selfStep_no

/-- The terminal exit bound places the window position past 7. -/
theorem exitB_gt7 {ρ : Fin 7 → ℝ} (hpos : ∀ k, 0 < ρ k) {a : Fin 7} {Aex : ℚ}
    (h : BHolds true (ρ a / ρ 0) (Aex / 7)) : (7 : ℝ) < WinPos ρ a Aex := by
  simp only [BHolds, Rat.cast_div, Rat.cast_ofNat] at h
  have h0 : 0 < (ρ a / ρ 0 : ℝ) := div_pos (hpos a) (hpos 0)
  have hAexPos : (0 : ℝ) < (Aex : ℝ) := by linarith
  have h2 : (7 : ℝ) * (ρ a / ρ 0 : ℝ) < (Aex : ℝ) := by
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 7)] at h
    linear_combination h
  show (7 : ℝ) < (Aex : ℝ) / (ρ a / ρ 0)
  rw [lt_div_iff₀ h0]
  exact h2

#print axioms exitB_gt7

/-- A realized step to the base row (`b = 0`) whose tooth entry is at least 7 (the zone
form's `j ≥ 1` gives `A = 8j−1 ≥ 7`) forces the window position past 7 — the base row has
no envelope teeth, so such a step is a mid-window 7-crossing. -/
theorem row0_gt7 {ρ : Fin 7 → ℝ} (hpos : ∀ k, 0 < ρ k) {a : Fin 7} {Aex A : ℚ}
    (hAex : 0 < Aex) (hA7 : (7 : ℚ) ≤ A)
    (sat1 : BHolds true (ρ a / ρ 0) (Aex / A)) : (7 : ℝ) < WinPos ρ a Aex := by
  simp only [BHolds, Rat.cast_div] at sat1
  have h0 : 0 < (ρ a / ρ 0 : ℝ) := div_pos (hpos a) (hpos 0)
  have hA' : (0 : ℝ) < (A : ℝ) :=
    Rat.cast_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 7) hA7)
  have hle : (Aex : ℝ) / (A : ℝ) ≤ (Aex : ℝ) / 7 :=
    (le_div_div (X := (Aex : ℝ)) (Y := 7) (Z := (A : ℝ)) (Rat.cast_pos.mpr hAex)
      (by norm_num) hA').mpr (by exact_mod_cast hA7)
  have hlt : (ρ a / ρ 0 : ℝ) < (Aex : ℝ) / 7 := lt_of_lt_of_le sat1 hle
  show (7 : ℝ) < (Aex : ℝ) / (ρ a / ρ 0)
  rw [lt_div_iff₀ h0]
  rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 7)] at hlt
  linear_combination hlt

#print axioms row0_gt7

/-- **Seam 1, multiplied out:** the step's upper seam says
`(ρ a / ρ 0) · A < Aex · (ρ b / ρ 0)` — the reading `(ρ b / ρ 0) · R` sits past the tooth
entry `A`. -/
theorem seam1_mul {ρ : Fin 7 → ℝ} (hpos : ∀ k, 0 < ρ k)
    {a b : Fin 7} {Aex A : ℚ} (hA : 0 < A)
    (sat1 : BHolds true (ρ a / ρ b) (Aex / A)) :
    (ρ a / ρ 0 : ℝ) * (A : ℝ) < (Aex : ℝ) * (ρ b / ρ 0 : ℝ) := by
  have hsat : (ρ a / ρ b : ℝ) < ((Aex / A : ℚ) : ℝ) := sat1
  simp only [Rat.cast_div] at hsat
  have h := mul_lt_mul_of_pos_right hsat (mul_pos (hpos b) (Rat.cast_pos.mpr hA))
  have e1 : (ρ a / ρ b : ℝ) * (ρ b * (A : ℝ)) = (ρ a : ℝ) * (A : ℝ) := by
    rw [← mul_assoc, div_mul_cancel₀ (ρ a : ℝ) (ne_of_gt (hpos b))]
  have e2 : ((Aex : ℝ) / (A : ℝ)) * (ρ b * (A : ℝ)) = (Aex : ℝ) * (ρ b : ℝ) := by
    rw [mul_comm (ρ b : ℝ) (A : ℝ), ← mul_assoc,
      div_mul_cancel₀ (Aex : ℝ) (ne_of_gt (Rat.cast_pos.mpr hA))]
  rw [e1, e2] at h
  -- h : (ρ a) * A < Aex * (ρ b)   (over ℝ)
  rw [div_mul_eq_mul_div, div_lt_iff₀ (hpos 0), mul_comm (Aex : ℝ) (ρ b / ρ 0 : ℝ),
    div_mul_mul_cancel (hpos 0)]
  linear_combination h

#print axioms seam1_mul

/-- **The reading-past-the-entry form:** seam 1 says `A < (ρ b / ρ 0) · R` where
`R = WinPos ρ a Aex` is the window position. -/
theorem seam1_reading {ρ : Fin 7 → ℝ} (hpos : ∀ k, 0 < ρ k)
    {a b : Fin 7} {Aex A : ℚ} (hAex : 0 < Aex) (hA : 0 < A)
    (sat1 : BHolds true (ρ a / ρ b) (Aex / A)) :
    (A : ℝ) < (ρ b / ρ 0 : ℝ) * WinPos ρ a Aex := by
  have hX : 0 < (ρ a / ρ 0 : ℝ) := div_pos (hpos a) (hpos 0)
  have h1 := seam1_mul hpos hA sat1
  simp only [WinPos]
  rw [lt_mul_div hX (Rat.cast_pos.mpr hAex)]
  linear_combination h1

#print axioms seam1_reading

/-- **The entry-side edge mapping (seam 1 ⟹ the graph's entry condition).**  With the
envelope domination `ρ b / ρ 0 ≤ hi` and the frontier-sup coverage `R ≤ p`, the state
graph's edge condition `A / hi < p` holds. -/
theorem seam1_entry_lt {ρ : Fin 7 → ℝ} {hi p : ℚ} (hpos : ∀ k, 0 < ρ k)
    {a b : Fin 7} {Aex A : ℚ} (hAex : 0 < Aex) (hA : 0 < A)
    (sat1 : BHolds true (ρ a / ρ b) (Aex / A))
    (hbhi : (ρ b / ρ 0 : ℝ) ≤ (hi : ℝ)) (hhipos : 0 < (hi : ℝ))
    (hRle : WinPos ρ a Aex ≤ (p : ℝ)) :
    ((A : ℝ) / (hi : ℝ)) < (p : ℝ) := by
  have hread := seam1_reading hpos hAex hA sat1
  have hRpos : 0 < WinPos ρ a Aex := div_pos (Rat.cast_pos.mpr hAex)
    (div_pos (hpos a) (hpos 0))
  have hfin : (A : ℝ) < (hi : ℝ) * (p : ℝ) := by
    calc (A : ℝ) < (ρ b / ρ 0 : ℝ) * WinPos ρ a Aex := hread
      _ ≤ (hi : ℝ) * WinPos ρ a Aex := mul_le_mul_of_nonneg_right hbhi hRpos.le
      _ ≤ (hi : ℝ) * (p : ℝ) := mul_le_mul_of_nonneg_left hRle hhipos.le
  rw [div_lt_iff₀ hhipos, mul_comm (p : ℝ) (hi : ℝ)]
  exact hfin

#print axioms seam1_entry_lt

/-- **The completing-side mapping (seam 1 + the exit bound ⟹ `7·A < p·B`).**  The
completing transition's inequality `7 · A < p · B` follows from the step's seam 1 (the
reading past the entry `A`), the exit bound past the step (`7 · ρ b / ρ 0 < B`: the new
position past 7), and the frontier-sup coverage `R ≤ p`. -/
theorem comp_ineq_lt {ρ : Fin 7 → ℝ} {p : ℚ} (hpos : ∀ k, 0 < ρ k)
    {a b : Fin 7} {Aex A B : ℚ} (hAex : 0 < Aex) (hA : 0 < A) (hB : 0 < B)
    (sat1 : BHolds true (ρ a / ρ b) (Aex / A))
    (h7 : (7 : ℝ) * (ρ b / ρ 0 : ℝ) < (B : ℝ))
    (hRle : WinPos ρ a Aex ≤ (p : ℝ)) :
    ((7 : ℝ) * (A : ℝ)) < ((p : ℝ) * (B : ℝ)) := by
  have hread := seam1_reading hpos hAex hA sat1
  have hRpos : 0 < WinPos ρ a Aex := div_pos (Rat.cast_pos.mpr hAex)
    (div_pos (hpos a) (hpos 0))
  calc (7 : ℝ) * (A : ℝ) < (7 : ℝ) * ((ρ b / ρ 0 : ℝ) * WinPos ρ a Aex) :=
        mul_lt_mul_of_pos_left hread (by norm_num)
    _ = ((7 : ℝ) * (ρ b / ρ 0 : ℝ)) * WinPos ρ a Aex := by ring
    _ < (B : ℝ) * WinPos ρ a Aex := mul_lt_mul_of_pos_right h7 hRpos
    _ ≤ (p : ℝ) * (B : ℝ) := by
        rw [mul_comm (p : ℝ) (B : ℝ)]
        exact mul_le_mul_of_nonneg_left hRle (le_of_lt (Rat.cast_pos.mpr hB))

#print axioms comp_ineq_lt

/-! ## 2. The relaxed state-graph verdict (the datum the projection consumes) -/

/-- One relaxed state-graph edge: from state `(p, a)` the tooth `(A, B)` of row `b ≠ a`
(with `j ≥ 1`) whose entry sits below the frontier sup (`A / dfsHi < p`).  NOTE: the
artifact's `reach_utc` additionally requires the straddle `p < x` for PUSHING `(x, b)`;
a real chain's step does not imply that half (finding 1 of the header), so the projection
consumes the relaxed closure. -/
-- STANDING: DEFINITION
def RtEdge (n : Fin 7 → ℤ) (U : UTable) (p : ℚ) (a b : Fin 7) (A B : ℚ) : Prop :=
  ZoneTooth A B ∧ b ≠ a ∧ 0 < b.val ∧ (((A : ℝ) / (dfsHi n U b : ℝ)) < (p : ℝ))

/-- One completing transition: the edge condition plus the exit-sup past 7 plus the
completing inequality `7·A < p·B` (verbatim `reach_utc`). -/
-- STANDING: DEFINITION
def RtComp (n : Fin 7 → ℤ) (U : UTable) (p : ℚ) (a b : Fin 7) (A B : ℚ) : Prop :=
  RtEdge n U p a b A B ∧ (7 : ℚ) < B / dfsLo n U b ∧ (7 : ℚ) * A < p * B

/-- The reach_utc verdict at a leaf state `(U, a, Aex, P)`, relaxed-closure form: an
explicit finite explored state list, containing the start state, closed under the relaxed
edges, with every explored frontier sup ≤ 7 (equivalently, given closure: completing-free
— see `no_comp_of_bounded`). -/
-- STANDING: DEFINITION
structure ReachUtcVerdict (n : Fin 7 → ℤ) (U : UTable) (P : ℚ) (a : Fin 7) : Type where
  /-- the explored `(frontier-sup, reading row)` state set -/
  S : List (ℚ × Fin 7)
  /-- the exploration starts at the leaf's own state -/
  hstart : (P, a) ∈ S
  /-- every explored frontier sup stays within the window -/
  hp7 : ∀ q : ℚ, ∀ a' : Fin 7, (q, a') ∈ S → (q : ℝ) ≤ 7
  /-- relaxed closure: every tooth edge from an explored state has its exit-sup state explored -/
  hclose : ∀ q : ℚ, ∀ a' : Fin 7, (q, a') ∈ S → ∀ b : Fin 7, 0 < b.val → b ≠ a' →
    ∀ j : ℕ, 1 ≤ j →
      ((((8 * j - 1 : ℕ) : ℚ) / dfsHi n U b : ℝ) < (q : ℝ)) →
      ((((8 * j + 1 : ℕ) : ℚ) / dfsLo n U b, b) ∈ S)

/-- `dfsLo` is positive on every non-base row (its max contains the constant `1`). -/
theorem dfsLo_pos (n : Fin 7 → ℤ) (U : UTable) (b : Fin 7) (hb : 0 < b.val) :
    0 < dfsLo n U b := by
  unfold dfsLo
  rw [if_pos hb]
  cases hb2 : U 0 b with
  | none =>
      exact lt_of_lt_of_le (show (0 : ℚ) < 1 by norm_num) (le_max_right _ _)
  | some c =>
      refine lt_of_lt_of_le (show (0 : ℚ) < 1 by norm_num) ?_
      exact le_trans (le_max_right _ _) (le_max_left _ _)

#print axioms dfsLo_pos

/-- Given the relaxed closure, the verdict's 7-bound makes every state completing-free —
a completing transition's tooth has entry below the state's sup, so its exit-sup state
would be explored and exceed 7. -/
theorem no_comp_of_bounded (n : Fin 7 → ℤ) (U : UTable) (P : ℚ) (a : Fin 7)
    (v : ReachUtcVerdict n U P a) :
    ∀ q : ℚ, ∀ a' : Fin 7, (q, a') ∈ v.S → ∀ b : Fin 7, ∀ A B : ℚ, ¬ RtComp n U q a' b A B := by
  intro q a' hmem b A B hc
  obtain ⟨he, hx7, -⟩ := hc
  obtain ⟨htooth, hba, hbpos, helt⟩ := he
  obtain ⟨j, hj1, hAeq, hBeq⟩ := htooth
  rw [hAeq] at helt
  have hx := v.hclose q a' hmem b hbpos hba j hj1 helt
  have hleq : ((8 * j + 1 : ℕ) : ℚ) / dfsLo n U b ≤ (7 : ℚ) :=
    Rat.cast_le.mp (v.hp7 (((8 * j + 1 : ℕ) : ℚ) / dfsLo n U b) b hx)
  rw [hBeq] at hx7
  exact absurd hx7 (not_lt.2 hleq)

#print axioms no_comp_of_bounded

/-! ## 3. The projection (the engine: the `dfsWalk`-shaped induction over the chain) -/

/-- **The state-graph projection (box-free engine).**  A zone-form realized chain from a
leaf state covered by a relaxed-closed, 7-bounded explored set cannot exist: the chain's
every prefix keeps a covered explored state (`R ≤ p`, same row), each step's edge condition
holds (`seam1_entry_lt`), the closure follows the chain through the state graph, and the
terminal exit bound pushes a state's position past 7 against the 7-bound. -/
theorem reachWalk (n : Fin 7 → ℤ) (U : UTable) (P : ℚ) (a : Fin 7)
    (v : ReachUtcVerdict n U P a)
    (ρ : Fin 7 → ℝ) (hpos : ∀ k, 0 < ρ k)
    (hdomHi : ∀ b : Fin 7, 0 < b.val → (ρ b / ρ 0 : ℝ) ≤ (dfsHi n U b : ℝ))
    (hdomLo : ∀ b : Fin 7, 0 < b.val → (dfsLo n U b : ℝ) ≤ (ρ b / ρ 0 : ℝ))
    (hhiPos : ∀ b : Fin 7, 0 < b.val → 0 < (dfsHi n U b : ℝ)) :
    ∀ steps : List Step, (∀ s ∈ steps, ZoneTooth s.A s.B) →
      ∀ (U' : UTable) (a' : Fin 7) (Aex' p : ℚ), 0 < a'.val → 0 < Aex' → IsZoneExit Aex' →
        ((Aex' : ℝ) / (dfsLo n U a' : ℝ) ≤ (p : ℝ)) → (p, a') ∈ v.S →
        ¬ ChainRealized ρ U' a' Aex' steps := by
  intro steps
  induction steps with
  | nil =>
    intro _ U' a' Aex' p haval hAexPos _ hPcov hmem hchain
    have h7 : (7 : ℝ) < WinPos ρ a' Aex' := exitB_gt7 hpos hchain
    have hRle : WinPos ρ a' Aex' ≤ (Aex' : ℝ) / ((dfsLo n U a' : ℚ) : ℝ) :=
      div_le_div_of_pos (Rat.cast_pos.mpr hAexPos) (hdomLo a' haval)
        (Rat.cast_pos.mpr (dfsLo_pos n U a' haval)) (div_pos (hpos a') (hpos 0))
    have hp7 := v.hp7 p a' hmem
    linarith
  | cons s rest ih =>
    intro hzone U' a' Aex' p haval hAexPos hAexE hPcov hmem hchain
    simp only [ChainRealized] at hchain
    obtain ⟨V, hV, hAp, hBp, sat1, sat2, hrest⟩ := hchain
    obtain ⟨j, hj1, hAeq, hBeq⟩ := hzone s (by simp)
    have hRle : WinPos ρ a' Aex' ≤ (p : ℝ) :=
      le_trans (div_le_div_of_pos (Rat.cast_pos.mpr hAexPos) (hdomLo a' haval)
        (Rat.cast_pos.mpr (dfsLo_pos n U a' haval)) (div_pos (hpos a') (hpos 0))) hPcov
    have hp7 := v.hp7 p a' hmem
    by_cases hb0 : s.b = 0
    · -- step to the base row: the zone form's A ≥ 7 forces the position past 7 mid-window
      have sat1' : BHolds true (ρ a' / ρ 0) (Aex' / s.A) := by
        rw [hb0] at sat1; exact sat1
      have hA7 : (7 : ℚ) ≤ s.A := by
        rw [hAeq]
        have hj7 : (7 : ℕ) ≤ 8 * j - 1 := by omega
        exact_mod_cast hj7
      have h7 : (7 : ℝ) < WinPos ρ a' Aex' := row0_gt7 hpos hAexPos hA7 sat1'
      linarith
    · have hsbpos : 0 < s.b.val := by
        by_contra hcon
        exact hb0 (Fin.ext (by omega))
      by_cases hba : s.b = a'
      · -- self-step: the two seams contradict the zone forms
        have sat1' : BHolds true (ρ a' / ρ a') (Aex' / s.A) := by
          rw [hba] at sat1; exact sat1
        have sat2' : BHolds true (ρ a' / ρ a') (s.B / Aex') := by
          rw [hba] at sat2; exact sat2
        exact selfStep_no hpos hAp hAexPos ⟨j, hj1, hAeq, hBeq⟩ hAexE sat1' sat2'
      · -- the projection step: the real edge is a graph edge; the closure follows the chain
        have helt : ((((8 * j - 1 : ℕ) : ℚ) : ℝ) / (dfsHi n U s.b : ℝ)) < (p : ℝ) := by
          rw [← hAeq]
          exact seam1_entry_lt hpos hAexPos hAp sat1 (hdomHi s.b hsbpos)
            (hhiPos s.b hsbpos) hRle
        have hmemb : ((((8 * j + 1 : ℕ) : ℚ) / dfsLo n U s.b), s.b) ∈ v.S :=
          v.hclose p a' hmem s.b hsbpos hba j hj1 helt
        have hPcov' : ((s.B : ℝ) / (dfsLo n U s.b : ℝ)) ≤
            ((((8 * j + 1 : ℕ) : ℚ) / dfsLo n U s.b : ℚ) : ℝ) := by
          rw [hBeq, Rat.cast_div]
        have hzone' : ∀ t ∈ rest, ZoneTooth t.A t.B :=
          fun t ht => hzone t (by simp only [List.mem_cons]; exact Or.inr ht)
        have hBpos : 0 < s.B := hBp
        have hBzone : IsZoneExit s.B := ⟨j, hBeq⟩
        exact ih hzone' V s.b s.B
          (((8 * j + 1 : ℕ) : ℚ) / dfsLo n U s.b) hsbpos hBpos hBzone hPcov' hmemb hrest

#print axioms reachWalk

/-! ## 4. OWED (b)'s PROOF side (the general lemma) -/

/-- **OWED (b)'s PROOF side (the general lemma).**  If the relaxed `reach_utc` exploration
from a leaf's state `(frontier-sup P, reading row a)` over the leaf's envelope teeth has an
explicit finite explored set (start state included, relaxed-closed, every sup ≤ 7), and the
envelope dominates the readings (`dfsLo ≤ ρ b / ρ 0 ≤ dfsHi` for rows 1..6), then NO
zone-form `ChainRealized` continuation from the leaf's table/state exists.  The zone form
is exactly what the soft filters (`dfsZone`) carry for the E810 covering chains
(`zone_of_dfsSoftAdm`); the unrestricted form is FALSE (see `unrestricted_false`). -/
theorem no_zone_chain_of_reach_utc (n : Fin 7 → ℤ) (U : UTable) (a : Fin 7) (Aex P : ℚ)
    (v : ReachUtcVerdict n U P a)
    (ρ : Fin 7 → ℝ) (hpos : ∀ k, 0 < ρ k)
    (hfine : UFine ρ U)
    (hdomHi : ∀ b : Fin 7, 0 < b.val → (ρ b / ρ 0 : ℝ) ≤ (dfsHi n U b : ℝ))
    (hdomLo : ∀ b : Fin 7, 0 < b.val → (dfsLo n U b : ℝ) ≤ (ρ b / ρ 0 : ℝ))
    (hhiPos : ∀ b : Fin 7, 0 < b.val → 0 < (dfsHi n U b : ℝ))
    (ha0 : 0 < a.val) (hAex : IsZoneExit Aex)
    (hPcov : ((Aex : ℝ) / (dfsLo n U a : ℝ) ≤ (P : ℝ)))
    (steps : List Step) (hzone : ∀ s ∈ steps, ZoneTooth s.A s.B) :
    ¬ ChainRealized ρ U a Aex steps := by
  obtain ⟨m, hm⟩ := hAex
  have hAexPos : 0 < Aex := by
    rw [hm]
    positivity
  exact fun h => reachWalk n U P a v ρ hpos hdomHi hdomLo hhiPos steps hzone U a Aex P ha0
    hAexPos ⟨m, hm⟩ hPcov v.hstart h

#print axioms no_zone_chain_of_reach_utc
/-! ## 5. The E810-side bridge and the adjusted tree walk -/

/-- The soft filters' `dfsZone` conjunct carries exactly the zone form for the steps of a
REALIZED chain whose steps are soft-admissible along the induced path: the chain's own
`uStep` survivals thread the `DfsSoftAdm` recursion through the child states (without a
survival the recursion is vacuous past the failing step, so the chain hypothesis is
load-bearing). -/
theorem zone_of_dfsSoftAdm_realized (n : Fin 7 → ℤ) (ρ : Fin 7 → ℝ) :
    ∀ (steps : List Step) (st : DfsNode), DfsSoftAdm n st steps →
      ChainRealized ρ st.U st.a st.Aex steps →
        ∀ s ∈ steps, ZoneTooth s.A s.B := by
  intro steps
  induction steps with
  | nil => intro st _ _ s hs; exact absurd hs (by simp)
  | cons t rest ih =>
    intro st hadm hchain s hs
    simp only [DfsSoftAdm] at hadm
    obtain ⟨hsoft, hrec⟩ := hadm
    simp only [ChainRealized] at hchain
    obtain ⟨V, hV, -, -, -, -, hrest⟩ := hchain
    rcases List.mem_cons.1 hs with rfl | hmem
    · obtain ⟨hz, -, -⟩ := hsoft
      obtain ⟨j, hj, hA, hB, -⟩ := hz
      exact ⟨j, hj, hA, hB⟩
    · exact ih (childState n st t.b t.B V) (hrec V hV) hrest s hmem

#print axioms zone_of_dfsSoftAdm_realized

/-- The per-prune-leaf domination in the zone form the reach_utc verdict certifies (the
`DfsPruneDom` shape with `ZoneTooth` carried on the steps). -/
-- STANDING: DEFINITION
def DfsPruneDomZone (n : Fin 7 → ℤ) : DfsCert → Prop
  | .node _ ch => ∀ c ∈ ch, DfsPruneDomZone n c
  | .prune st =>
    ∀ (ρ : Fin 7 → ℝ), (∀ k, 0 < ρ k) → UFine ρ st.U →
      ∀ steps : List Step, (∀ s ∈ steps, ZoneTooth s.A s.B) →
        ¬ ChainRealized ρ st.U st.a st.Aex steps
  | .deadend _ => True

/-- **The adjusted tree-domination lemma** (`dfsWalk` with the zone-form prune-dom): a real
zone-form chain whose opening matches a closed, enumerating, prune-dominated tree root and
whose steps are soft-admissible along the induced path cannot exist.  The proof is
`dfsWalk`'s structure; the prune-leaf case applies the zone-form domination to the
remaining chain, whose steps are zone-form by soft-admissibility. -/
theorem dfsWalkZone (n : Fin 7 → ℤ) (steps : List Step) (hzone : ∀ s ∈ steps, ZoneTooth s.A s.B) :
    ∀ (T : DfsCert) (st : DfsNode), T.root = st → DfsClosed T → DfsEnum n T → DfsPruneDomZone n T →
      ∀ ρ : Fin 7 → ℝ, (∀ k, 0 < ρ k) → UFine ρ st.U →
        ChainRealized ρ st.U st.a st.Aex steps → DfsSoftAdm n st steps → False := by
  induction steps with
  | nil =>
    intro T st hroot hclosed _ _ ρ hpos hfine hchain _
    simp only [ChainRealized] at hchain
    have h1 : uExitOK st.U st.a st.Aex = true := uExitOK_of_fine hpos hfine hchain
    rcases T with ⟨m, ch⟩ | ⟨m⟩ | ⟨m⟩ <;>
      simp only [DfsCert.root, DfsClosed, DfsNodeOK] at hroot hclosed
    · obtain ⟨hOK, -⟩ := hclosed
      rw [hroot, h1] at hOK
      exact Bool.noConfusion hOK
    · rw [hroot, h1] at hclosed
      exact Bool.noConfusion hclosed
    · rw [hroot, h1] at hclosed
      exact Bool.noConfusion hclosed
  | cons s rest ih =>
    intro T st hroot hclosed henum hprune ρ hpos hfine hchain hadm
    simp only [ChainRealized] at hchain
    obtain ⟨V, hV, hA, hB, sat1, sat2, hrest⟩ := hchain
    simp only [DfsSoftAdm] at hadm
    obtain ⟨hsoft, hrec⟩ := hadm
    have hc1 : 0 < (st.Aex / s.A : ℚ) := bpos_of_holds (div_pos (hpos st.a) (hpos s.b)) sat1
    have hAex' : 0 < st.Aex := by
      have h1 : st.Aex = (st.Aex / s.A) * s.A := by field_simp
      rw [h1]
      exact mul_pos hc1 hA
    obtain ⟨V1, hadd1, hadd2⟩ := uStep_some_add hAex' hA hB hV
    have hf1 : UFine ρ V1 := uAdd_fine_some hpos hfine sat1 hadd1
    have hfV : UFine ρ V := uAdd_fine_some hpos hf1 sat2 hadd2
    have hseam : uStep st.U st.a s.b st.Aex s.A s.B ≠ none := by
      rw [hV]
      exact Option.some_ne_none V
    have hfilt : DfsFilters n st s.b s.A s.B := ⟨hsoft, hseam⟩
    have hzone' : ∀ t ∈ rest, ZoneTooth t.A t.B :=
      fun t ht => hzone t (by simp only [List.mem_cons]; exact Or.inr ht)
    rcases T with ⟨m, ch⟩ | ⟨m⟩ | ⟨m⟩ <;>
      simp only [DfsCert.root] at hroot <;> rw [hroot] at hclosed henum hprune
    · simp only [DfsClosed, DfsEnum, DfsPruneDomZone] at hclosed henum hprune
      obtain ⟨-, hch⟩ := hclosed
      obtain ⟨hcE, hcEch⟩ := henum
      obtain ⟨c, hcch, hM⟩ := hcE s.b s.A s.B hfilt
      simp only [DfsMatch] at hM
      obtain ⟨V', hV', hchild⟩ := hM
      have hVV : V = V' := Option.some.inj (hV.symm.trans hV')
      rw [← hVV] at hchild
      rcases c with ⟨m2, ch2⟩ | ⟨m2⟩ | ⟨m2⟩ <;> simp only [DfsCert.root] at hchild
      · exact ih hzone' (DfsCert.node m2 ch2) (childState n st s.b s.B V) hchild.symm
          (hch _ hcch) (hcEch _ hcch) (hprune _ hcch) ρ hpos hfV hrest (hrec V hV)
      · exact ih hzone' (DfsCert.prune m2) (childState n st s.b s.B V) hchild.symm
          (hch _ hcch) (hcEch _ hcch) (hprune _ hcch) ρ hpos hfV hrest (hrec V hV)
      · exact ih hzone' (DfsCert.deadend m2) (childState n st s.b s.B V) hchild.symm
          (hch _ hcch) (hcEch _ hcch) (hprune _ hcch) ρ hpos hfV hrest (hrec V hV)
    · simp only [DfsPruneDomZone] at hprune
      exact hprune ρ hpos hfine (s :: rest) hzone ⟨V, hV, hA, hB, sat1, sat2, hrest⟩
    · simp only [DfsEnum] at henum
      exact henum s.b s.A s.B hfilt

#print axioms dfsWalkZone

/-- The adjusted no-chain composition (drop-in for `noChain_of_forest`): the real chain's
zone form is extracted from the soft-admissibility hypothesis. -/
theorem noChain_of_forest_zone (n : Fin 7 → ℤ) (T : List DfsCert)
    (hclosed : ∀ t ∈ T, DfsClosed t) (henum : ∀ t ∈ T, DfsEnum n t)
    (hprune : ∀ t ∈ T, DfsPruneDomZone n t)
    (ρ : Fin 7 → ℝ) (U0 : UTable) (a0 : Fin 7) (Aex0 : ℚ) (steps : List Step)
    (hpos : ∀ k, 0 < ρ k) (_hfine : UFine ρ U0)
    (hchain : ChainRealized ρ U0 a0 Aex0 steps)
    (hadm : ∃ t ∈ T, t.root.a = a0 ∧ t.root.Aex = Aex0 ∧ UFine ρ t.root.U ∧
      DfsSoftAdm n t.root steps) : False := by
  obtain ⟨t, htm, ⟨ha, hAx, hfineR, hadmR⟩⟩ := hadm
  have hchain' : ChainRealized ρ t.root.U a0 Aex0 steps :=
    chainRealized_tableMono hpos steps U0 a0 Aex0 hchain t.root.U hfineR
  rw [← ha, ← hAx] at hchain'
  exact dfsWalkZone n steps
    (zone_of_dfsSoftAdm_realized n ρ steps t.root hadmR hchain') t t.root rfl
    (hclosed t htm) (henum t htm) (hprune t htm) ρ hpos hfineR hchain' hadmR

#print axioms noChain_of_forest_zone

/-- The adjusted DFS-soundness theorem (box form), drop-in for `m4CertSound_of_forest`
with the zone-form prune-dom hypothesis. -/
theorem m4CertSound_of_forest_zone (n : Fin 7 → ℤ) (T : List DfsCert)
    (hclosed : ∀ t ∈ T, DfsClosed t) (henum : ∀ t ∈ T, DfsEnum n t)
    (hprune : ∀ t ∈ T, DfsPruneDomZone n t) (hcadm : DfsRootAdm n T) : M4CertSound n :=
  fun ρ U0 a0 Aex0 steps hpos hfine0 hchain =>
    noChain_of_forest_zone n T hclosed henum hprune ρ U0 a0 Aex0 steps hpos hfine0 hchain
      (hcadm ρ U0 a0 Aex0 steps hpos hfine0 hchain)

#print axioms m4CertSound_of_forest_zone


set_option maxHeartbeats 8000000

open Fresh.M4CertRung2_1_1_3_4_5_5_7

/-! ## 6. The pilot instance: box b1 = (1, 1, 3, 4, 5, 5, 7), reach leaf node 2

The leaf's state (from the [T 32/32]-verified tree mirror `m4rung2_tree_1_1_3_4_5_5_7.jsonl`,
node 2, kind `reach`, depth 3): `(U, a, Aex, P) = (tbl2, row 3, 9, 18/7)`.  The banked
per-leaf verdict `reachutc_1_1_3_4_5_5_7.json` records `no_completing_state_reachable`
with the STRICT explored set `[(18/7, rank 4), (18/5, rank 3), (1377/343, rank 4)]`
(dump ranks = row + 1).  The projection consumes the RELAXED closure of the same state
graph over the same banked node table — the 11-state set `S2` below (finding 1: the strict
set is not relaxed-closed; the relaxed closure is still completing-free, by
`no_comp_of_bounded` given closure and the 7-bounds below). -/

/-- The envelope dominations at `tbl2`, per row from `UFine` plus the table's entry lemmas:
`dfsHi` is the (b, 0) entry and `dfsLo` is `1 / (0, b)` at every row of this leaf. -/
theorem domHi2 (ρ : Fin 7 → ℝ) (hpos : ∀ k, 0 < ρ k) (hfine : UFine ρ tbl2) :
    ∀ b : Fin 7, 0 < b.val → (ρ b / ρ 0 : ℝ) ≤ (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 b : ℝ) := by
  intro b hb
  have h2 := hfine b 0
  rcases hn : b.val with _ | _ | _ | _ | _ | _ | _
  · simp [hn] at hb
  · have hbe : b = (1 : Fin 7) := Fin.ext (by omega); subst hbe
    have h3 := bhof_eq_some h2 tbl2_c_1_0
    simp only [BHolds] at h3
    rw [show dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 1 = (3 / 2 : ℚ) from
      by norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_1_0]]
    exact h3
  · have hbe : b = (2 : Fin 7) := Fin.ext (by omega); subst hbe
    have h3 := bhof_eq_some h2 tbl2_c_2_0
    simp only [BHolds] at h3
    rw [show dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 2 = (7 / 2 : ℚ) from
      by norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_2_0]]
    exact h3
  · have hbe : b = (3 : Fin 7) := Fin.ext (by omega); subst hbe
    have h3 := bhof_eq_some h2 tbl2_c_3_0
    simp only [BHolds] at h3
    rw [show dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 3 = (9 / 2 : ℚ) from
      by norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_3_0]]
    exact h3
  · have hbe : b = (4 : Fin 7) := Fin.ext (by omega); subst hbe
    have h3 := bhof_eq_some h2 tbl2_c_4_0
    simp only [BHolds] at h3
    rw [show dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 4 = (11 / 2 : ℚ) from
      by norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_4_0]]
    exact le_of_lt h3
  · have hbe : b = (5 : Fin 7) := Fin.ext (by omega); subst hbe
    have h3 := bhof_eq_some h2 tbl2_c_5_0
    simp only [BHolds] at h3
    rw [show dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 5 = (11 / 2 : ℚ) from
      by norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_5_0]]
    exact h3
  · have hbe : b = (6 : Fin 7) := Fin.ext (by omega); subst hbe
    have h3 := bhof_eq_some h2 tbl2_c_6_0
    simp only [BHolds] at h3
    rw [show dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 6 = (99 / 14 : ℚ) from
      by norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_6_0]]
    exact le_of_lt h3

#print axioms domHi2

theorem domLo2 (ρ : Fin 7 → ℝ) (hpos : ∀ k, 0 < ρ k) (hfine : UFine ρ tbl2) :
    ∀ b : Fin 7, 0 < b.val → (dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 b : ℝ) ≤ (ρ b / ρ 0 : ℝ) := by
  intro b hb
  have h2 := hfine 0 b
  have hp01 : 0 < (ρ 0 / ρ b : ℝ) := div_pos (hpos 0) (hpos b)
  have hinv : (ρ b / ρ 0 : ℝ) = 1 / (ρ 0 / ρ b : ℝ) := by
    field_simp
  rcases hn : b.val with _ | _ | _ | _ | _ | _ | _
  · simp [hn] at hb
  · have hbe : b = (1 : Fin 7) := Fin.ext (by omega); subst hbe
    have h3 := bhof_eq_some h2 tbl2_c_0_1
    simp only [BHolds, Rat.cast_div, Rat.cast_ofNat] at h3
    have hhe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) = (1 : ℚ) := by
      norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_1]
    norm_num at h3
    rw [hhe, hinv, le_div_iff₀ hp01]
    norm_num
    linarith

  · have hbe : b = (2 : Fin 7) := Fin.ext (by omega); subst hbe
    have h3 := bhof_eq_some h2 tbl2_c_0_2
    simp only [BHolds, Rat.cast_div] at h3
    rw [show dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 2 = (5 / 2 : ℚ) from
      by norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_2], hinv, le_div_iff₀ hp01]
    have hc : ((5 / 2 : ℚ) : ℝ) * ((2 / 5 : ℚ) : ℝ) = 1 := by norm_num
    linarith [h3, hc]
  · have hbe : b = (3 : Fin 7) := Fin.ext (by omega); subst hbe
    have h3 := bhof_eq_some h2 tbl2_c_0_3
    simp only [BHolds, Rat.cast_div] at h3
    rw [show dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 3 = (343 / 81 : ℚ) from
      by norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_3], hinv, le_div_iff₀ hp01]
    have hc : ((343 / 81 : ℚ) : ℝ) * ((81 / 343 : ℚ) : ℝ) = 1 := by norm_num
    linarith [h3, hc]
  · have hbe : b = (4 : Fin 7) := Fin.ext (by omega); subst hbe
    have h3 := bhof_eq_some h2 tbl2_c_0_4
    simp only [BHolds, Rat.cast_div] at h3
    rw [show dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 4 = (49 / 9 : ℚ) from
      by norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_4], hinv, le_div_iff₀ hp01]
    have hc : ((49 / 9 : ℚ) : ℝ) * ((9 / 49 : ℚ) : ℝ) = 1 := by norm_num
    linarith [h3, hc]
  · have hbe : b = (5 : Fin 7) := Fin.ext (by omega); subst hbe
    have h3 := bhof_eq_some h2 tbl2_c_0_5
    simp only [BHolds, Rat.cast_div] at h3
    rw [show dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 5 = (49 / 9 : ℚ) from
      by norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_5], hinv, le_div_iff₀ hp01]
    have hc : ((49 / 9 : ℚ) : ℝ) * ((9 / 49 : ℚ) : ℝ) = 1 := by norm_num
    linarith [h3, hc]
  · have hbe : b = (6 : Fin 7) := Fin.ext (by omega); subst hbe
    have h3 := bhof_eq_some h2 tbl2_c_0_6
    simp only [BHolds, Rat.cast_div] at h3
    rw [show dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 6 = (7 : ℚ) from
      by norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_6], hinv, le_div_iff₀ hp01]
    have hc : ((7 : ℚ) : ℝ) * ((1 / 7 : ℚ) : ℝ) = 1 := by norm_num
    linarith [h3, hc]

#print axioms domLo2

/-- The ℚ-side bridge from the state-graph entry condition to the tooth bound. -/
theorem entry_lt_q {hi q : ℚ} {j : ℕ} (hhipos : 0 < (hi : ℝ))
    (he : (((8 * j - 1 : ℕ) : ℚ) : ℝ) / (hi : ℝ) < (q : ℝ)) :
    ((8 * j - 1 : ℕ) : ℚ) < q * hi := by
  rw [div_lt_iff₀ hhipos] at he
  refine Rat.cast_lt (K := ℝ).mp ?_
  rw [Rat.cast_mul]
  exact he

#print axioms entry_lt_q

/-- The relaxed `reach_utc` closure of leaf node 2's state `(18/7, row 3)` over `tbl2`'s
envelope teeth: 11 states, every frontier sup ≤ 7. -/
def S2 : List (ℚ × Fin 7) :=
  [((18 / 5 : ℚ), (2 : Fin 7)), ((729 / 343 : ℚ), (3 : Fin 7)), ((18 / 7 : ℚ), (3 : Fin 7)), ((1377 / 343 : ℚ), (3 : Fin 7)), ((81 / 49 : ℚ), (4 : Fin 7)), ((153 / 49 : ℚ), (4 : Fin 7)), ((81 / 49 : ℚ), (5 : Fin 7)), ((153 / 49 : ℚ), (5 : Fin 7)), ((9 / 7 : ℚ), (6 : Fin 7)), ((17 / 7 : ℚ), (6 : Fin 7)), ((25 / 7 : ℚ), (6 : Fin 7))]

/-- The relaxed-closure verdict for leaf node 2 (a `def`: the verdict record is data-carrying). -/
def verdict2 : ReachUtcVerdict (boxN m4res_1_1_3_4_5_5_7) tbl2 (18 / 7 : ℚ) (3 : Fin 7) where
  S := S2
  hstart := by simp [S2]
  hp7 := by
    intro q a' hq
    simp only [S2, List.mem_cons, Prod.mk.injEq] at hq
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hq
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · exact absurd hq (by simp)
  hclose := by
    intro q a' hq b hbpos hba j hj1 he
    simp only [S2, List.mem_cons, Prod.mk.injEq] at hq
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hq
    · -- state 18 / 5, row 2
      rcases hb0 : b.val with _ | _ | _ | _ | _ | _ | _
      · simp [hb0] at hbpos
      · have hbe : b = (1 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) = (3 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_1_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) = (1 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_1]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 1 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 1 := by exact_mod_cast hjb
        omega
      · have hbe : b = (2 : Fin 7) := Fin.ext (by omega)
        exact absurd hbe hba
      · have hbe : b = (3 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (3 : Fin 7) = (9 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_3_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (3 : Fin 7) = (343 / 81 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_3]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (3 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 3 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 3 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (4 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) = (11 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_4_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) = (49 / 9 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_4]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 3 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 3 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (5 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) = (11 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_5_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) = (49 / 9 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_5]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 3 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 3 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (6 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (6 : Fin 7) = (99 / 14 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_6_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (6 : Fin 7) = (7 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_6]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (6 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 4 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 4 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
    · -- state 729 / 343, row 3
      rcases hb0 : b.val with _ | _ | _ | _ | _ | _ | _
      · simp [hb0] at hbpos
      · have hbe : b = (1 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) = (3 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_1_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) = (1 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_1]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 1 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 1 := by exact_mod_cast hjb
        omega
      · have hbe : b = (2 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) = (7 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_2_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) = (5 / 2 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_2]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 2 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 2 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (3 : Fin 7) := Fin.ext (by omega)
        exact absurd hbe hba
      · have hbe : b = (4 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) = (11 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_4_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) = (49 / 9 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_4]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 2 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 2 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (5 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) = (11 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_5_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) = (49 / 9 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_5]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 2 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 2 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (6 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (6 : Fin 7) = (99 / 14 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_6_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (6 : Fin 7) = (7 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_6]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (6 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 3 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 3 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
    · -- state 18 / 7, row 3
      rcases hb0 : b.val with _ | _ | _ | _ | _ | _ | _
      · simp [hb0] at hbpos
      · have hbe : b = (1 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) = (3 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_1_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) = (1 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_1]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 1 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 1 := by exact_mod_cast hjb
        omega
      · have hbe : b = (2 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) = (7 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_2_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) = (5 / 2 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_2]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 2 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 2 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (3 : Fin 7) := Fin.ext (by omega)
        exact absurd hbe hba
      · have hbe : b = (4 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) = (11 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_4_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) = (49 / 9 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_4]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 2 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 2 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (5 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) = (11 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_5_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) = (49 / 9 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_5]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 2 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 2 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (6 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (6 : Fin 7) = (99 / 14 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_6_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (6 : Fin 7) = (7 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_6]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (6 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 3 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 3 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
    · -- state 1377 / 343, row 3
      rcases hb0 : b.val with _ | _ | _ | _ | _ | _ | _
      · simp [hb0] at hbpos
      · have hbe : b = (1 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) = (3 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_1_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) = (1 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_1]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 1 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 1 := by exact_mod_cast hjb
        omega
      · have hbe : b = (2 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) = (7 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_2_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) = (5 / 2 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_2]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 2 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 2 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (3 : Fin 7) := Fin.ext (by omega)
        exact absurd hbe hba
      · have hbe : b = (4 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) = (11 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_4_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) = (49 / 9 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_4]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 3 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 3 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (5 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) = (11 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_5_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) = (49 / 9 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_5]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 3 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 3 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (6 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (6 : Fin 7) = (99 / 14 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_6_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (6 : Fin 7) = (7 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_6]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (6 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 4 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 4 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
    · -- state 81 / 49, row 4
      rcases hb0 : b.val with _ | _ | _ | _ | _ | _ | _
      · simp [hb0] at hbpos
      · have hbe : b = (1 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) = (3 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_1_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) = (1 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_1]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 1 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 1 := by exact_mod_cast hjb
        omega
      · have hbe : b = (2 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) = (7 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_2_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) = (5 / 2 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_2]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 1 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 1 := by exact_mod_cast hjb
        omega
      · have hbe : b = (3 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (3 : Fin 7) = (9 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_3_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (3 : Fin 7) = (343 / 81 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_3]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (3 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 2 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 2 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (4 : Fin 7) := Fin.ext (by omega)
        exact absurd hbe hba
      · have hbe : b = (5 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) = (11 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_5_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) = (49 / 9 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_5]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 2 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 2 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (6 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (6 : Fin 7) = (99 / 14 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_6_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (6 : Fin 7) = (7 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_6]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (6 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 2 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 2 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
    · -- state 153 / 49, row 4
      rcases hb0 : b.val with _ | _ | _ | _ | _ | _ | _
      · simp [hb0] at hbpos
      · have hbe : b = (1 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) = (3 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_1_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) = (1 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_1]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 1 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 1 := by exact_mod_cast hjb
        omega
      · have hbe : b = (2 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) = (7 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_2_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) = (5 / 2 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_2]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 2 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 2 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (3 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (3 : Fin 7) = (9 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_3_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (3 : Fin 7) = (343 / 81 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_3]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (3 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 2 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 2 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (4 : Fin 7) := Fin.ext (by omega)
        exact absurd hbe hba
      · have hbe : b = (5 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) = (11 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_5_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) = (49 / 9 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_5]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 3 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 3 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (6 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (6 : Fin 7) = (99 / 14 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_6_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (6 : Fin 7) = (7 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_6]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (6 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 3 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 3 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
    · -- state 81 / 49, row 5
      rcases hb0 : b.val with _ | _ | _ | _ | _ | _ | _
      · simp [hb0] at hbpos
      · have hbe : b = (1 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) = (3 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_1_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) = (1 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_1]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 1 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 1 := by exact_mod_cast hjb
        omega
      · have hbe : b = (2 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) = (7 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_2_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) = (5 / 2 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_2]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 1 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 1 := by exact_mod_cast hjb
        omega
      · have hbe : b = (3 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (3 : Fin 7) = (9 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_3_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (3 : Fin 7) = (343 / 81 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_3]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (3 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 2 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 2 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (4 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) = (11 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_4_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) = (49 / 9 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_4]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 2 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 2 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (5 : Fin 7) := Fin.ext (by omega)
        exact absurd hbe hba
      · have hbe : b = (6 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (6 : Fin 7) = (99 / 14 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_6_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (6 : Fin 7) = (7 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_6]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (6 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 2 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 2 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
    · -- state 153 / 49, row 5
      rcases hb0 : b.val with _ | _ | _ | _ | _ | _ | _
      · simp [hb0] at hbpos
      · have hbe : b = (1 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) = (3 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_1_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) = (1 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_1]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 1 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 1 := by exact_mod_cast hjb
        omega
      · have hbe : b = (2 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) = (7 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_2_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) = (5 / 2 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_2]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 2 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 2 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (3 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (3 : Fin 7) = (9 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_3_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (3 : Fin 7) = (343 / 81 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_3]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (3 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 2 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 2 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (4 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) = (11 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_4_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) = (49 / 9 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_4]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 3 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 3 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (5 : Fin 7) := Fin.ext (by omega)
        exact absurd hbe hba
      · have hbe : b = (6 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (6 : Fin 7) = (99 / 14 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_6_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (6 : Fin 7) = (7 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_6]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (6 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 3 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 3 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
    · -- state 9 / 7, row 6
      rcases hb0 : b.val with _ | _ | _ | _ | _ | _ | _
      · simp [hb0] at hbpos
      · have hbe : b = (1 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) = (3 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_1_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) = (1 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_1]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 1 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 1 := by exact_mod_cast hjb
        omega
      · have hbe : b = (2 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) = (7 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_2_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) = (5 / 2 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_2]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 1 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 1 := by exact_mod_cast hjb
        omega
      · have hbe : b = (3 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (3 : Fin 7) = (9 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_3_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (3 : Fin 7) = (343 / 81 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_3]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (3 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 1 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 1 := by exact_mod_cast hjb
        omega
      · have hbe : b = (4 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) = (11 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_4_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) = (49 / 9 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_4]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 2 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 2 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (5 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) = (11 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_5_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) = (49 / 9 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_5]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 2 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 2 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (6 : Fin 7) := Fin.ext (by omega)
        exact absurd hbe hba
    · -- state 17 / 7, row 6
      rcases hb0 : b.val with _ | _ | _ | _ | _ | _ | _
      · simp [hb0] at hbpos
      · have hbe : b = (1 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) = (3 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_1_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) = (1 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_1]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 1 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 1 := by exact_mod_cast hjb
        omega
      · have hbe : b = (2 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) = (7 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_2_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) = (5 / 2 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_2]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 2 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 2 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (3 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (3 : Fin 7) = (9 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_3_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (3 : Fin 7) = (343 / 81 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_3]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (3 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 2 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 2 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (4 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) = (11 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_4_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) = (49 / 9 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_4]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 2 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 2 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (5 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) = (11 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_5_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) = (49 / 9 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_5]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 2 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 2 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (6 : Fin 7) := Fin.ext (by omega)
        exact absurd hbe hba
    · -- state 25 / 7, row 6
      rcases hb0 : b.val with _ | _ | _ | _ | _ | _ | _
      · simp [hb0] at hbpos
      · have hbe : b = (1 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) = (3 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_1_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) = (1 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_1]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (1 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 1 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 1 := by exact_mod_cast hjb
        omega
      · have hbe : b = (2 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) = (7 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_2_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) = (5 / 2 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_2]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (2 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 2 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 2 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (3 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (3 : Fin 7) = (9 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_3_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (3 : Fin 7) = (343 / 81 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_3]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (3 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 3 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 3 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (4 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) = (11 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_4_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) = (49 / 9 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_4]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (4 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 3 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 3 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (5 : Fin 7) := Fin.ext (by omega)
        subst hbe
        have hhie : dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) = (11 / 2 : ℚ) := by
          norm_num [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_5_0]
        have hloe : dfsLo (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) = (49 / 9 : ℚ) := by
          norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_5]
        have hhpos : 0 < (dfsHi (boxN m4res_1_1_3_4_5_5_7) tbl2 (5 : Fin 7) : ℝ) := by
          rw [hhie]; positivity
        have hjb : (j : ℚ) < 3 := by
          have h2 := entry_lt_q (hhipos := hhpos) he
          rw [hhie] at h2
          have hsub : ((8 * j - 1 : ℕ) : ℚ) = (8 : ℚ) * (j : ℚ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 8 * j)]
            push_cast
            ring
          rw [hsub] at h2
          norm_num at h2
          linarith
        have jn : j < 3 := by exact_mod_cast hjb
        interval_cases j <;>
          first
            | omega
            | (rw [hhie] at he; norm_num at he; rw [hloe]; simp [S2] <;> norm_num)
      · have hbe : b = (6 : Fin 7) := Fin.ext (by omega)
        exact absurd hbe hba

    · exact absurd hq (by simp)
-- (a data record: no axioms to print)

/-- **The zone-form per-leaf domination of leaf node 2** — OWED (b)'s PROOF side, pilot
instance: the reach_utc verdict (relaxed-closure form) plus the envelope dominations kill
every zone-form realized continuation from the leaf's state. -/
theorem no_zone_chain_leaf2 (ρ : Fin 7 → ℝ) (hpos : ∀ k, 0 < ρ k) (hfine : UFine ρ tbl2)
    (steps : List Step) (hzone : ∀ s ∈ steps, ZoneTooth s.A s.B) :
    ¬ ChainRealized ρ tbl2 (3 : Fin 7) (9 : ℚ) steps := by
  refine no_zone_chain_of_reach_utc (boxN m4res_1_1_3_4_5_5_7) tbl2 (3 : Fin 7) (9 : ℚ)
    (18 / 7 : ℚ) verdict2 ρ hpos hfine (domHi2 ρ hpos hfine) (domLo2 ρ hpos hfine)
    (fun b hb => ?_) (by decide) ⟨1, rfl⟩ ?_ steps hzone
  · fin_cases b <;>
      simp [dfsHi, boxN, m4res_1_1_3_4_5_5_7, tbl2] <;> norm_num
  · norm_num [dfsLo, boxN, m4res_1_1_3_4_5_5_7, tbl2_c_0_3]

#print axioms no_zone_chain_leaf2

/-- **Finding 2, machine-checked: the UNRESTRICTED per-leaf domination is FALSE.**  The
state graph only models envelope comb teeth, while a realized continuation may use
non-teeth zone edges: `ρbad` realizes `tbl2` exactly (all 42 bounds) and realizes the
one-step continuation `⟨row 1, A = 2, B = 8⟩` with the exit bound `ρ 1 / ρ 0 < 8/7` —
while the verdict `no_completing_state_reachable` is true.  The prune is sound against
ZONE-FORM chains only (`ZoneTooth`), which the E810 side supplies
(`zone_of_dfsSoftAdm_realized`). -/
noncomputable def ρbad : Fin 7 → ℝ := fun k => ((match k with
  | (0 : Fin 7) => (1 : ℚ)
  | (1 : Fin 7) => 11 / 10
  | (2 : Fin 7) => 3
  | (3 : Fin 7) => 9 / 2
  | (4 : Fin 7) => 547 / 100
  | (5 : Fin 7) => 549 / 100
  | (6 : Fin 7) => 701 / 100) : ℝ)

theorem unrestricted_false :
    ∃ ρ : Fin 7 → ℝ, (∀ k, 0 < ρ k) ∧ UFine ρ tbl2 ∧
      ChainRealized ρ tbl2 (3 : Fin 7) (9 : ℚ) [⟨(1 : Fin 7), (2 : ℚ), (8 : ℚ)⟩] := by
  refine ⟨ρbad, ?_, ?_, ?_⟩
  · intro k
    fin_cases k <;> simp only [ρbad] <;> norm_num
  · intro i j
    fin_cases i <;> fin_cases j <;>
      first
        | exact bhof_none_of rfl
        | exact bhof_some (by norm_num [BHolds, ρbad])
  · refine ⟨tbl2, ?_, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · exact uStep_eq_some' (by norm_num) (by norm_num) (by norm_num)
        (uAdd_eq_some_self (by simp [uKeepCur, tbl2_c_3_1] <;> norm_num))
        (uAdd_eq_some_self (by simp [uKeepCur, tbl2_c_1_3] <;> norm_num))
    · show ((ρbad 3 / ρbad 1 : ℝ)) < (((9 / 2 : ℚ) : ℝ))
      norm_num [ρbad]
    · show ((ρbad 1 / ρbad 3 : ℝ)) < (((8 / 9 : ℚ) : ℝ))
      norm_num [ρbad]
    · show ((ρbad 1 / ρbad 0 : ℝ)) < (((8 / 7 : ℚ) : ℝ))
      norm_num [ρbad]

#print axioms unrestricted_false

/-! The pilot consumption note: the leaf's zone-form domination `no_zone_chain_leaf2` IS the
`DfsPruneDomZone`-condition of the transcribed tree `tree2` up to the definitional
unfolding `tree2 = DfsCert.prune node2` and `node2 = ⟨tbl2, 3, 9, 18/7, _⟩` (the
`DfsPruneDomZone.prune` case's statement is exactly `no_zone_chain_leaf2`'s conclusion;
the wrapper definition is omitted here because Lean's codegen linter rejects the
`Real`-dependent proof term for a theorem-shaped def — the composition
`m4CertSound_of_forest_zone` consumes it directly). -/



end Fresh.M4Cert
