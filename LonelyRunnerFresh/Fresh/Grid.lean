import Mathlib
import Fresh.Framework

/-!
# The grid layer (Task A): native versions of v9 sections 2 and 3 (Theorems 4 to 6)

Written 2026-10-07.  Imports Mathlib and `Fresh.Framework` only.  Nothing is imported from the existing
`LonelyRunner` repo; every proof below was written here.  Provenance (the existing declaration each theorem
corresponds to, read and not copied) is recorded in the docstring of each theorem.

Contents.
* Arithmetic of `distInt` (shift by an integer, upper bound by `|x|`, value at `z/8`).
* `octagon`: eight points pairwise at circle distance at least `1/8` are a regular octagon, i.e. every
  difference is a whole number of eighths (v9 Theorem 2 in difference form).
* `deviation_position` (v9 Theorem 5), `deviation_survives` and `deviation_necessary`, `deviation_integral`,
  `deviation_iff` (v9 Theorem 6), and the unanchored counterexample `unanchored_not_integral`.
* `gridGlobalIsolation : GridGlobalIsolation`.
* AP (v9 Theorem 4): `ap_globalIsolation`, `ap_not_even`, and the exact characterisation
  `ap_globalIsolation_iff` (global isolation at `t` iff `t = a/(8d)` with `a` a unit mod 8, at every real `t`),
  and `grid_extra_instant` (why exhaustiveness is special to the AP: a grid whose step is not primitive has more).
* One counting step, tagged at the step in `octagon`: **[PROVISIONAL: counting tool]** (injective `Fin 8 → Fin 8`
  is onto).  Every result that uses `octagon` (`deviation_integral*`, `deviation_iff`, `ap_globalIsolation_iff`)
  rests on it; `deviation_survives`, `deviation_necessary`, `gridGlobalIsolation`, `ap_globalIsolation`,
  `ap_not_even` do not.

No runner is stationary anywhere: every statement is about differences of speeds; no speed is set to 0.
-/

open Classical

namespace Fresh

/-! ## Arithmetic of `distInt` -/

theorem distInt_add_int (x : ℝ) (z : ℤ) : distInt (x + z) = distInt x := by
  unfold distInt
  rw [round_add_intCast]
  push_cast
  congr 1
  ring

#print axioms distInt_add_int

theorem distInt_le_abs (x : ℝ) : distInt x ≤ |x| := by
  unfold distInt
  simpa using round_le x 0

#print axioms distInt_le_abs

theorem distInt_intCast (z : ℤ) : distInt (z : ℝ) = 0 := by
  unfold distInt
  simp [round_intCast]

#print axioms distInt_intCast

/-- A whole number of eighths that is not a whole number of laps is at distance at least `1/8` from a lap. -/
theorem distInt_int_div_eight {z : ℤ} (h : ¬ (8 : ℤ) ∣ z) : (1 / 8 : ℝ) ≤ distInt ((z : ℝ) / 8) := by
  unfold distInt
  set m : ℤ := round ((z : ℝ) / 8)
  have hne : z - 8 * m ≠ 0 := by
    intro h0
    exact h ⟨m, by linarith⟩
  have h1 : (1 : ℝ) ≤ |((z - 8 * m : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hne
  have hrw : (z : ℝ) / 8 - (m : ℝ) = ((z - 8 * m : ℤ) : ℝ) / 8 := by
    push_cast
    ring
  rw [hrw, abs_div]
  have : |(8 : ℝ)| = 8 := by norm_num
  rw [this]
  linarith

#print axioms distInt_int_div_eight

/-- A whole number of laps, written in eighths, is at distance 0. -/
theorem distInt_int_div_eight_of_dvd {z : ℤ} (h : (8 : ℤ) ∣ z) : distInt ((z : ℝ) / 8) = 0 := by
  obtain ⟨m, rfl⟩ := h
  have : (((8 * m : ℤ) : ℝ) / 8) = (m : ℝ) := by push_cast; ring
  rw [this, distInt_intCast]

#print axioms distInt_int_div_eight_of_dvd

/-! ## The octagon: zero slack (v9 Theorem 2, in difference form) -/

/-- **The octagon.**  If eight points on the circle are pairwise at distance at least `1/8`, every difference is a
whole number of eighths: the points are the vertices of a regular octagon.  This is v9 Theorem 2 (all gaps exactly
`1/8`) stated without sorting.

Proof.  Write each point as `⌊x⌋ + (B + r)/8` with bin `B ∈ {0,…,7}` and remainder `r ∈ [0,1)`.  Two points in one
bin are closer than `1/8`, so the bin map is injective, hence onto the eight bins
**[PROVISIONAL: counting tool]** (an injective map `Fin 8 → Fin 8` is onto; supports the claim that every bin is
occupied).  For consecutive bins (cyclically, `7` then `0`) the separation `(1 + r' - r)/8 ≥ 1/8` gives `r ≤ r'`;
going once round the eight bins, the remainders are cyclically non-decreasing, hence all equal.  Then every
difference is `(B - B')/8` plus whole laps.

Provenance: corresponds to `grid_of_pairwise` (sorting the positions, gaps sum to one) and `pos_eq_multiple` in
`ConstructionN/Integrality.lean` of the existing repo.  The route here is different (bins and remainders, no sort)
and was written from scratch. -/
theorem octagon (x : Fin 8 → ℝ)
    (hsep : ∀ i j, i ≠ j → (1 / 8 : ℝ) ≤ distInt (x i - x j)) :
    ∀ i j, ∃ z : ℤ, x i - x j = (z : ℝ) / 8 := by
  set f : Fin 8 → ℝ := fun i => Int.fract (x i) with hf
  have hf0 : ∀ i, 0 ≤ 8 * f i := fun i => by
    have := Int.fract_nonneg (x i); simp only [hf]; linarith
  have hf1 : ∀ i, 8 * f i < 8 := fun i => by
    have := Int.fract_lt_one (x i); simp only [hf]; linarith
  set B : Fin 8 → ℕ := fun i => ⌊8 * f i⌋₊ with hB
  have hBlt : ∀ i, B i < 8 := fun i => (Nat.floor_lt (hf0 i)).2 (by exact_mod_cast hf1 i)
  set r : Fin 8 → ℝ := fun i => 8 * f i - B i with hr
  have hr0 : ∀ i, 0 ≤ r i := fun i => by
    simp only [hr, hB]; linarith [Nat.floor_le (hf0 i)]
  have hr1 : ∀ i, r i < 1 := fun i => by
    simp only [hr, hB]; linarith [Nat.lt_floor_add_one (8 * f i)]
  have hx : ∀ i, x i = (⌊x i⌋ : ℝ) + ((B i : ℝ) + r i) / 8 := fun i => by
    have h1 : ((B i : ℝ) + r i) / 8 = f i := by simp only [hr]; ring
    rw [h1]
    exact (Int.floor_add_fract (x i)).symm
  have hdiff : ∀ i j, x i - x j
      = ((B i : ℝ) - B j + (r i - r j)) / 8 + ((⌊x i⌋ - ⌊x j⌋ : ℤ) : ℝ) := by
    intro i j
    have := hx i
    have := hx j
    push_cast
    linarith
  -- two points in one bin are closer than 1/8
  have hBinj : ∀ i j, B i = B j → i = j := by
    intro i j hij
    by_contra hne
    have h := hsep i j hne
    have hij' : (B i : ℝ) = B j := by exact_mod_cast hij
    have hd : x i - x j = (r i - r j) / 8 + ((⌊x i⌋ - ⌊x j⌋ : ℤ) : ℝ) := by
      rw [hdiff i j, hij']; ring
    rw [hd, distInt_add_int] at h
    have h2 := distInt_le_abs ((r i - r j) / 8)
    have h3 : |(r i - r j) / 8| < 1 / 8 := by
      rw [abs_lt]
      constructor <;> linarith [hr0 i, hr0 j, hr1 i, hr1 j]
    linarith
  -- consecutive bins (cyclically): the remainder does not decrease
  have hstep : ∀ i j, (B j = B i + 1 ∨ (B i = 7 ∧ B j = 0)) → r i ≤ r j := by
    intro i j hcase
    have hne : j ≠ i := by
      intro h; subst h; omega
    have h := hsep j i hne
    obtain ⟨n, hn⟩ : ∃ n : ℤ, x j - x i = (1 + r j - r i) / 8 + (n : ℝ) := by
      rcases hcase with h1 | ⟨h1, h2⟩
      · refine ⟨⌊x j⌋ - ⌊x i⌋, ?_⟩
        have hb : (B j : ℝ) = B i + 1 := by exact_mod_cast h1
        rw [hdiff j i, hb]; ring
      · refine ⟨⌊x j⌋ - ⌊x i⌋ - 1, ?_⟩
        have hb1 : (B i : ℝ) = 7 := by exact_mod_cast h1
        have hb2 : (B j : ℝ) = 0 := by exact_mod_cast h2
        rw [hdiff j i, hb1, hb2]; push_cast; ring
    rw [hn, distInt_add_int] at h
    have h2 := distInt_le_abs ((1 + r j - r i) / 8)
    have hpos : 0 < (1 + r j - r i) / 8 := by linarith [hr0 j, hr1 i]
    rw [abs_of_pos hpos] at h2
    linarith
  -- every bin is occupied
  let bin : Fin 8 → Fin 8 := fun i => ⟨B i, hBlt i⟩
  have hbinj : Function.Injective bin := by
    intro i j h
    exact hBinj i j (by simpa [bin] using congrArg Fin.val h)
  -- [PROVISIONAL: counting tool] injective `Fin 8 → Fin 8` is onto; supports "every bin is occupied".
  have hbsurj : Function.Surjective bin := Finite.injective_iff_surjective.mp hbinj
  choose g hg using hbsurj
  have hg' : ∀ b : Fin 8, B (g b) = b.val := fun b => by
    simpa [bin] using congrArg Fin.val (hg b)
  have c0 := hstep (g 0) (g 1) (Or.inl (by rw [hg', hg']; decide))
  have c1 := hstep (g 1) (g 2) (Or.inl (by rw [hg', hg']; decide))
  have c2 := hstep (g 2) (g 3) (Or.inl (by rw [hg', hg']; decide))
  have c3 := hstep (g 3) (g 4) (Or.inl (by rw [hg', hg']; decide))
  have c4 := hstep (g 4) (g 5) (Or.inl (by rw [hg', hg']; decide))
  have c5 := hstep (g 5) (g 6) (Or.inl (by rw [hg', hg']; decide))
  have c6 := hstep (g 6) (g 7) (Or.inl (by rw [hg', hg']; decide))
  have c7 := hstep (g 7) (g 0) (Or.inr ⟨by rw [hg']; decide, by rw [hg']; decide⟩)
  have hall : ∀ b : Fin 8, r (g b) = r (g 0) := by
    intro b
    fin_cases b <;> simp <;> linarith
  have hgi : ∀ i, g (bin i) = i := fun i => hBinj _ _ (by rw [hg'])
  have hreq : ∀ i, r i = r (g 0) := fun i => by rw [← hgi i]; exact hall _
  intro i j
  refine ⟨(B i : ℤ) - B j + 8 * (⌊x i⌋ - ⌊x j⌋), ?_⟩
  rw [hdiff i j, hreq i, hreq j]
  push_cast
  ring

#print axioms octagon

/-! ## v9 Theorem 5: the position formula -/

/-- **v9 Theorem 5 (position).**  At `t = a/(8d)` a runner of speed `v₀ + k d + e` sits at
`v₀ a/(8d) + k a/8 + (e a/d)/8`: a common rotation, the AP vertex `k a/8`, and a displacement of exactly `e a/d`
eighths.  Pure algebra; no hypothesis on `a`.

Provenance: `ConstructionN.displacement` (`Parts.lean`) and `deviation_separation` (`Reference.lean`). -/
theorem deviation_position (v₀ d : ℝ) (hd : d ≠ 0) (k : ℤ) (e : ℝ) (a : ℤ) :
    (v₀ + (k : ℝ) * d + e) * ((a : ℝ) / (8 * d))
      = v₀ * a / (8 * d) + (k : ℝ) * a / 8 + (e * a / d) / 8 := by
  field_simp

#print axioms deviation_position

/-- The pair form of Theorem 5: when both displacements are whole eighths `w, w'`, the separation of the pair at
`a/(8d)` is `((k a + w) - (k' a + w'))/8`.  Provenance: `deviation_separation` (`ConstructionN/Reference.lean`). -/
theorem deviation_pair (v₀ d : ℝ) (hd : d ≠ 0) (a k k' : ℤ) (e e' : ℝ) (w w' : ℤ)
    (hw : e * a / d = w) (hw' : e' * a / d = w') :
    ((v₀ + (k : ℝ) * d + e) - (v₀ + (k' : ℝ) * d + e')) * ((a : ℝ) / (8 * d))
      = (((k * a + w) - (k' * a + w') : ℤ) : ℝ) / 8 := by
  rw [sub_mul, deviation_position v₀ d hd k e a, deviation_position v₀ d hd k' e' a, hw, hw']
  push_cast
  ring

#print axioms deviation_pair

/-! ## v9 Theorem 6: when the global instant survives a deviation -/

/-- **v9 Theorem 6, sufficient direction.**  If every displacement `e j · a / d` is a whole number `w j` of eighths
and `j ↦ idx j · a + w j` is injective mod 8, all eight runners are isolated at `a/(8d)`.

Neither the anchoring `e 0 = 0` nor `a` being a unit is needed for this direction: injectivity of the combined map
already forces every pair onto distinct vertices.  Provenance: `survives_of` (`ConstructionN/Reference.lean`). -/
theorem deviation_survives (v : Fin 8 → ℝ) (d v₀ : ℝ) (idx : Fin 8 → ℤ) (e : Fin 8 → ℝ) (hd : 0 < d)
    (hv : ∀ j, v j = v₀ + (idx j : ℝ) * d + e j) (a : ℤ) (w : Fin 8 → ℤ)
    (hw : ∀ j, e j * a / d = w j) (hinj : CompleteResidues (fun j => idx j * a + w j)) :
    GloballyIsolatedAt v ((a : ℝ) / (8 * d)) := by
  intro k i hik
  rw [hv i, hv k, deviation_pair v₀ d hd.ne' a (idx i) (idx k) (e i) (e k) (w i) (w k) (hw i) (hw k)]
  apply distInt_int_div_eight
  intro h8
  apply hik
  apply hinj
  exact (Int.modEq_of_dvd h8).symm

#print axioms deviation_survives

/-- **v9 Theorem 6, necessary direction (given integrality).**  If every displacement is a whole number of eighths
and the instant `a/(8d)` is a global isolation, then `j ↦ idx j · a + w j` is injective mod 8: two runners sent to one
vertex are at distance 0.  Provenance: `not_dvd_of_sep` (`ConstructionN/Integrality.lean`). -/
theorem deviation_necessary (v : Fin 8 → ℝ) (d v₀ : ℝ) (idx : Fin 8 → ℤ) (e : Fin 8 → ℝ) (hd : 0 < d)
    (hv : ∀ j, v j = v₀ + (idx j : ℝ) * d + e j) (a : ℤ) (w : Fin 8 → ℤ)
    (hw : ∀ j, e j * a / d = w j) (hiso : GloballyIsolatedAt v ((a : ℝ) / (8 * d))) :
    CompleteResidues (fun j => idx j * a + w j) := by
  intro j j' hjj
  by_contra hne
  have h := hiso j' j hne
  rw [hv j, hv j', deviation_pair v₀ d hd.ne' a (idx j) (idx j') (e j) (e j') (w j) (w j') (hw j) (hw j'),
    distInt_int_div_eight_of_dvd (Int.ModEq.dvd (show Int.ModEq 8 _ _ from hjj.symm))] at h
  norm_num at h

#print axioms deviation_necessary

/-- **Integrality, unanchored.**  A global isolation at `a/(8d)` forces every RELATIVE displacement
`(e j - e 0) · a / d` to be a whole number of eighths.  This is as much integrality as holds without the anchoring:
see `unanchored_not_integral`.  The proof is the octagon: all eight positions are vertices of one regular octagon.
Provenance: `int_of_pairwise_sep` (`ConstructionN/Integrality.lean`); the octagon step is `octagon` above. -/
theorem deviation_integral_unanchored (v : Fin 8 → ℝ) (d v₀ : ℝ) (idx : Fin 8 → ℤ) (e : Fin 8 → ℝ)
    (hd : 0 < d) (hv : ∀ j, v j = v₀ + (idx j : ℝ) * d + e j) (a : ℤ)
    (hiso : GloballyIsolatedAt v ((a : ℝ) / (8 * d))) :
    ∀ j, ∃ w : ℤ, (e j - e 0) * a / d = w := by
  intro j
  set t : ℝ := (a : ℝ) / (8 * d) with ht
  have hsep : ∀ i i', i ≠ i' → (1 / 8 : ℝ) ≤ distInt (v i * t - v i' * t) := fun i i' h => by
    rw [← sub_mul]; exact hiso i' i h
  obtain ⟨z, hz⟩ := octagon (fun i => v i * t) hsep j 0
  refine ⟨z - (idx j - idx 0) * a, ?_⟩
  have hpos : (v j - v 0) * t = (((idx j - idx 0) * a : ℤ) : ℝ) / 8 + ((e j - e 0) * a / d) / 8 := by
    rw [hv j, hv 0, ht]
    push_cast
    field_simp
    ring
  have hz' : (v j - v 0) * t = (z : ℝ) / 8 := by rw [sub_mul]; exact hz
  push_cast at hpos ⊢
  linarith

#print axioms deviation_integral_unanchored

/-- **Integrality, anchored (`e 0 = 0`).**  A global isolation at `a/(8d)` forces every displacement `e j · a / d`
to be a whole number of eighths. -/
theorem deviation_integral (v : Fin 8 → ℝ) (d v₀ : ℝ) (idx : Fin 8 → ℤ) (e : Fin 8 → ℝ)
    (hd : 0 < d) (he : e 0 = 0) (hv : ∀ j, v j = v₀ + (idx j : ℝ) * d + e j) (a : ℤ)
    (hiso : GloballyIsolatedAt v ((a : ℝ) / (8 * d))) :
    ∀ j, ∃ w : ℤ, e j * a / d = w := by
  intro j
  obtain ⟨w, hw⟩ := deviation_integral_unanchored v d v₀ idx e hd hv a hiso j
  exact ⟨w, by rw [he, sub_zero] at hw; exact hw⟩

#print axioms deviation_integral

/-- **v9 Theorem 6 (anchored), both directions.**  With `e 0 = 0`: the instant `a/(8d)` is a global isolation iff
every displacement `e j · a / d` is a whole number `w j` and `j ↦ idx j · a + w j` is injective mod 8.
Provenance: `survives_of` + `int_of_pairwise_sep` + `not_dvd_of_sep`. -/
theorem deviation_iff (v : Fin 8 → ℝ) (d v₀ : ℝ) (idx : Fin 8 → ℤ) (e : Fin 8 → ℝ)
    (hd : 0 < d) (he : e 0 = 0) (hv : ∀ j, v j = v₀ + (idx j : ℝ) * d + e j) (a : ℤ) :
    GloballyIsolatedAt v ((a : ℝ) / (8 * d)) ↔
      ∃ w : Fin 8 → ℤ, (∀ j, e j * a / d = w j) ∧ CompleteResidues (fun j => idx j * a + w j) := by
  constructor
  · intro hiso
    choose w hw using deviation_integral v d v₀ idx e hd he hv a hiso
    exact ⟨w, hw, deviation_necessary v d v₀ idx e hd hv a w hw hiso⟩
  · rintro ⟨w, hw, hinj⟩
    exact deviation_survives v d v₀ idx e hd hv a w hw hinj

#print axioms deviation_iff

/-- The index map `j ↦ j` has a complete residue system mod 8. -/
theorem completeResidues_id : CompleteResidues (fun j : Fin 8 => ((j : ℕ) : ℤ)) := by
  intro j j' h
  have := j.isLt
  have := j'.isLt
  apply Fin.ext
  simp only at h
  omega

#print axioms completeResidues_id

/-- **Why the anchoring is needed (counterexample, v9 Theorem 6 remark).**  Speeds `1 + j + 1/2`, written as the AP
`1 + j` with deviation `e j = 1/2` for every `j` (so `e 0 ≠ 0`), are globally isolated at `1/8`, yet `e 0 · 1 / 1 = 1/2`
is not a whole number.  The failed hypothesis is `e 0 = 0`: a common deviation is a common rotation, invisible to every
separation, so integrality can only hold for relative displacements (`deviation_integral_unanchored`). -/
theorem unanchored_not_integral :
    ∃ (v e : Fin 8 → ℝ), IsArrangement v ∧ (∀ j, v j = 1 + (((j : ℕ) : ℤ) : ℝ) * 1 + e j) ∧
      GloballyIsolatedAt v ((1 : ℤ) / (8 * 1)) ∧ ¬ ∃ w : ℤ, e 0 * (1 : ℤ) / 1 = w := by
  refine ⟨fun j => 1 + (((j : ℕ) : ℤ) : ℝ) * 1 + 1 / 2, fun _ => 1 / 2, ?_, fun j => rfl, ?_, ?_⟩
  · refine ⟨fun j => by positivity, ?_⟩
    intro j j' h
    simp only [add_left_inj, mul_one, add_right_inj, Int.cast_natCast, Nat.cast_inj] at h
    exact Fin.ext h
  · refine deviation_survives _ 1 (3 / 2) (fun j => ((j : ℕ) : ℤ)) (fun _ => 0) one_pos
      (fun j => by ring) 1 (fun _ => 0) (fun j => by simp) ?_
    intro j j' h
    exact completeResidues_id j j' (by simpa using h)
  · rintro ⟨w, hw⟩
    have h2 : (2 * w : ℤ) = 1 := by
      have : (1 : ℝ) / 2 = w := by simpa using hw
      exact_mod_cast (by linarith : (2 * (w : ℝ)) = 1)
    omega

#print axioms unanchored_not_integral

/-! ## The grid claim of `Framework.lean` -/

/-- **`GridGlobalIsolation`** (v9 Theorems 4 and 5 for a grid): a grid arrangement `v₀ + idx j · d`, with the indices
a complete residue system mod 8, is globally isolated at every `a/(8d)` with `a` a unit mod 8.  Proof: Theorem 6
with zero deviation; `a` a unit keeps `j ↦ idx j · a` injective mod 8.
Provenance: `ap_reference` (`ConstructionN/Reference.lean`) for the AP; the grid form is v9 §3. -/
theorem gridGlobalIsolation : GridGlobalIsolation := by
  intro v d v₀ idx hd hidx hv a ha
  refine deviation_survives v d v₀ idx (fun _ => 0) hd (fun j => by rw [hv j]; ring) a (fun _ => 0)
    (fun j => by simp) ?_
  intro j j' h
  simp only [add_zero] at h
  apply hidx
  have h8 : (8 : ℤ) ∣ (idx j' - idx j) * a := by
    rw [sub_mul]; exact Int.ModEq.dvd (show Int.ModEq 8 _ _ from h)
  exact (Int.modEq_of_dvd (ha.symm.dvd_of_dvd_mul_right h8))

#print axioms gridGlobalIsolation

/-! ## The AP (v9 Theorem 4) -/

/-- The AP is globally isolated at every `a/(8d)` with `a` a unit mod 8.  Provenance: `ap_reference`. -/
theorem ap_globalIsolation (v : Fin 8 → ℝ) (d v₀ : ℝ) (hd : 0 < d)
    (hv : ∀ j : Fin 8, v j = v₀ + ((j : ℕ) : ℝ) * d) (a : ℤ) (ha : IsCoprime a 8) :
    GloballyIsolatedAt v ((a : ℝ) / (8 * d)) :=
  gridGlobalIsolation v d v₀ (fun j => ((j : ℕ) : ℤ)) hd completeResidues_id
    (fun j => by rw [hv j]; push_cast; ring) a ha

#print axioms ap_globalIsolation

/-- At the AP, `a/(8d)` with `a` even is NOT a global isolation: runners `0` and `4` are `4a/8 = a/2` laps apart,
a whole number of laps, so they coincide on the circle. -/
theorem ap_not_even (v : Fin 8 → ℝ) (d v₀ : ℝ) (hd : 0 < d)
    (hv : ∀ j : Fin 8, v j = v₀ + ((j : ℕ) : ℝ) * d) (a : ℤ) (ha : Even a) :
    ¬ GloballyIsolatedAt v ((a : ℝ) / (8 * d)) := by
  intro hiso
  have h := hiso 0 4 (by decide)
  obtain ⟨b, rfl⟩ := ha
  have hpos : (v 4 - v 0) * (((b + b : ℤ) : ℝ) / (8 * d)) = (((8 * b : ℤ) : ℝ)) / 8 := by
    rw [hv 4, hv 0, show ((4 : Fin 8) : ℕ) = 4 from rfl, show ((0 : Fin 8) : ℕ) = 0 from rfl]
    push_cast
    field_simp
    ring
  rw [hpos, distInt_int_div_eight_of_dvd (dvd_mul_right 8 b)] at h
  norm_num at h

#print axioms ap_not_even

/-- An odd integer is a unit mod 8. -/
theorem isCoprime_eight_of_odd {a : ℤ} (ha : Odd a) : IsCoprime a 8 := by
  obtain ⟨k, rfl⟩ := ha
  have h2 : IsCoprime (2 * k + 1) 2 := ⟨1, -k, by ring⟩
  have := h2.pow_right (n := 3)
  norm_num at this
  exact this

#print axioms isCoprime_eight_of_odd

/-- **v9 Theorem 4 (the φ(8) law), exact.**  The AP `v₀ + j d` is globally isolated at an instant `t` (any real
`t`) if and only if `t = a/(8d)` with `a` a unit mod 8.  This includes "at no other instant": the forward direction
is the octagon (runners 0 and 1 force `d t` to be a whole number of eighths `a/8`) followed by `ap_not_even` (an
even `a` puts runners 0 and 4 together).  In particular on `(0, 2/d]` the instants are exactly the eight points
`a/(8d)`, `a ∈ {1,3,…,15}` (v9 §2, "lonely set at the AP"; not separately stated here).
Provenance: `isolation_forces_coprime_grid`, `instants_on_grid` (`ConstructionN/Instants.lean`). -/
theorem ap_globalIsolation_iff (v : Fin 8 → ℝ) (d v₀ : ℝ) (hd : 0 < d)
    (hv : ∀ j : Fin 8, v j = v₀ + ((j : ℕ) : ℝ) * d) (t : ℝ) :
    GloballyIsolatedAt v t ↔ ∃ a : ℤ, IsCoprime a 8 ∧ t = (a : ℝ) / (8 * d) := by
  constructor
  · intro hiso
    have hsep : ∀ i i', i ≠ i' → (1 / 8 : ℝ) ≤ distInt (v i * t - v i' * t) := fun i i' h => by
      rw [← sub_mul]; exact hiso i' i h
    obtain ⟨z, hz⟩ := octagon (fun i => v i * t) hsep 1 0
    have ht : t = (z : ℝ) / (8 * d) := by
      have h1 : v 1 * t - v 0 * t = d * t := by rw [hv 1, hv 0]; simp; ring
      rw [h1] at hz
      field_simp
      linarith
    refine ⟨z, ?_, ht⟩
    rcases Int.even_or_odd z with he | ho
    · exact absurd (ht ▸ hiso) (ap_not_even v d v₀ hd hv z he)
    · exact isCoprime_eight_of_odd ho
  · rintro ⟨a, ha, rfl⟩
    exact ap_globalIsolation v d v₀ hd hv a ha

#print axioms ap_globalIsolation_iff

/-- **Why "no other instant" is special to the AP, not to every grid.**  The grid with indices `idx j = 9 j` has a
complete residue system mod 8 (`9 j ≡ j`), so `gridGlobalIsolation` applies at `a/(8d)`; but it is the AP of common
difference `9d`, so it is ALSO globally isolated at `1/(72 d)`, which is not `a/(8d)` for any integer `a`.  The
failed hypothesis for exhaustiveness is that `d` be the primitive step (`gcd` of the index differences equal to 1). -/
theorem grid_extra_instant (v : Fin 8 → ℝ) (d v₀ : ℝ) (hd : 0 < d)
    (hv : ∀ j : Fin 8, v j = v₀ + ((9 * (j : ℕ) : ℤ) : ℝ) * d) :
    CompleteResidues (fun j : Fin 8 => ((9 * (j : ℕ) : ℤ))) ∧
      GloballyIsolatedAt v (1 / (72 * d)) ∧ ∀ a : ℤ, (1 / (72 * d) : ℝ) ≠ (a : ℝ) / (8 * d) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j j' h
    have := j.isLt
    have := j'.isLt
    apply Fin.ext
    simp only at h
    omega
  · have h := ap_globalIsolation v (9 * d) v₀ (by positivity) (fun j => by rw [hv j]; push_cast; ring) 1
      isCoprime_one_left
    have he : ((1 : ℤ) : ℝ) / (8 * (9 * d)) = 1 / (72 * d) := by push_cast; ring
    rwa [he] at h
  · intro a h
    have h9 : (9 * a : ℤ) = 1 := by
      have : (1 : ℝ) = 9 * a := by
        field_simp at h
        linarith
      exact_mod_cast this.symm
    omega

#print axioms grid_extra_instant

end Fresh
