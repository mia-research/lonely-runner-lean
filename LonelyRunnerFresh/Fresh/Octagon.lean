import Mathlib
import Fresh.Framework
import Fresh.Grid
import Fresh.Localisation

/-!
# Isolation and the octagon (Task K): native versions of v9 section 1 (Theorems 1 to 3) and the bridge of
# Theorem 10 to arrangements

Written 2026-10-07.  Imports Mathlib, `Fresh.Framework`, `Fresh.Grid`, `Fresh.Localisation` only.  Nothing is
imported from the existing `LonelyRunner` repo; every proof below was written here.

Contents.
* (1) `gapAhead`, `gapBehind` (finset infima, no sorting) and `isolatedAt_iff_gaps` (v9 Theorem 1).
* (2) `pairDist_symm`, `lonely_symmetry`, `isolated_of_all_others` and `not_exactly_seven` (v9 Corollary 3).  The
  proof is the symmetry of circle distance, `distInt (-x) = distInt x`; no counting.
* (3) `globallyIsolatedAt_iff_octagon` (v9 Theorem 2) and `globallyIsolated_pairDist_eighths`.  The forward direction
  uses `Fresh.octagon`, whose own step "an injective `Fin 8 → Fin 8` is onto" is tagged
  **[PROVISIONAL: counting tool]** in `Fresh/Grid.lean`; (3) and its corollary INHERIT that tag.  The backward
  direction does not use it.
* (4) `integer_flank_isolated_iff`: v9 Theorem 10 read on an integer arrangement (speeds `z j`), through
  `Fresh.Localisation.certificate_clear_iff`.  No counting.

No runner is stationary: every statement is about differences of speeds `v i - v k`; no speed is set to 0.
-/

open Classical

namespace Fresh.Octagon

open Fresh

/-! ## (1) The two flanking gaps (v9 Theorem 1, without sorting) -/

theorem erase_nonempty (k : Fin 8) : (Finset.univ.erase k).Nonempty := by
  refine ⟨k + 1, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩⟩
  intro h
  have := congrArg (fun x => x - k) h
  simp at this

#print axioms erase_nonempty

/-- The gap ahead of the subject `k` at `t`: the least forward distance `fract((v i - v k) t)` to another runner. -/
noncomputable def gapAhead (v : Fin 8 → ℝ) (k : Fin 8) (t : ℝ) : ℝ :=
  (Finset.univ.erase k).inf' (erase_nonempty k) (fun i => Int.fract ((v i - v k) * t))

/-- The gap behind the subject `k` at `t`: the least backward distance `fract((v k - v i) t)` to another runner. -/
noncomputable def gapBehind (v : Fin 8 → ℝ) (k : Fin 8) (t : ℝ) : ℝ :=
  (Finset.univ.erase k).inf' (erase_nonempty k) (fun i => Int.fract ((v k - v i) * t))

/-- The gap ahead is the forward distance to an actual runner (the next one ahead). -/
theorem gapAhead_attained (v : Fin 8 → ℝ) (k : Fin 8) (t : ℝ) :
    ∃ i, i ≠ k ∧ gapAhead v k t = Int.fract ((v i - v k) * t) := by
  obtain ⟨i, hi, h⟩ := Finset.exists_mem_eq_inf' (erase_nonempty k) (fun i => Int.fract ((v i - v k) * t))
  exact ⟨i, (Finset.mem_erase.mp hi).1, h⟩

#print axioms gapAhead_attained

/-- The gap behind is the backward distance to an actual runner (the next one behind). -/
theorem gapBehind_attained (v : Fin 8 → ℝ) (k : Fin 8) (t : ℝ) :
    ∃ i, i ≠ k ∧ gapBehind v k t = Int.fract ((v k - v i) * t) := by
  obtain ⟨i, hi, h⟩ := Finset.exists_mem_eq_inf' (erase_nonempty k) (fun i => Int.fract ((v k - v i) * t))
  exact ⟨i, (Finset.mem_erase.mp hi).1, h⟩

#print axioms gapBehind_attained

/-- One runner, both directions: `1/8 ≤ ‖x‖` iff the forward distance `fract x` and the backward distance
`fract (-x)` are both at least `1/8`.  At `fract x = 0` both sides fail; otherwise `fract (-x) = 1 - fract x`. -/
theorem clear_iff_fract_both (x : ℝ) :
    (1 / 8 : ℝ) ≤ distInt x ↔ 1 / 8 ≤ Int.fract x ∧ 1 / 8 ≤ Int.fract (-x) := by
  rw [Fresh.Localisation.clear_iff_fract]
  by_cases h0 : Int.fract x = 0
  · rw [h0]
    constructor <;> rintro ⟨h, _⟩ <;> norm_num at h
  · rw [Int.fract_neg h0]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

#print axioms clear_iff_fract_both

/-- **v9 Theorem 1.**  Runner `k` is isolated at `t` iff both flanking gaps are at least `1/8`.
Provenance: v9 §1 Theorem 1 / P§2; the existing repo states isolation directly through `‖·‖` and sorts positions
(`grid_of_pairwise`); this unsorted form was written here. -/
theorem isolatedAt_iff_gaps (v : Fin 8 → ℝ) (k : Fin 8) (t : ℝ) :
    IsolatedAt v k t ↔ (1 / 8 : ℝ) ≤ gapAhead v k t ∧ (1 / 8 : ℝ) ≤ gapBehind v k t := by
  unfold IsolatedAt gapAhead gapBehind
  rw [Finset.le_inf'_iff, Finset.le_inf'_iff]
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  have hneg : ∀ i, -((v i - v k) * t) = (v k - v i) * t := fun i => by ring
  constructor
  · intro h
    refine ⟨fun i hi => ((clear_iff_fract_both _).mp (h i hi)).1, fun i hi => ?_⟩
    rw [← hneg]
    exact ((clear_iff_fract_both _).mp (h i hi)).2
  · rintro ⟨h1, h2⟩ i hi
    rw [clear_iff_fract_both, hneg]
    exact ⟨h1 i hi, h2 i hi⟩

#print axioms isolatedAt_iff_gaps

/-! ## (2) Symmetry and Corollary 3 -/

/-- Circle distance between two runners is symmetric: `distInt (-x) = distInt x`. -/
theorem pairDist_symm (v : Fin 8 → ℝ) (i k : Fin 8) (t : ℝ) :
    distInt ((v k - v i) * t) = distInt ((v i - v k) * t) := by
  rw [show (v k - v i) * t = -((v i - v k) * t) by ring, Fresh.Localisation.distInt_neg]

#print axioms pairDist_symm

/-- **Lonely symmetry.**  If `k` is isolated at `t`, every other runner `i` is at circle distance at least `1/8`
from `k`, read from either side: `k` does not crowd `i` either.  Proof: symmetry of circle distance. -/
theorem lonely_symmetry {v : Fin 8 → ℝ} {k : Fin 8} {t : ℝ} (h : IsolatedAt v k t) :
    ∀ i, i ≠ k → (1 / 8 : ℝ) ≤ distInt ((v i - v k) * t) ∧ (1 / 8 : ℝ) ≤ distInt ((v k - v i) * t) :=
  fun i hi => ⟨h i hi, by rw [pairDist_symm]; exact h i hi⟩

#print axioms lonely_symmetry

/-- If every runner other than `m` is isolated at `t`, then `m` is isolated at `t`: each `i ≠ m` being isolated
puts `m` at distance at least `1/8` from `i`, and the distance is symmetric. -/
theorem isolated_of_all_others {v : Fin 8 → ℝ} {t : ℝ} (m : Fin 8)
    (h : ∀ k, k ≠ m → IsolatedAt v k t) : IsolatedAt v m t := by
  intro i hi
  rw [← pairDist_symm]
  exact h i hi m (Ne.symm hi)

#print axioms isolated_of_all_others

/-- Seven runners isolated at `t` (all but `m`) make the eighth isolated: global isolation. -/
theorem global_of_seven {v : Fin 8 → ℝ} {t : ℝ} (m : Fin 8)
    (h : ∀ k, k ≠ m → IsolatedAt v k t) : GloballyIsolatedAt v t := by
  intro k
  by_cases hk : k = m
  · subst hk; exact isolated_of_all_others k h
  · exact h k hk

#print axioms global_of_seven

/-- **v9 Corollary 3.**  The number of runners isolated at one instant is never exactly seven: no runner `m` is
non-isolated while the other seven are isolated.  Stated as "all but one" (the complement of a single runner), so
no cardinality step is used. -/
theorem not_exactly_seven (v : Fin 8 → ℝ) (t : ℝ) :
    ¬ ∃ m : Fin 8, ¬ IsolatedAt v m t ∧ ∀ k, k ≠ m → IsolatedAt v k t := by
  rintro ⟨m, hm, h⟩
  exact hm (isolated_of_all_others m h)

#print axioms not_exactly_seven

/-! ## (3) Global isolation is the regular octagon (v9 Theorem 2)

The forward direction uses `Fresh.octagon` and so INHERITS its **[PROVISIONAL: counting tool]** step (an injective
`Fin 8 → Fin 8` is onto; supports "every bin is occupied"), tagged at that step in `Fresh/Grid.lean`. -/

/-- **v9 Theorem 2.**  All eight runners are isolated at `t` iff the positions relative to runner `0` are whole
eighths `w j / 8` whose residues mod 8 are pairwise distinct: the eight runners stand on the eight distinct vertices
of a regular octagon.  [PROVISIONAL: counting tool] inherited from `Fresh.octagon` (forward direction only).
Provenance: `grid_of_pairwise`, `pos_eq_multiple`, `not_dvd_of_sep` (`ConstructionN/Integrality.lean`); proof here
written from `Fresh.octagon` and `Fresh.distInt_int_div_eight`. -/
theorem globallyIsolatedAt_iff_octagon (v : Fin 8 → ℝ) (t : ℝ) :
    GloballyIsolatedAt v t ↔
      ∃ w : Fin 8 → ℤ, (∀ j, (v j - v 0) * t = (w j : ℝ) / 8) ∧ Function.Injective (fun j => w j % 8) := by
  constructor
  · intro hiso
    have hsep : ∀ i j, i ≠ j → (1 / 8 : ℝ) ≤ distInt (v i * t - v j * t) := fun i j h => by
      rw [← sub_mul]; exact hiso j i h
    -- [PROVISIONAL: counting tool] inherited: `Fresh.octagon` (every bin occupied); supports integrality of `w`.
    have hoct := Fresh.octagon (fun i => v i * t) hsep
    choose w hw using fun j => hoct j 0
    have hw' : ∀ j, (v j - v 0) * t = (w j : ℝ) / 8 := fun j => by rw [sub_mul]; exact hw j
    refine ⟨w, hw', ?_⟩
    intro j j' hjj
    by_contra hne
    have h := hiso j' j hne
    have hd : (v j - v j') * t = ((w j - w j' : ℤ) : ℝ) / 8 := by
      have h1 := hw' j
      have h2 := hw' j'
      push_cast
      linarith
    have h8 : (8 : ℤ) ∣ w j - w j' := Int.ModEq.dvd (show Int.ModEq 8 _ _ from hjj.symm)
    rw [hd, Fresh.distInt_int_div_eight_of_dvd h8] at h
    norm_num at h
  · rintro ⟨w, hw, hinj⟩ k i hik
    have hd : (v i - v k) * t = ((w i - w k : ℤ) : ℝ) / 8 := by
      have h1 := hw i
      have h2 := hw k
      push_cast
      linarith
    rw [hd]
    apply Fresh.distInt_int_div_eight
    intro h8
    exact hik (hinj (Int.ModEq.eq (Int.modEq_of_dvd h8).symm))

#print axioms globallyIsolatedAt_iff_octagon

/-- The circle distance of a whole number of eighths is a whole number of eighths. -/
theorem distInt_eighths (z : ℤ) : ∃ n : ℤ, distInt ((z : ℝ) / 8) = (n : ℝ) / 8 := by
  unfold distInt
  refine ⟨|z - 8 * round ((z : ℝ) / 8)|, ?_⟩
  push_cast
  rw [show (z : ℝ) / 8 - (round ((z : ℝ) / 8) : ℝ) = ((z : ℝ) - 8 * (round ((z : ℝ) / 8) : ℝ)) / 8 by ring,
    abs_div]
  norm_num

#print axioms distInt_eighths

/-- **Corollary of Theorem 2.**  At a global isolation the circle distance between any two distinct runners is a
whole number `n` of eighths, with `1 ≤ n ≤ 4`.  [PROVISIONAL: counting tool] inherited from `Fresh.octagon`. -/
theorem globallyIsolated_pairDist_eighths {v : Fin 8 → ℝ} {t : ℝ} (hiso : GloballyIsolatedAt v t)
    (i j : Fin 8) (hij : i ≠ j) :
    ∃ n : ℤ, distInt ((v i - v j) * t) = (n : ℝ) / 8 ∧ 1 ≤ n ∧ n ≤ 4 := by
  obtain ⟨w, hw, -⟩ := (globallyIsolatedAt_iff_octagon v t).mp hiso
  have hd : (v i - v j) * t = ((w i - w j : ℤ) : ℝ) / 8 := by
    have h1 := hw i
    have h2 := hw j
    push_cast
    linarith
  obtain ⟨n, hn⟩ := distInt_eighths (w i - w j)
  rw [hd]
  refine ⟨n, hn, ?_, ?_⟩
  · have h := hiso j i hij
    rw [hd, hn] at h
    have : (1 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  · have h := Fresh.Localisation.distInt_le_half (((w i - w j : ℤ) : ℝ) / 8)
    rw [hn] at h
    have : (n : ℝ) ≤ 4 := by linarith
    exact_mod_cast this

#print axioms globallyIsolated_pairDist_eighths

/-! ## (4) Theorem 10 on an integer arrangement -/

/-- **Bridge of v9 Theorem 10 to arrangements.**  For integer speeds `z j` (positive, pairwise distinct), a flank
`e = |z i₀ - z k|` of subject `k`, and a lap `n`, the subject is isolated at the opening `(n + 1/8)/e` iff every other
runner's disparity `|z i - z k|` satisfies `e ≤ |z i - z k| (8n+1) mod 8e ≤ 7e`.
Only injectivity is used (it makes `e > 0`); positivity is carried as the arrangement hypothesis (rule 5) and is not
needed by the proof.  Provenance: P§6 certificate / `Flanks.clear_of_residue_band` (existing repo); here it is
`Fresh.Localisation.certificate_clear_iff` plus the sign lemma `distInt_abs_mul`. -/
theorem integer_flank_isolated_iff (z : Fin 8 → ℤ) (_hpos : ∀ j, 0 < z j) (hinj : Function.Injective z)
    (k i₀ : Fin 8) (hi₀ : i₀ ≠ k) (e : ℤ) (he : e = |z i₀ - z k|) (n : ℕ) :
    IsolatedAt (fun j => (z j : ℝ)) k (((n : ℝ) + 1 / 8) / e) ↔
      ∀ i, i ≠ k → e ≤ (|z i - z k| * (8 * n + 1)) % (8 * e) ∧
        (|z i - z k| * (8 * n + 1)) % (8 * e) ≤ 7 * e := by
  have he0 : 0 < e := by
    rw [he]
    apply abs_pos.mpr
    intro h
    exact hi₀ (hinj (sub_eq_zero.mp h))
  unfold IsolatedAt
  refine forall₂_congr fun i _ => ?_
  rw [← Fresh.Localisation.certificate_clear_iff _ e he0 n, ← Fresh.Localisation.distInt_abs_mul]
  push_cast
  rfl

#print axioms integer_flank_isolated_iff

end Fresh.Octagon
