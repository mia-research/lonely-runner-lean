import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.LonelyCells
import Fresh.Admissible
import Fresh.EightResidualLink

/-!
# The resolution rule on real speeds: what the cap becomes

Written 2026-10-25 (owner: "Can we expand resolutioncap8=64 to real instead of integers?").  New file.  The old rule `ResolutionClears8 S D j` (integer disparity set `S`, integer resolution `D`, `D ≤ 64`) says every
reading is clear at the instant `(8j + 1)/(8D)`.  Its real form `ResolutionClearsR v k D j` takes any real `D > 0` and `j : ℕ`.
* `resolution_nat_iff`: for an integer disparity set the old rule is the real rule at an integer `D` (it uses `nat_clear_iff`).
* `resolutionR_iff_isolation`: with `D` ranging over all positive reals the rule is EQUIVALENT to `Isolation v k` (take `j = 0`, `D = 1/(8t)`): lifting the cap to the reals does not give a rule, it gives the conjecture.  So the cap `D ≤ 64` is a finite search
  budget of the integer setting, not a mathematical feature.
* `isolation_flank`: every isolation implies an isolation at a FLANK OPENING `(n + 1/8)/x`, `x` one of the subject's own disparities (the left end of its first cell, `LonelyCells.cell_left_end_is_opening`).  So the resolution `D` may be restricted
  to the seven disparities of the subject: nothing is lost, and the integer `D ≤ 64` that is not a disparity is not needed.  What is left of the cap is a bound on the lap `n`.
Grades: [L].  Not claimed: a bound on the lap `n` (that is the owed `PathLonelyBound` / `WindowBound`).
-/

open Classical

namespace Fresh.ResolutionReal

open Fresh Fresh.Admissible Fresh.EightResidualLink

/-- The resolution rule on real speeds: every reading is clear at `(8j + 1)/(8D)`. -/
-- STANDING: DEFINITION
def ResolutionClearsR (v : Fin 8 → ℝ) (k : Fin 8) (D : ℝ) (j : ℕ) : Prop :=
  ∀ i, i ≠ k → (1 / 8 : ℝ) ≤ distInt (|v i - v k| * (((8 * j + 1 : ℕ) : ℝ) / (8 * D)))

theorem resolution_nat_iff {v : Fin 8 → ℝ} {k : Fin 8} {S : Finset ℕ} (hS : HasDisp v k S) {D : ℕ} (hD : 0 < D) (j : ℕ) :
    ResolutionClears8 S D j ↔ ResolutionClearsR v k (D : ℝ) j := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  constructor
  · intro h i hik
    have hmem : |v i - v k| ∈ disparitySet v k := Finset.mem_image.2 ⟨i, Finset.mem_erase.2 ⟨hik, Finset.mem_univ _⟩, rfl⟩
    obtain ⟨d, hd, hde⟩ := (hS _).1 hmem
    rw [← hde]
    have := (nat_clear_iff D (d * (8 * j + 1)) hD).2 (h d hd)
    have e : (d : ℝ) * (((8 * j + 1 : ℕ) : ℝ) / (8 * D)) = ((d * (8 * j + 1) : ℕ) : ℝ) * (1 / (8 * (D : ℝ))) := by
      push_cast; field_simp
    rw [e]; exact this
  · intro h d hd
    have hmem : (d : ℝ) ∈ disparitySet v k := (hS _).2 ⟨d, hd, rfl⟩
    obtain ⟨i, hi, hie⟩ := Finset.mem_image.1 hmem
    have hik : i ≠ k := (Finset.mem_erase.1 hi).1
    have := h i hik
    rw [hie] at this
    have e : (d : ℝ) * (((8 * j + 1 : ℕ) : ℝ) / (8 * D)) = ((d * (8 * j + 1) : ℕ) : ℝ) * (1 / (8 * (D : ℝ))) := by
      push_cast; field_simp
    rw [e] at this
    exact (nat_clear_iff D (d * (8 * j + 1)) hD).1 this

theorem resolutionR_iff_isolation (v : Fin 8 → ℝ) (k : Fin 8) :
    (∃ D : ℝ, 0 < D ∧ ∃ j : ℕ, ResolutionClearsR v k D j) ↔ Isolation v k := by
  constructor
  · rintro ⟨D, hD, j, h⟩
    refine ⟨((8 * j + 1 : ℕ) : ℝ) / (8 * D), by positivity, fun i hik => ?_⟩
    have := h i hik
    rwa [Fresh.Localisation.distInt_abs_mul] at this
  · rintro ⟨t, ht, hiso⟩
    refine ⟨1 / (8 * t), by positivity, 0, fun i hik => ?_⟩
    have e : (((8 * 0 + 1 : ℕ) : ℝ) / (8 * (1 / (8 * t)))) = t := by
      push_cast; field_simp
    rw [e, Fresh.Localisation.distInt_abs_mul]
    exact hiso i hik

theorem isolation_flank {v : Fin 8 → ℝ} (hv : Function.Injective v) {k : Fin 8} (h : Isolation v k) :
    ∃ x ∈ disparitySet v k, ∃ n : ℕ, IsolatedAt v k (((n : ℝ) + 1 / 8) / x) := by
  obtain ⟨t, ht, hiso⟩ := h
  have hpos : ∀ d ∈ disparitySet v k, 0 < d := by
    intro d hd
    obtain ⟨i, hik, rfl⟩ := Fresh.Localisation.mem_disparitySet.1 hd
    exact abs_pos.2 (sub_ne_zero.2 (fun h => hik (hv h)))
  have hne : (disparitySet v k).Nonempty := by
    obtain ⟨i, hi⟩ := exists_ne8 k
    exact ⟨_, Fresh.Localisation.mem_disparitySet.2 ⟨i, hi, rfl⟩⟩
  have hl : t ∈ LonelyCells.lonelySet (disparitySet v k) := (Fresh.Localisation.isolatedAt_iff v k t).1 hiso
  obtain ⟨x, hx, y, hy, hc, _, _⟩ := LonelyCells.cell_of_lonely hpos hne ht hl
  obtain ⟨x', hx', n, hu, _, _, _⟩ := LonelyCells.cell_left_end_is_opening hpos hc
  refine ⟨x', hx', n, ?_⟩
  have hlu : (Localisation.lastOpening x t) ∈ LonelyCells.lonelySet (disparitySet v k) := hc.2.2.1 ⟨le_rfl, hc.2.1⟩
  rw [← hu]
  exact (Fresh.Localisation.isolatedAt_iff v k _).2 hlu

theorem flank_iff_isolation {v : Fin 8 → ℝ} (hv : Function.Injective v) (k : Fin 8) :
    (∃ x ∈ disparitySet v k, ∃ n : ℕ, IsolatedAt v k (((n : ℝ) + 1 / 8) / x)) ↔ Isolation v k := by
  constructor
  · rintro ⟨x, hx, n, hiso⟩
    have hxpos : 0 < x := by
      obtain ⟨i, hik, rfl⟩ := Fresh.Localisation.mem_disparitySet.1 hx
      exact abs_pos.2 (sub_ne_zero.2 (fun h => hik (hv h)))
    exact ⟨_, by positivity, hiso⟩
  · exact isolation_flank hv

#print axioms resolution_nat_iff
#print axioms resolutionR_iff_isolation
#print axioms isolation_flank
#print axioms flank_iff_isolation

end Fresh.ResolutionReal
