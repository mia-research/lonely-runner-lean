import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Cascade
import Fresh.CascadeLandingG
import Fresh.SelfMoverCommon

/-!
# From the first isolation instant to the cascade, without a bound on `δ`

Written 2026-10-22.  New file.  `selfland_of_first` (SelfMoverCommon) assumes `δ < 1` only to know that every other runner's reading is non-zero.
A reading that is zero cannot be clear at any instant (`distInt 0 = 0`), so non-zeroness follows from the first isolation instant itself; the
bound on `δ` is not needed.  Grades: [L].
-/

open Classical

namespace Fresh.OneMover

open Fresh

theorem selfland_of_first' (c : ℝ) (i0 : ℕ) (hi0 : i0 < 8) (s δ : ℝ) (hs : s = 1 ∨ s = -1) (k : Fin 8)
    (hk : (⟨i0, hi0⟩ : Fin 8) ≠ k) (hδ : 0 < δ) (T : ℝ) (hT : 0 < T)
    (hF : FirstIso (selfV c i0 s δ k) k T) :
    (∃ seq : ℕ → ℝ, seq 0 = 1 / (8 * δ) ∧
      (∀ n, IsMove (disparitySet (selfV c i0 s δ k) k) (seq n) (seq (n + 1))) ∧ ∃ N, seq (N + 1) = seq N) ∧
    ∀ seq : ℕ → ℝ, seq 0 = 1 / (8 * δ) →
      (∀ n, IsMove (disparitySet (selfV c i0 s δ k) k) (seq n) (seq (n + 1))) → ∀ N, seq (N + 1) = seq N → seq N = T := by
  set v := selfV c i0 s δ k with hv
  have hpos : ∀ d ∈ disparitySet v k, 0 < d := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
    have hik : i ≠ k := (Finset.mem_erase.mp hi).1
    apply abs_pos.mpr
    intro h0
    have h1 := hF.1 i hik
    rw [h0, zero_mul] at h1
    have h2 := Fresh.Localisation.distInt_le (0 : ℝ) 0
    simp at h2
    linarith
  have ham : δ ∈ disparitySet v k := by
    refine Finset.mem_image.mpr ⟨⟨i0, hi0⟩, Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩, ?_⟩
    rw [hv, selfV_diff c i0 s δ k ⟨i0, hi0⟩ hk]
    simp only [sub_self, zero_sub]
    rcases hs with rfl | rfl <;> simp [abs_of_pos hδ]
  have hfirst : IsFirst (disparitySet v k) T :=
    ⟨(Fresh.Cascade.isolatedAt_iff_lonelyAt v k T).1 hF.1,
      fun s' hs' hl => hF.2 s' hs' ((Fresh.Cascade.isolatedAt_iff_lonelyAt v k s').2 hl)⟩
  exact cascade_landsG hpos ham hT hfirst

#print axioms selfland_of_first'

end Fresh.OneMover
