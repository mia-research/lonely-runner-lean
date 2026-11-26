import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Cascade
import Fresh.CascadeLandingG
import Fresh.SelfMoverCommon
import Fresh.SelfMoverCommon2
import Fresh.SelfMoverAllCommon
import Fresh.SelfMoverOutside

/-!
# The subject moving: the leaf lemmas of the all-positions theorem

Written 2026-10-22.  New file.  Each leaf takes one configuration's cascade statement (an `∃ T` assembly, or a `FirstIso` for the far outside cases)
and returns the position-level conclusion `∃ a ∈ disparitySet (oneMover c x k) k, Lands (oneMover c x k) k a`.  Grades: [L].
-/

open Classical

namespace Fresh.OneMover

open Fresh

theorem leaf (c x δ : ℝ) (i0 : ℕ) (hi0 : i0 < 8) (s : ℝ) (hs : s = 1 ∨ s = -1) (K : Fin 8)
    (hk : (⟨i0, hi0⟩ : Fin 8) ≠ K) (hδ : 0 < δ) (hxe : x = c + (i0 : ℝ) + s * δ)
    (h : ∃ T : ℝ, 0 < T ∧ (∃ seq : ℕ → ℝ, seq 0 = 1 / (8 * δ) ∧
      (∀ n, IsMove (disparitySet (selfV c i0 s δ K) K) (seq n) (seq (n + 1))) ∧ ∃ N, seq (N + 1) = seq N) ∧
      ∀ seq : ℕ → ℝ, seq 0 = 1 / (8 * δ) →
        (∀ n, IsMove (disparitySet (selfV c i0 s δ K) K) (seq n) (seq (n + 1))) → ∀ N, seq (N + 1) = seq N → seq N = T) :
    ∃ a ∈ disparitySet (oneMover c x K) K, Lands (oneMover c x K) K a := by
  rw [selfV_eq c i0 s δ x K hxe]
  exact ⟨δ, delta_mem c i0 hi0 s δ hs K hk hδ, h⟩

/-- The extreme runner `0` moves below the AP. -/
theorem leaf_out0 (c x δ : ℝ) (hδ : 0 < δ) (hxe : x = c + ((0 : ℕ) : ℝ) + (-1 : ℝ) * δ) :
    ∃ a ∈ disparitySet (oneMover c x (⟨0, by norm_num⟩ : Fin 8)) (⟨0, by norm_num⟩ : Fin 8),
      Lands (oneMover c x (⟨0, by norm_num⟩ : Fin 8)) (⟨0, by norm_num⟩ : Fin 8) a := by
  rw [selfV_eq c 0 (-1 : ℝ) δ x _ hxe]
  have hF := outside_below_k0 c δ hδ
  have ha : (1 + δ) ∈ disparitySet (selfV c 0 (-1 : ℝ) δ (⟨0, by norm_num⟩ : Fin 8)) (⟨0, by norm_num⟩ : Fin 8) := by
    refine Finset.mem_image.mpr ⟨⟨1, by norm_num⟩, Finset.mem_erase.mpr ⟨by decide, Finset.mem_univ _⟩, ?_⟩
    rw [selfV_diff c 0 (-1 : ℝ) δ _ ⟨1, by norm_num⟩ (by decide)]
    simp only [Nat.cast_one, Nat.cast_zero]
    rw [abs_of_pos (by linarith)]; ring
  exact ⟨1 + δ, ha, lands_of_first _ _ _ _ ha (by positivity) hF⟩

/-- The extreme runner `7` moves above the AP. -/
theorem leaf_out7 (c x δ : ℝ) (hδ : 0 < δ) (hxe : x = c + ((7 : ℕ) : ℝ) + (1 : ℝ) * δ) :
    ∃ a ∈ disparitySet (oneMover c x (⟨7, by norm_num⟩ : Fin 8)) (⟨7, by norm_num⟩ : Fin 8),
      Lands (oneMover c x (⟨7, by norm_num⟩ : Fin 8)) (⟨7, by norm_num⟩ : Fin 8) a := by
  rw [selfV_eq c 7 (1 : ℝ) δ x _ hxe]
  have hF := outside_above_k7 c δ hδ
  have ha : (1 + δ) ∈ disparitySet (selfV c 7 (1 : ℝ) δ (⟨7, by norm_num⟩ : Fin 8)) (⟨7, by norm_num⟩ : Fin 8) := by
    refine Finset.mem_image.mpr ⟨⟨6, by norm_num⟩, Finset.mem_erase.mpr ⟨by decide, Finset.mem_univ _⟩, ?_⟩
    rw [selfV_diff c 7 (1 : ℝ) δ _ ⟨6, by norm_num⟩ (by decide)]
    simp only [Nat.cast_ofNat]
    rw [abs_of_neg (by linarith)]; ring
  exact ⟨1 + δ, ha, lands_of_first _ _ _ _ ha (by positivity) hF⟩

/-- Below the AP, not the extreme runner, `δ ≥ 7/6`. -/
theorem leaf_far0 (c x δ : ℝ) (K : Fin 8) (hk : (K : ℕ) ≠ 0) (hδ : (7 : ℝ) / 6 ≤ δ)
    (hxe : x = c + ((0 : ℕ) : ℝ) + (-1 : ℝ) * δ) :
    ∃ a ∈ disparitySet (oneMover c x K) K, Lands (oneMover c x K) K a := by
  have hδp : 0 < δ := by linarith
  rw [selfV_eq c 0 (-1 : ℝ) δ x K hxe]
  have hk' : (⟨0, by norm_num⟩ : Fin 8) ≠ K := fun h => hk (by rw [← h])
  have ha := delta_mem c 0 (by norm_num) (-1 : ℝ) δ (Or.inr rfl) K hk' hδp
  exact ⟨δ, ha, lands_of_first _ _ _ _ ha (by positivity) (outside_below_k_ne0 c δ K hk hδ)⟩

/-- Above the AP, not the extreme runner, `δ ≥ 7/6`. -/
theorem leaf_far7 (c x δ : ℝ) (K : Fin 8) (hk : (K : ℕ) ≠ 7) (hδ : (7 : ℝ) / 6 ≤ δ)
    (hxe : x = c + ((7 : ℕ) : ℝ) + (1 : ℝ) * δ) :
    ∃ a ∈ disparitySet (oneMover c x K) K, Lands (oneMover c x K) K a := by
  have hδp : 0 < δ := by linarith
  rw [selfV_eq c 7 (1 : ℝ) δ x K hxe]
  have hk' : (⟨7, by norm_num⟩ : Fin 8) ≠ K := fun h => hk (by rw [← h])
  have ha := delta_mem c 7 (by norm_num) (1 : ℝ) δ (Or.inl rfl) K hk' hδp
  exact ⟨δ, ha, lands_of_first _ _ _ _ ha (by positivity) (outside_above_k_ne7 c δ K hk hδ)⟩

#print axioms leaf
#print axioms leaf_out0
#print axioms leaf_out7
#print axioms leaf_far0
#print axioms leaf_far7

end Fresh.OneMover
