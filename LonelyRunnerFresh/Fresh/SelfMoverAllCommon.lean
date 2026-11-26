import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Cascade
import Fresh.CascadeLandingG
import Fresh.SelfMoverCommon
import Fresh.SelfMoverCommon2

/-!
# The subject moving: shared statement and links for the all-positions theorem

Written 2026-10-22.  New file.  `Lands v k a` is the cascade statement for the arrangement `v` and subject `k` from the start `1/(8a)`:
a first isolation instant `T > 0` exists, the cascade from `1/(8a)` reaches a fixed point, and every fixed point is `T`.  Grades: [L].
-/

open Classical

namespace Fresh.OneMover

open Fresh

/-- The cascade statement from the start `1/(8a)`. -/
-- STANDING: DEFINITION
def Lands (v : Fin 8 → ℝ) (k : Fin 8) (a : ℝ) : Prop :=
  ∃ T : ℝ, 0 < T ∧ (∃ seq : ℕ → ℝ, seq 0 = 1 / (8 * a) ∧
      (∀ n, IsMove (disparitySet v k) (seq n) (seq (n + 1))) ∧ ∃ N, seq (N + 1) = seq N) ∧
    ∀ seq : ℕ → ℝ, seq 0 = 1 / (8 * a) →
      (∀ n, IsMove (disparitySet v k) (seq n) (seq (n + 1))) → ∀ N, seq (N + 1) = seq N → seq N = T

/-- From a first isolation instant and any member `a` of the disparity set to the cascade statement. -/
theorem lands_of_first (v : Fin 8 → ℝ) (k : Fin 8) (a T : ℝ) (ha : a ∈ disparitySet v k) (hT : 0 < T)
    (hF : FirstIso v k T) : Lands v k a := by
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
  have hfirst : IsFirst (disparitySet v k) T :=
    ⟨(Fresh.Cascade.isolatedAt_iff_lonelyAt v k T).1 hF.1,
      fun s' hs' hl => hF.2 s' hs' ((Fresh.Cascade.isolatedAt_iff_lonelyAt v k s').2 hl)⟩
  exact ⟨T, hT, cascade_landsG hpos ha hT hfirst⟩

/-- The nearest runner's reading `δ` is a disparity. -/
theorem delta_mem (c : ℝ) (i0 : ℕ) (hi0 : i0 < 8) (s δ : ℝ) (hs : s = 1 ∨ s = -1) (k : Fin 8)
    (hk : (⟨i0, hi0⟩ : Fin 8) ≠ k) (hδ : 0 < δ) : δ ∈ disparitySet (selfV c i0 s δ k) k := by
  refine Finset.mem_image.mpr ⟨⟨i0, hi0⟩, Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩, ?_⟩
  rw [selfV_diff c i0 s δ k ⟨i0, hi0⟩ hk]
  simp only [sub_self, zero_sub]
  rcases hs with rfl | rfl <;> simp [abs_of_pos hδ]

theorem selfV_eq (c : ℝ) (i0 : ℕ) (s δ x : ℝ) (k : Fin 8) (hx : x = c + (i0 : ℝ) + s * δ) :
    oneMover c x k = selfV c i0 s δ k := by
  rw [selfV, hx]

/-- The conclusion shape of the generated assemblies is `Lands` at `a = δ`. -/
theorem lands_of_conc (v : Fin 8 → ℝ) (k : Fin 8) (a : ℝ)
    (h : ∃ T : ℝ, 0 < T ∧ (∃ seq : ℕ → ℝ, seq 0 = 1 / (8 * a) ∧
      (∀ n, IsMove (disparitySet v k) (seq n) (seq (n + 1))) ∧ ∃ N, seq (N + 1) = seq N) ∧
      ∀ seq : ℕ → ℝ, seq 0 = 1 / (8 * a) →
        (∀ n, IsMove (disparitySet v k) (seq n) (seq (n + 1))) → ∀ N, seq (N + 1) = seq N → seq N = T) :
    Lands v k a := h

#print axioms lands_of_first
#print axioms delta_mem
#print axioms selfV_eq

end Fresh.OneMover
