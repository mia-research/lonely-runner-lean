import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Cascade
import Fresh.SelfMoverAllCommon

/-!
# From the cascade statement with an explicit landing instant to `Lands`

Written 2026-10-22.  New file.  Grades: [L].
-/

open Classical

namespace Fresh.OneMover

open Fresh

theorem lands_of_cascade (v : Fin 8 → ℝ) (k : Fin 8) (a T : ℝ) (hpos : ∀ d ∈ disparitySet v k, 0 < d) (ha : 0 < a)
    (h : (∃ seq : ℕ → ℝ, seq 0 = 1 / (8 * a) ∧ (∀ n, IsMove (disparitySet v k) (seq n) (seq (n + 1))) ∧ ∃ N, seq (N + 1) = seq N) ∧
      ∀ seq : ℕ → ℝ, seq 0 = 1 / (8 * a) → (∀ n, IsMove (disparitySet v k) (seq n) (seq (n + 1))) →
        ∀ N, seq (N + 1) = seq N → seq N = T) : Lands v k a := by
  obtain ⟨⟨seq, h0, hmv, N, hN⟩, hall⟩ := h
  have hT : seq N = T := hall seq h0 hmv N hN
  have hmono : ∀ n, seq 0 ≤ seq n := by
    intro n
    induction n with
    | zero => exact le_refl _
    | succ n ih => exact le_trans ih (Fresh.Cascade.le_of_isMove hpos (hmv n))
  have hpos0 : 0 < seq 0 := by rw [h0]; positivity
  exact ⟨T, by rw [← hT]; exact lt_of_lt_of_le hpos0 (hmono N), ⟨seq, h0, hmv, N, hN⟩, hall⟩

#print axioms lands_of_cascade

end Fresh.OneMover
