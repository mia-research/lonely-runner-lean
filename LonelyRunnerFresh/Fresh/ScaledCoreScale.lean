import Mathlib
import Fresh.Localisation

/-!
# Scaling a core with a real extra reading

Written 2026-10-29.  New file.  If a set `S` of positive readings together with ANY real `y > 0` has a common `1/8`-clear instant, then so does `m S` (every reading multiplied by a positive real `m`) together with ANY real `x > 0`:
take `y = x / m` and the instant `t / m`.  So a core certified once against every real extra reading is certified at every multiple.  Grade [L].
-/

namespace Fresh.ScaledCoreScale

open Fresh

theorem scale {S : Finset ℝ}
    (H : ∀ y : ℝ, 0 < y → ∃ t : ℝ, 0 < t ∧ (∀ s ∈ S, (1 / 8 : ℝ) ≤ distInt (s * t)) ∧ (1 / 8 : ℝ) ≤ distInt (y * t))
    {m : ℝ} (hm : 0 < m) {x : ℝ} (hx : 0 < x) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ S, (1 / 8 : ℝ) ≤ distInt ((m * s) * t)) ∧ (1 / 8 : ℝ) ≤ distInt (x * t) := by
  obtain ⟨t, ht, hS, hy⟩ := H (x / m) (div_pos hx hm)
  refine ⟨t / m, div_pos ht hm, fun s hs => ?_, ?_⟩
  · have : (m * s) * (t / m) = s * t := by field_simp
    rw [this]; exact hS s hs
  · have : x * (t / m) = (x / m) * t := by ring
    rw [this]; exact hy

#print axioms scale

end Fresh.ScaledCoreScale
