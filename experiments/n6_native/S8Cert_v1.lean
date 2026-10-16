import LonelyRunner.LRC.Spec.OrderSixSecSevenNativeN

/-!
# Closed-form window condition for the §8 certificate (n6_native, E85)

`window_two`'s residue condition holds whenever the window is at least `1/(3a) + 2/(3b)`: the largest `m` with
`3 m a < a + b` has `(m + 1/3)/b < 1/(3a) + 2/(3b)`. This makes every window statement of the §8 certificate a
closed-form rational inequality, monotone in each speed.
-/

namespace N6Native
open LRC.S7Native

theorem window_two_simple {a b J₀ ℓ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hℓ : 1 / (3 * a) + 2 / (3 * b) ≤ ℓ) :
    ∃ t : ℝ, J₀ ≤ t ∧ t ≤ J₀ + ℓ ∧ (6 : ℝ)⁻¹ ≤ circDist (a * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (b * t) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  apply window_two ha hab
  · have : 1 / (3 * b) ≤ 2 / (3 * b) := by gcongr; norm_num
    linarith
  · intro m hm
    have key : ((m : ℝ) + 1 / 3) / b ≤ 1 / (3 * a) + 2 / (3 * b) := by
      rw [div_le_iff₀ hb]
      have : (m : ℝ) * (3 * a) < a + b := by linarith
      have e : (1 / (3 * a) + 2 / (3 * b)) * b = b / (3 * a) + 2 / 3 := by field_simp
      rw [e]
      have : (m : ℝ) < (a + b) / (3 * a) := by rw [lt_div_iff₀ (by positivity)]; linarith
      have e2 : (a + b) / (3 * a) = 1 / 3 + b / (3 * a) := by field_simp
      linarith
    linarith

end N6Native

#print axioms N6Native.window_two_simple
