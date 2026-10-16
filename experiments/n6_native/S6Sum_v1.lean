import LonelyRunner.LRC.Spec.OrderSixEightNativeN

/-!
# §6 with the sum relation `v₄ = v₃ + v₁` (n6_native, E97)

At a meeting time `T = k/D` runners 2, 3 are on the subject and runner 4 reads what runner 1 reads, `p` (because
`v₄ T = v₃ T + v₁ T`). After `T`, on the instants where runner 3 reads `x₃ ∈ [7/6 − p, 5/6]`: runner 4 reads `x₃ + p + v₁s`,
one lap on and in the band; runner 1 reads `p + v₁ s ≤ 5/6` when `p ≤ (5/6)(1 − v₁/v₃)`; runner 2 reads `x₃ · v₂/v₃ ≥ x₃/2`;
and runner 5 is folded when the stretch `(p − 1/3)/v₃` is at least `1/(3v₅)`.
-/

namespace N6Native
open LRC.S7Native LRC.S8Native

set_option maxHeartbeats 1000000 in
theorem s6_sum_window {v1 v2 v3 v5 T p : ℝ} {N1 N2 N3 : ℤ} (h1 : 0 < v1) (h2 : 0 < v2) (h23 : v2 ≤ v3)
    (h2half : v3 ≤ 2 * v2) (h5 : 0 < v5)
    (hT1 : v1 * T = N1 + p) (hT2 : v2 * T = N2) (hT3 : v3 * T = N3)
    (hplo : 1 / 3 + v3 / (3 * v5) ≤ p) (hphi : p ≤ 5 / 6 * (1 - v1 / v3)) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist ((v3 + v1) * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have h3 : 0 < v3 := lt_of_lt_of_le h2 h23
  have hr : v1 / v3 * v3 = v1 := by field_simp
  -- the stretch: s ∈ [(7/6 - p)/v3, 5/(6 v3)]
  have hlen : 1 / (3 * v5) ≤ 5 / (6 * v3) - (7 / 6 - p) / v3 := by
    have e : 5 / (6 * v3) - (7 / 6 - p) / v3 = (p - 1 / 3) / v3 := by field_simp; ring
    rw [e, div_le_div_iff₀ (by positivity) h3]
    have : v3 / (3 * v5) * (3 * v5) = v3 := by field_simp
    nlinarith
  obtain ⟨t', ht1, ht2, c5⟩ := LRC.S8Native.fold_one (J₀ := T + (7 / 6 - p) / v3)
    (ℓ := 5 / (6 * v3) - (7 / 6 - p) / v3) h5 hlen
  set s := t' - T with hs
  have hsa : (7 / 6 - p) / v3 ≤ s := by rw [hs]; linarith
  have hsb : s ≤ 5 / (6 * v3) := by rw [hs]; linarith
  have x3a : 7 / 6 - p ≤ v3 * s := by rw [div_le_iff₀ h3] at hsa; linarith
  have x3b : v3 * s ≤ 5 / 6 := by rw [le_div_iff₀ (by positivity)] at hsb; linarith
  have hp56 : p ≤ 5 / 6 := by
    have : 0 ≤ v1 / v3 := by positivity
    nlinarith
  have hs0 : 0 ≤ s := by
    have : 0 ≤ (7 / 6 - p) / v3 := div_nonneg (by linarith) h3.le
    linarith
  have x1b : v1 * s ≤ 5 / 6 * (v1 / v3) := by
    have : v1 * s = v1 / v3 * (v3 * s) := by field_simp
    rw [this]; have : 0 ≤ v1 / v3 := by positivity
    nlinarith
  have x1a : 0 ≤ v1 * s := mul_nonneg h1.le hs0
  have ht : t' = T + s := by rw [hs]; ring
  refine ⟨t', ?_, ?_, ?_, ?_, c5⟩
  · rw [ht, mul_add, hT1]; apply clear_of_band (p := N1) <;> nlinarith
  · have x2a : 1 / 6 ≤ v2 * s := by
      have : v3 * s ≤ 2 * (v2 * s) := by nlinarith
      linarith
    have x2b : v2 * s ≤ 5 / 6 := by nlinarith
    rw [ht, mul_add, hT2]; apply clear_of_band (p := N2) <;> linarith
  · rw [ht, mul_add, hT3]; apply clear_of_band (p := N3) <;> linarith
  · rw [ht, show (v3 + v1) * (T + s) = v3 * T + v1 * T + (v3 * s + v1 * s) by ring, hT1, hT3]
    apply clear_of_band (p := N3 + N1 + 1)
    · push_cast; linarith
    · push_cast; nlinarith

end N6Native

#print axioms N6Native.s6_sum_window
