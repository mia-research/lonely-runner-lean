import LonelyRunner.LRC.Spec.OrderSixSecFiveNativeK2N
import LonelyRunner.LRC.Spec.OrderSixSecFiveNativeK1LargeN
import LonelyRunner.LRC.Spec.OrderSixSecFiveNativeK1MidN
import LonelyRunner.LRC.Spec.OrderSixSecFiveNativeK1SmallN

/-!
# BHK §5 natively, all cases (n6_native, E105–E115)

§5: `D = v₃ − v₂ ∣ v₁`, `3v₁ < v₃`. With `v₁ = kD`:
* `k ≥ 2` — `S5Large.s5_k2` (pair windows at `j₀`, runner-4 leaves and the step lemma for `α = v₁/v₂ ≤ 1/25`, a
  kernel-checked box tree for `α > 1/25`);
* `k = 1` (`v₃ = v₂ + v₁`) — `S5K1Large.s5k1_large` (`v₂ < 25v₁`: box tree with the two tight-point leaves),
  `S5K1Mid.s5k1_mid` (`25v₁ ≤ v₂ ≤ 50v₁`: box tree), `S6Native.s5k1_small` (`v₂ ≥ 50v₁`: runner-4 leaves, step lemma,
  uniform window, and on the strip `λ ∈ [25/14, 16/5]` an `ivt_box` tree in `(λ, λ₅)` and the runner-5 sweep).
`lonely_5_native` is §5 in the dispatch's form.
-/

namespace LRC.S5Native
open LRC.S7Native LRC.S8Native

/-- **§5 natively, five circle readings.** -/
theorem s5_all {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4) (h45 : v4 < v5)
    (hsmall : 3 * v1 < v3) (hD1 : (v3 - v2) ∣ v1) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have hD0 : 0 < v3 - v2 := by omega
  have hv3 : v3 = v2 + (v3 - v2) := by omega
  obtain ⟨k, hk⟩ := hD1
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hk1 : k = 1 := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, mul_zero] at hk; omega
      · omega
    rw [hk1, mul_one] at hk
    have hv3' : v3 = v2 + v1 := by omega
    rcases Nat.lt_or_ge v2 (25 * v1) with ha | ha
    · exact LRC.S5K1Large.s5k1_large h0 h12 hv3' h34 h45 hsmall ha
    rcases le_or_gt v2 (50 * v1) with hb | hb
    · exact LRC.S5K1Mid.s5k1_mid h0 h12 hv3' h34 h45 hsmall ha hb
    · exact LRC.S6Native.s5k1_small h0 h12 hv3' h34 h45 hsmall hb.le
  · have hD2 : 2 * (v3 - v2) ≤ v1 := by rw [hk]; nlinarith
    exact LRC.S5Large.s5_k2 h0 h12 hv3 hD0 hD2 h34 h45 hsmall

/-- **BHK §5 natively, in the dispatch's form.** -/
theorem lonely_5_native {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3)
    (h34 : v3 < v4) (h45 : v4 < v5) (hsmall : 3 * v1 < v3) (hD1 : (v3 - v2) ∣ v1) :
    ∃ t : ℝ, 0 < t ∧ LRC.OrderSixN.Lonely6 v1 v2 v3 v4 v5 t := by
  obtain ⟨s, a1, a2, a3, a4, a5⟩ := s5_all h0 h12 h23 h34 h45 hsmall hD1
  obtain ⟨m, hm⟩ := exists_nat_gt (-s)
  have key : ∀ v : ℕ, circDist ((v : ℝ) * (s + ((m + 1 : ℕ) : ℝ))) = circDist ((v : ℝ) * s) := by
    intro v
    have e' : (v : ℝ) * (s + ((m + 1 : ℕ) : ℝ)) = (v : ℝ) * s + ((v * (m + 1) : ℕ) : ℤ) := by push_cast; ring
    rw [e', s8_circDist_add_int]
  refine ⟨s + ((m + 1 : ℕ) : ℝ), by push_cast; linarith, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [key, one_div] <;> assumption

end LRC.S5Native
