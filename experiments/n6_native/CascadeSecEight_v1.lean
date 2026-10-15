import LonelyRunner.LRC.Cascade.Flanks

/-!
# BHK §8 in the walk: two exact step rules (observations formalised)

Observed on all §8 sets (`six_s8_step_rule_v1.out`, 0 exceptions): at opening 1 of `v₅` with
`5v₁ < v₅ < 7v₁` the three slowest are clear, and `v₄` is in the way there exactly when `7v₄ > 5v₅`.
-/

namespace CascadeSecEight

open ConstructionN

/-- The slow elements are clear at opening 1 of a fast flank `v₅ ∈ (5v₁, 7v₁)`, when `v₁ ≤ d ≤ 3v₁`. -/
theorem s8_slow_clear_at_v5 {v1 v5 d : ℝ} (hv1 : 0 < v1) (h5lo : 5 * v1 < v5) (h5hi : v5 < 7 * v1)
    (hd1 : v1 ≤ d) (hd3 : d ≤ 3 * v1) :
    ((6 : ℕ) : ℝ)⁻¹ ≤ circDist (d * Flanks.flankOpening 6 v5 1) := by
  haveI : Fact (2 ≤ 6) := ⟨by norm_num⟩
  have hv5 : 0 < v5 := by linarith
  refine Flanks.clear_at_first_opening_of_ratio (n := 6) hv5 ?_ ?_ <;> push_cast <;> nlinarith

/-- `v₄` is in the way at opening 1 of `v₅` exactly when `7v₄ > 5v₅` (for `v₁ < v₄ < v₅ < 7v₁`). -/
theorem s8_v4_steps_on {v1 v4 v5 : ℝ} (hv1 : 0 < v1) (h14 : v1 < v4) (h45 : v4 < v5) (h5 : v5 < 7 * v1) :
    circDist (v4 * Flanks.flankOpening 6 v5 1) < ((6 : ℕ) : ℝ)⁻¹ ↔ 5 * v5 < 7 * v4 := by
  have hv5 : 0 < v5 := by linarith
  have hy : v4 * Flanks.flankOpening 6 v5 1 = 7 * v4 / (6 * v5) := by
    unfold Flanks.flankOpening; push_cast; field_simp; ring
  rw [hy]
  have hlo : (6 : ℝ)⁻¹ < 7 * v4 / (6 * v5) := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  have hhi : 7 * v4 / (6 * v5) < 7 / 6 := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  push_cast
  constructor
  · intro h
    by_contra hc; push Not at hc
    have h56 : 7 * v4 / (6 * v5) ≤ 5 / 6 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    haveI : Fact (2 ≤ 6) := ⟨by norm_num⟩
    have := Flanks.circDist_ge_of_band (n := 6) (y := 7 * v4 / (6 * v5)) 0 (by push_cast; linarith)
      (by push_cast; linarith)
    simp only [Int.cast_zero, add_zero] at this
    push_cast at this; linarith
  · intro h
    have h56 : 5 / 6 < 7 * v4 / (6 * v5) := by
      rw [lt_div_iff₀ (by positivity)]; nlinarith
    have := circDist_le_abs_sub_int (7 * v4 / (6 * v5)) 1
    push_cast at this
    have hab : |7 * v4 / (6 * v5) - 1| < 6⁻¹ := by rw [abs_lt]; constructor <;> linarith
    linarith

end CascadeSecEight

#print axioms CascadeSecEight.s8_slow_clear_at_v5
#print axioms CascadeSecEight.s8_v4_steps_on
