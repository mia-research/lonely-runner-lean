import LonelyRunner.LRC.Spec.PinchReflectionN

#print axioms LRC.PinchReflection.affine_right
#print axioms LRC.PinchReflection.reflected_band
#print axioms LRC.PinchReflection.reflected_slack
#print axioms LRC.PinchReflection.active_boundaries
#print axioms LRC.PinchReflection.active_slope_reversal
#print axioms LRC.PinchReflection.active_slope_nonpos
#print axioms LRC.PinchReflection.reflected_right_inequalities
#print axioms LRC.PinchReflection.reflected_right_windows
#print axioms LRC.PinchReflection.rational_common_multiplier
#print axioms LRC.PinchReflection.rational_reflection_data
#print axioms LRC.PinchReflection.rational_pinch_transport

namespace LRC.PinchReflection.Regression

theorem boundary_swap :
    ((7 : ℝ)*(1/8) = 7/8) ∧ ((7 : ℝ)*(7/8) = 6+1/8) := by norm_num

theorem slope_swap :
    -(7 : ℝ)*((7/8)*(-1/8)-(1/8)*(7/8)) = 49/32 := by norm_num

/-- A concrete one-sided pinch invokes the universal selector without giving
it replacement labels or assuming clearance on the right. -/
theorem two_boundary_transport :
    ∃ p : Fin 2 → ℤ, ∃ e : ℝ, 0 < e ∧ ∀ h : ℝ, 0 ≤ h → h ≤ e →
      ∃ u : ℝ, 0 < u ∧ ∀ i ∈ (Finset.univ : Finset (Fin 2)),
        (p i : ℝ)+1/8 ≤
          (((![1/8,7/8] : Fin 2 → ℚ) i : ℝ)+h*(![-1/8,7/8] : Fin 2 → ℝ) i)*u ∧
        (((![1/8,7/8] : Fin 2 → ℚ) i : ℝ)+h*(![-1/8,7/8] : Fin 2 → ℝ) i)*u ≤ p i+7/8 := by
  apply rational_pinch_transport Finset.univ Finset.univ_nonempty
    ![1/8,7/8] ![-1/8,7/8] (fun _ => 0) 1 (delta := 1/10)
  · intro i hi; fin_cases i <;> norm_num
  · norm_num
  · norm_num
  · intro i hi; fin_cases i <;> norm_num
  · intro i hi j hj; fin_cases i <;> fin_cases j <;> norm_num

#print axioms boundary_swap
#print axioms slope_swap
#print axioms two_boundary_transport

end LRC.PinchReflection.Regression
