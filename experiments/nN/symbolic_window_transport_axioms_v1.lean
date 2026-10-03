import LonelyRunner.LRC.Spec.SymbolicWindowFamilyN

#print axioms LRC.SymbolicWindowTransport.pinch_interior
#print axioms LRC.SymbolicWindowTransport.slack_at_pinch
#print axioms LRC.SymbolicWindowTransport.slack_at_pinch_iff
#print axioms LRC.SymbolicWindowTransport.slack_at_pinch_pos_iff
#print axioms LRC.SymbolicWindowTransport.pinch_order_iff
#print axioms LRC.SymbolicWindowTransport.affine_nonneg_between
#print axioms LRC.SymbolicWindowTransport.lap_inequalities_between
#print axioms LRC.SymbolicWindowTransport.replacement_window_at_pinch
#print axioms LRC.SymbolicWindowTransport.positive_windows_between
#print axioms LRC.SymbolicWindowFamily.target
#print axioms LRC.SymbolicWindowFamily.laps
#print axioms LRC.SymbolicWindowFamily.knots
#print axioms LRC.SymbolicWindowFamily.endpoint_inequalities
#print axioms LRC.SymbolicWindowFamily.family_clear
#print axioms LRC.SymbolicWindowFamily.family_lonely

namespace LRC.SymbolicWindowTransport.Regression

/-- The first exact pinch in the wide example. -/
theorem wide_first_pinch : (10 : ℝ)/(10-(-847/199)) = 1990/2837 := by norm_num

/-- A replacement can start infeasible at the AP and become strictly feasible
at the old pinch. -/
theorem replacement_not_initially_feasible :
    (0 : ℝ) < (1-10/(10-(-847/199)))*(-1) + (10/(10-(-847/199)))*2 := by
  norm_num

/-- A replacement test can fail: positivity is not automatic from an old pinch. -/
theorem replacement_can_fail :
    ¬ ((0 : ℝ) ≤ (1-10/(10-(-847/199)))*(-1) + (10/(10-(-847/199)))*(-2)) := by
  norm_num

/-- Singleton boundaries are preserved by the exact non-strict criterion. -/
theorem equal_boundary :
    (1-(1 : ℝ)/(1-(-1)))*1 + ((1 : ℝ)/(1-(-1)))*(-1) = 0 := by norm_num

/-- A uniform finite lap list cannot reach arbitrarily small nearest gaps.
This is a necessary bound, not an existence or termination assertion. -/
theorem lap_budget_requires_gap {m t : ℝ} {K : ℕ} (hm : 0 ≤ m)
    (hnear : 1/8 ≤ m*t) (hfar : 7*t ≤ (K : ℝ)+7/8) :
    7 ≤ m*(8*(K : ℝ)+7) := by
  nlinarith [mul_le_mul_of_nonneg_left hfar hm]

#print axioms wide_first_pinch
#print axioms replacement_not_initially_feasible
#print axioms replacement_can_fail
#print axioms equal_boundary
#print axioms lap_budget_requires_gap

end LRC.SymbolicWindowTransport.Regression
