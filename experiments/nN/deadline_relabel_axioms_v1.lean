import LonelyRunner.LRC.Spec.DeadlineRelabelN

#print axioms LRC.DeadlineRelabel.label_bound_before_deadline
#print axioms LRC.DeadlineRelabel.forced_label_drop
#print axioms LRC.DeadlineRelabel.label_update_le
#print axioms LRC.DeadlineRelabel.relabel_bounds
#print axioms LRC.DeadlineRelabel.triple_clears_middle
#print axioms LRC.DeadlineRelabel.five_clears_middle
#print axioms LRC.DeadlineRelabel.double_blocker_middle
#print axioms LRC.DeadlineRelabel.triple_blocker_ranges
#print axioms LRC.DeadlineRelabel.five_clears_triple_blocker
#print axioms LRC.DeadlineRelabel.boundary_clear
#print axioms LRC.DeadlineRelabel.one_small_group
#print axioms LRC.DeadlineRelabel.pinch_one_blocker
#print axioms LRC.DeadlineRelabel.dilated_phase
#print axioms LRC.DeadlineRelabel.pinch_one_blocker_readings
#print axioms LRC.DeadlineRelabel.forward_margin_iff
#print axioms LRC.DeadlineRelabel.exceptionReadings
#print axioms LRC.DeadlineRelabel.exception_backward_bands
#print axioms LRC.DeadlineRelabel.exception_backward_clear

namespace LRC.DeadlineRelabel.Regression

/-- The old event is clear, including both pinching boundary readings. -/
theorem old_clear : ∀ i, (8 : ℝ)⁻¹ ≤ circDist (exceptionReadings 100 i) := by
  intro i
  fin_cases i <;> norm_num [exceptionReadings, circDist, Int.fract]

/-- Each proposed dilation has exactly its indicated lone blocker. -/
theorem sole_blockers :
    (∀ i, circDist (2 * exceptionReadings 100 i) < (8 : ℝ)⁻¹ ↔ i = 2) ∧
    (∀ i, circDist (3 * exceptionReadings 100 i) < (8 : ℝ)⁻¹ ↔ i = 3) ∧
    (∀ i, circDist (5 * exceptionReadings 100 i) < (8 : ℝ)⁻¹ ↔ i = 4) := by
  constructor
  · intro i; fin_cases i <;> norm_num [exceptionReadings, circDist, Int.fract] <;> decide
  constructor <;> intro i <;> fin_cases i <;>
    norm_num [exceptionReadings, circDist, Int.fract] <;> decide

/-- At all three forward exits an explicitly identified other reading is caught. -/
theorem forward_failures :
    circDist ((7 / 16 : ℝ) * (9 / 4)) < (8 : ℝ)⁻¹ ∧
    circDist ((5 / 8 : ℝ) * (7227 / 2408)) < (8 : ℝ)⁻¹ ∧
    circDist ((7 / 8 : ℝ) * (45 / 8)) < (8 : ℝ)⁻¹ := by
  norm_num [circDist, Int.fract]

#print axioms old_clear
#print axioms sole_blockers
#print axioms forward_failures

end LRC.DeadlineRelabel.Regression
