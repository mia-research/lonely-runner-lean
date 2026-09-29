import LonelyRunner.LRC.Spec.LapDeadlineN

#print axioms LRC.LapDeadline.lap
#print axioms LRC.LapDeadline.slack
#print axioms LRC.LapDeadline.deadline
#print axioms LRC.LapDeadline.slack_bounds
#print axioms LRC.LapDeadline.clear_iff_slack
#print axioms LRC.LapDeadline.captured_iff_slack
#print axioms LRC.LapDeadline.clear_iff_deadline
#print axioms LRC.LapDeadline.lap_update
#print axioms LRC.LapDeadline.slack_update
#print axioms LRC.LapDeadline.slack_update_from_phase
#print axioms LRC.LapDeadline.deadline_update
#print axioms LRC.LapDeadline.lap_mono
#print axioms LRC.LapDeadline.lap_unchanged_iff
#print axioms LRC.LapDeadline.retain_deadline
#print axioms LRC.LapDeadline.lap_of_band
#print axioms LRC.LapDeadline.lap_of_capture
#print axioms LRC.LapDeadline.setter_reset
#print axioms LRC.LapDeadline.group_deadline_advance
#print axioms LRC.LapDeadline.group_window_iff
#print axioms LRC.LapDeadline.group_window_nonempty
#print axioms LRC.LapDeadline.group_window_width
#print axioms LRC.LapDeadline.lonely_after_shift_iff

namespace LRC.LapDeadline.Regression

/-- At an entering edge the deadline is met exactly: still clear. -/
theorem equality_is_clear : slack 6 (7 / 48) = 0 ∧
    (8 : ℝ)⁻¹ ≤ circDist ((6 : ℝ) * (7 / 48)) := by
  have h : slack 6 (7 / 48) = 0 := by norm_num [slack, lap]
  exact ⟨h, (clear_iff_slack 6 (7 / 48)).mpr h.ge⟩

/-- The outside runner in the review example loses its retained deadline. -/
theorem review_deadline_crossing : lap 6 (25 / 198) = 0 ∧ lap 6 (9 / 56) = 0 ∧
    slack 6 (25 / 198) = 31 / 264 ∧ slack 6 (9 / 56) = -(5 / 56 : ℝ) := by
  norm_num [slack, lap]

/-- At the subsequent opening its label advances and clearance is refreshed. -/
theorem exact_opening_reset : lap 6 (3 / 16) = 1 ∧ slack 6 (3 / 16) = 3 / 4 ∧
    deadline 6 (3 / 16) = deadline 6 (9 / 56) + 1 / 6 := by
  norm_num [lap, slack, deadline]

/-- A jump can cross multiple openings and STILL land in capture. -/
theorem multiple_lap_jump : lap 8 (1 / 8) = 0 ∧ lap 8 (3 / 8) = 2 ∧
    slack 8 (1 / 8) = -(1 / 8 : ℝ) ∧ slack 8 (3 / 8) = -(1 / 8 : ℝ) := by
  norm_num [lap, slack]

/-- Exact width of the clear interval for a positive-lap group with extrema
8 and 17/2, captured on lap 1. -/
theorem group_width_example :
    ((1 : ℝ) + 7 / 8) / (17 / 2) - (1 + 1 / 8) / 8 = 87 / 1088 := by
  norm_num

#print axioms equality_is_clear
#print axioms review_deadline_crossing
#print axioms exact_opening_reset
#print axioms multiple_lap_jump
#print axioms group_width_example

end LRC.LapDeadline.Regression
