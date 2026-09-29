import LonelyRunner.LRC.Spec.WindowPinchN

/-! Complete declaration audit and exact endpoint regressions for WindowPinchN. -/

#print axioms LRC.WindowPinch.intervals_iff
#print axioms LRC.WindowPinch.intervals_iff_max_le_min
#print axioms LRC.WindowPinch.band_iff
#print axioms LRC.WindowPinch.lap_windows_iff
#print axioms LRC.WindowPinch.lonely_of_windows
#print axioms LRC.WindowPinch.exists_lonely_of_lap_inequalities
#print axioms LRC.WindowPinch.ratio_window_iff
#print axioms LRC.WindowPinch.scale_windows_iff
#print axioms LRC.WindowPinch.disparity_ratio_affine
#print axioms LRC.WindowPinch.boundary_order_iff
#print axioms LRC.WindowPinch.slack_affine
#print axioms LRC.WindowPinch.ap_window_iff
#print axioms LRC.WindowPinch.decreasing_slack_iff
#print axioms LRC.WindowPinch.first_pinch
#print axioms LRC.WindowPinch.exists_first_pinch
#print axioms LRC.WindowPinch.no_pinch_of_nonnegative_slopes
#print axioms LRC.WindowPinch.deformed_scale_iff
#print axioms LRC.WindowPinch.first_scale_pinch

namespace LRC.WindowPinch.Regression

/-- A singleton intersection is feasible, not a failed event. -/
theorem singleton_window : ∃ t : ℝ, ∀ i ∈ ({0} : Finset ℕ),
    (3 : ℝ) / 8 ≤ t ∧ t ≤ 3 / 8 := by
  exact ⟨3 / 8, fun _ _ => ⟨le_rfl, le_rfl⟩⟩

/-- A root at zero is included, and every positive parameter fails. -/
theorem immediate_pinch (s : ℝ) : 0 ≤ 0 + s * (-1 : ℝ) ↔ s ≤ 0 := by
  rw [decreasing_slack_iff (by norm_num : (-1 : ℝ) < 0)]
  norm_num

/-- Distinct constraints may have the same first root. -/
theorem tied_roots (s : ℝ) :
    (0 ≤ 2 + s * (-1 : ℝ) ∧ 0 ≤ 4 + s * (-2 : ℝ)) ↔ s ≤ 2 := by
  rw [decreasing_slack_iff (by norm_num : (-1 : ℝ) < 0),
    decreasing_slack_iff (by norm_num : (-2 : ℝ) < 0)]
  norm_num

/-- The review example really is lonely at 3/8, by the ordinary lap windows.
This asserts the witness, not a particular intervening cascade history. -/
theorem review_example : Arrangement.LonelyAt
    ![(0 : ℝ), 99 / 100, 2, 3, 4, 5, 6, 7] 0 (3 / 8) := by
  apply lonely_of_windows (q := ![0, 0, 0, 1, 1, 1, 2, 2])
  intro i hi
  fin_cases i <;> norm_num at *

#print axioms singleton_window
#print axioms immediate_pinch
#print axioms tied_roots
#print axioms review_example

end LRC.WindowPinch.Regression
