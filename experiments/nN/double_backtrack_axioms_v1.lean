import LonelyRunner.LRC.Spec.DoubleBacktrackN

#print axioms LRC.DoubleBacktrack.doubled_label
#print axioms LRC.DoubleBacktrack.doubled_clear_iff
#print axioms LRC.DoubleBacktrack.backtrack_band_iff
#print axioms LRC.DoubleBacktrack.strict_slack
#print axioms LRC.DoubleBacktrack.strict_slacks_extend
#print axioms LRC.DoubleBacktrack.readings
#print axioms LRC.DoubleBacktrack.replacement
#print axioms LRC.DoubleBacktrack.region_old_bands
#print axioms LRC.DoubleBacktrack.first_pinch_ratio
#print axioms LRC.DoubleBacktrack.region_labels
#print axioms LRC.DoubleBacktrack.region_bands
#print axioms LRC.DoubleBacktrack.region_selected_time
#print axioms LRC.DoubleBacktrack.region_lonely

namespace LRC.DoubleBacktrack.Regression

/-- The actual wide-example pinch lies in the proved region. -/
theorem wide_pinch :
    0 < (41 : ℝ)/(8*(2837/131)) ∧ Arrangement.LonelyAt
      (Fin.cases 0 (readings (742/131) (1413/131) (1544/131) (2616/131) (2837/131)))
      0 (41/(8*(2837/131))) := by
  apply region_lonely <;> norm_num

/-- The wide-example backward allowance exceeds the required repair. -/
theorem wide_margin :
    (303 : ℝ)/7336 - 212775/11326784 = 1947/86464 ∧ (0 : ℝ) < 1947/86464 := by
  norm_num

/-- A genuine failed branch: the required rollback crosses another opening. -/
theorem failed_budget : (1 : ℝ)/56 < 231/776 := by norm_num

/-- The carry threshold belongs to the new lap, preserving exact equality. -/
theorem carry_at_boundary : ⌊2*(9/16 : ℝ)-1/8⌋ = (1 : ℤ) := by norm_num

#print axioms wide_pinch
#print axioms wide_margin
#print axioms failed_budget
#print axioms carry_at_boundary

end LRC.DoubleBacktrack.Regression
