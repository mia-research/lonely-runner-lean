import LonelyRunner.LRC.Spec.CoreWindowInsertionN

#print axioms LRC.CoreWindowInsertion.exit_in_window
#print axioms LRC.CoreWindowInsertion.swallowed_iff
#print axioms LRC.CoreWindowInsertion.swallowed_speed_iff
#print axioms LRC.CoreWindowInsertion.swallowed_width
#print axioms LRC.CoreWindowInsertion.insertion_or_swallowed
#print axioms LRC.CoreWindowInsertion.swallowed_label_bound
#print axioms LRC.CoreWindowInsertion.finite_obstruction_labels

namespace LRC.CoreWindowInsertion.Regression

/-- A genuinely swallowed positive-width interval. -/
theorem swallowed_example :
    ∀ t : ℝ, 15 / 16 ≤ t → t ≤ 17 / 16 →
      circDist (1 * t) < (8 : ℝ)⁻¹ := by
  apply (swallowed_iff (V := 1) (L := 15 / 16) (U := 17 / 16)
    (by norm_num) (by norm_num)).mpr
  exact ⟨1, by norm_num, by norm_num⟩

/-- Equal capture-zone width is not swallowed: its endpoints are clear. -/
theorem equal_width_not_swallowed :
    ¬ (∀ t : ℝ, 7 / 8 ≤ t → t ≤ 9 / 8 →
      circDist (1 * t) < (8 : ℝ)⁻¹) := by
  intro h
  have hh := swallowed_width (V := 1) (L := 7 / 8) (U := 9 / 8)
    (by norm_num) (by norm_num) h
  norm_num at hh

#print axioms swallowed_example
#print axioms equal_width_not_swallowed

end LRC.CoreWindowInsertion.Regression
