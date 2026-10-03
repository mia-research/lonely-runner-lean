import LonelyRunner.LRC.Spec.CoreWindowReplacementExampleN

#print axioms LRC.CoreWindowCompatibility.positive_open_intervals_iff
#print axioms LRC.CoreWindowCompatibility.joint_capture_iff
#print axioms LRC.CoreWindowReplacementExample.core
#print axioms LRC.CoreWindowReplacementExample.earlyLo
#print axioms LRC.CoreWindowReplacementExample.earlyHi
#print axioms LRC.CoreWindowReplacementExample.early_endpoints
#print axioms LRC.CoreWindowReplacementExample.early_core_window
#print axioms LRC.CoreWindowReplacementExample.three_captures_force_interval
#print axioms LRC.CoreWindowReplacementExample.core_window
#print axioms LRC.CoreWindowReplacementExample.replacement_in_window
#print axioms LRC.CoreWindowReplacementExample.compatible_family_isolated
#print axioms LRC.CoreWindowReplacementExample.all_largest_insertions

namespace LRC.CoreWindowCompatibility.Regression

/-- Touching forbidden intervals have no common obstructing speed. -/
theorem touching_not_compatible :
    ¬ ∃ V : ℝ, 1 < V ∧ V < 2 ∧ 2 < V ∧ V < 3 := by
  rintro ⟨V, _, h1, h2, _⟩
  linarith

/-- The example is a parameter family, including its original late member. -/
theorem original_member : ∃ t : ℝ, 0 < t ∧
    (8 : ℝ)⁻¹ ≤ circDist ((363 / 50) * t) ∧
    ∀ i, (8 : ℝ)⁻¹ ≤ circDist (CoreWindowReplacementExample.core i * t) :=
  CoreWindowReplacementExample.all_largest_insertions (by norm_num)

#print axioms touching_not_compatible
#print axioms original_member

end LRC.CoreWindowCompatibility.Regression
