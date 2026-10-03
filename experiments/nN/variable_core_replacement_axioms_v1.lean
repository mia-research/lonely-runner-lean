import LonelyRunner.LRC.Spec.VariableCoreReplacementN

#print axioms LRC.VariableCoreReplacement.lower
#print axioms LRC.VariableCoreReplacement.upper
#print axioms LRC.VariableCoreReplacement.left
#print axioms LRC.VariableCoreReplacement.right
#print axioms LRC.VariableCoreReplacement.endpoints
#print axioms LRC.VariableCoreReplacement.windows_clear
#print axioms LRC.VariableCoreReplacement.obstruction_interval
#print axioms LRC.VariableCoreReplacement.rescue_reading
#print axioms LRC.VariableCoreReplacement.family_isolated

namespace LRC.VariableCoreReplacement.Regression

theorem nondegenerate_bounds : ∀ i, lower i < upper i := by
  intro i
  fin_cases i <;> norm_num [lower, upper]

theorem original_core_contained : ∀ i,
    lower i ≤ CoreWindowReplacementExample.core i ∧
    CoreWindowReplacementExample.core i ≤ upper i := by
  intro i
  fin_cases i <;> norm_num [lower, upper, CoreWindowReplacementExample.core]

theorem far_inserted_speed : ∃ t : ℝ, 0 < t ∧
    (8 : ℝ)⁻¹ ≤ circDist (1000 * t) ∧
    ∀ i, (8 : ℝ)⁻¹ ≤ circDist (CoreWindowReplacementExample.core i * t) :=
  family_isolated _ original_core_contained (by norm_num)

#print axioms nondegenerate_bounds
#print axioms original_core_contained
#print axioms far_inserted_speed

end LRC.VariableCoreReplacement.Regression
