import LonelyRunner.LRC.Spec.MappedCascadeRulesN

#print axioms LRC.MappedCascadeRules.faster_closes_before_opener
#print axioms LRC.MappedCascadeRules.own_closer_maximal
#print axioms LRC.MappedCascadeRules.earlier_setter_faster
#print axioms LRC.MappedCascadeRules.previous_setter_closes_first
#print axioms LRC.MappedCascadeRules.closing_displacement
#print axioms LRC.MappedCascadeRules.two_capture_speed_bound
#print axioms LRC.MappedCascadeRules.two_capture_opening_bound
#print axioms LRC.MappedCascadeRules.opening_bound_of_zone_link
#print axioms LRC.MappedCascadeRules.mapped_late_bound

namespace LRC.MappedCascadeRules.Regression

/-- Equality in the two closed constraints attains the algebraic bound.
This does not assert that the limiting configuration follows the open-cell path. -/
theorem limiting_equalities :
    (9 : ℝ) * (47 / 9) = 47 ∧
    (33 : ℝ) * (2209 / 297) = 47 * (47 / 9) ∧
    (89 : ℝ) / (2209 / 297) = 26433 / 2209 := by norm_num

/-- A faster reading at its lower edge still closes before the opener. -/
theorem faster_at_lower_edge : (7 - (1 : ℝ)) / 8 < 6 / 7 := by norm_num

#print axioms limiting_equalities
#print axioms faster_at_lower_edge

end LRC.MappedCascadeRules.Regression
