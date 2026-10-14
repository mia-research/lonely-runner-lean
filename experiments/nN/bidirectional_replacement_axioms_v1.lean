import LonelyRunner.LRC.Spec.BidirectionalReplacementN

#print axioms LRC.BidirectionalReplacement.backward_margin_iff
#print axioms LRC.BidirectionalReplacement.same_guard_fast
#print axioms LRC.BidirectionalReplacement.guards_distinct
#print axioms LRC.BidirectionalReplacement.guarded_interval_trapped
#print axioms LRC.BidirectionalReplacement.forced_forward_label
#print axioms LRC.BidirectionalReplacement.forced_backward_label
#print axioms LRC.BidirectionalReplacement.successor_pair_iff
#print axioms LRC.BidirectionalReplacement.centre
#print axioms LRC.BidirectionalReplacement.family_initial
#print axioms LRC.BidirectionalReplacement.family_first_exit
#print axioms LRC.BidirectionalReplacement.family_successor_bands
#print axioms LRC.BidirectionalReplacement.family_successor_clear

namespace LRC.BidirectionalReplacement.Regression

theorem old_clear : ∀ i, (8 : ℝ)⁻¹ ≤ circDist (centre i) := by
  intro i
  fin_cases i <;> norm_num [centre, circDist, Int.fract]

/-- No eligible lone-blocker dilation was omitted from the regression. -/
theorem candidate_blockers :
    (∀ i, circDist (2 * centre i) < (8 : ℝ)⁻¹ ↔ i = 2 ∨ i = 3) ∧
    (∀ i, circDist (3 * centre i) < (8 : ℝ)⁻¹ ↔ i = 5) ∧
    (∀ i, circDist (5 * centre i) < (8 : ℝ)⁻¹ ↔ i = 6) := by
  constructor
  · intro i; fin_cases i <;> norm_num [centre, circDist, Int.fract] <;> decide
  constructor <;> intro i <;> fin_cases i <;>
    norm_num [centre, circDist, Int.fract] <;> decide

/-- Both actual repairs fail at both lone-blocker candidates, not merely
the sufficient current-band retention tests. -/
theorem both_directions_fail :
    circDist ((399 / 64 : ℝ) * (88 / 29)) < (8 : ℝ)⁻¹ ∧
    circDist ((79 / 32 : ℝ) * (248 / 87)) < (8 : ℝ)⁻¹ ∧
    circDist ((2119 / 128 : ℝ) * (776 / 153)) < (8 : ℝ)⁻¹ ∧
    circDist ((399 / 64 : ℝ) * (760 / 153)) < (8 : ℝ)⁻¹ := by
  norm_num [circDist, Int.fract]

theorem selected_exits :
    (33 / 8 : ℝ) / (87 / 64) = 88 / 29 ∧
    (31 / 8 : ℝ) / (87 / 64) = 248 / 87 ∧
    (97 / 8 : ℝ) / (153 / 64) = 776 / 153 ∧
    (95 / 8 : ℝ) / (153 / 64) = 760 / 153 ∧
    (153 / 8 : ℝ) / (399 / 64) = 408 / 133 := by norm_num

/-- Reading 0 returns to clearance; it is not protected for the whole jump. -/
theorem intermediate_capture :
    (88 / 29 : ℝ) < 272 / 89 ∧ (272 / 89 : ℝ) < 408 / 133 ∧
    circDist ((89 / 8 : ℝ) * (272 / 89)) = 0 := by
  norm_num [circDist, Int.fract]

#print axioms old_clear
#print axioms candidate_blockers
#print axioms both_directions_fail
#print axioms selected_exits
#print axioms intermediate_capture

end LRC.BidirectionalReplacement.Regression
