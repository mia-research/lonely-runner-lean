import LonelyRunner.LRC.Spec.MixedLapOverlapN

#print axioms LRC.MixedLapOverlap.active_lower_at_move
#print axioms LRC.MixedLapOverlap.active_clear_until
#print axioms LRC.MixedLapOverlap.move_before_group_deadline
#print axioms LRC.MixedLapOverlap.persistent_blocker_gt_three
#print axioms LRC.MixedLapOverlap.outsider_overlaps
#print axioms LRC.MixedLapOverlap.overlap_with_one_outsider
#print axioms LRC.MixedLapOverlap.two_moves_of_disparity_budget
#print axioms LRC.MixedLapOverlap.opening_time_bound
#print axioms LRC.MixedLapOverlap.pair_after_slow_opening
#print axioms LRC.MixedLapOverlap.two_outsiders_overlap
#print axioms LRC.MixedLapOverlap.protected_clear_until
#print axioms LRC.MixedLapOverlap.protected_group_overlaps_one
#print axioms LRC.MixedLapOverlap.protected_group_overlaps_two

namespace LRC.MixedLapOverlap.Regression

open MomentIterationN

/-- Different integer laps share a genuine clear interval after the move. -/
theorem different_laps_clear : Lonely 8 {(1 : ℝ), 2, 3} (9 / 8) := by
  norm_num [Lonely, circDist]

/-- The two-outsider theorem applies at the exact width boundary. -/
theorem exact_width : ∃ s : ℝ, 1 ≤ s ∧ s ≤ 3 / 2 ∧
    (8 : ℝ)⁻¹ ≤ circDist (1 * s) ∧ (8 : ℝ)⁻¹ ≤ circDist (2 * s) := by
  exact two_outsiders_overlap (by norm_num) (by norm_num) (by norm_num)

/-- Two outside runners can require fast -> slow -> fast exits. The final
overlap is checked exactly, not just inferred from a numerical trace. -/
theorem three_exit_pattern :
    nextOpening 8 8 (7 / 8) = 57 / 64 ∧
    inWay 8 1 (57 / 64) ∧ nextOpening 8 1 (57 / 64) = 9 / 8 ∧
    inWay 8 8 (9 / 8) ∧ nextOpening 8 8 (9 / 8) = 73 / 64 ∧
    (8 : ℝ)⁻¹ ≤ circDist (1 * (73 / 64)) ∧
    (8 : ℝ)⁻¹ ≤ circDist (8 * (73 / 64)) := by
  norm_num [nextOpening, inWay, circDist]

/-- Persistent capture is possible above the factor-three threshold. -/
theorem persistent_fast_reading : inWay 8 8 1 ∧ inWay 8 8 (9 / 8) ∧ (3 : ℝ) < 8 := by
  norm_num [inWay, circDist]

/-- A far outside runner can be repaired after the first exit. -/
theorem fast_outsider_repair : inWay 8 104 (1 / 8) ∧
    nextOpening 8 104 (1 / 8) = 105 / 832 ∧
    Lonely 8 {(1 : ℝ), 6 / 5, 7 / 5, 8 / 5, 9 / 5, 2, 104} (105 / 832) := by
  norm_num [inWay, nextOpening, Lonely, circDist]

#print axioms different_laps_clear
#print axioms exact_width
#print axioms three_exit_pattern
#print axioms persistent_fast_reading
#print axioms fast_outsider_repair

end LRC.MixedLapOverlap.Regression
