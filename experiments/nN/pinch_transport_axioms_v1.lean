import LonelyRunner.LRC.Spec.PinchTransportN

#print axioms LRC.PinchTransport.exit_shift_bounds
#print axioms LRC.PinchTransport.reading_shift
#print axioms LRC.PinchTransport.displacement_lt_three_quarters
#print axioms LRC.PinchTransport.old_setter_band
#print axioms LRC.PinchTransport.handoff_pair_clear
#print axioms LRC.PinchTransport.same_lap_ratio
#print axioms LRC.PinchTransport.same_lap_group_band
#print axioms LRC.PinchTransport.same_lap_move_lonely
#print axioms LRC.PinchTransport.same_lap_separation_time
#print axioms LRC.PinchTransport.retained_band_iff
#print axioms LRC.PinchTransport.group_exit_lonely_of_deadlines

namespace LRC.PinchTransport.Regression

open MomentIterationN

/-- A two-reading capture group exits while an outside reading reaches its
upper deadline EXACTLY. Equality remains clear. -/
theorem group_with_exact_deadline :
    move 8 {(56 / 9 : ℝ), 8, 17 / 2} (1 / 8) = nextOpening 8 8 (1 / 8) ∧
      (1 / 8 : ℝ) < nextOpening 8 8 (1 / 8) ∧
      Lonely 8 {(56 / 9 : ℝ), 8, 17 / 2} (nextOpening 8 8 (1 / 8)) := by
  apply group_exit_lonely_of_deadlines _ {(8 : ℝ), 17 / 2} (K := 1) (fun _ => 0)
  all_goals norm_num [Finset.subset_iff]

/-- Lap zero lacks the closeness forced by positive-lap capture. -/
theorem zero_lap_can_recapture : inWay 8 8 (nextOpening 8 1 (1 / 128)) := by
  rw [nextOpening_eq (by norm_num : (0 : ℝ) < 1)
    (k := 0) (by norm_num : |(1 : ℝ) * (1 / 128) - (0 : ℤ)| < (8 : ℝ)⁻¹)]
  norm_num [inWay, circDist]

/-- The review example's next opening still has an outside blocker. This
guards against dropping the retained-deadline hypothesis. -/
theorem missed_deadline : inWay 8 6 (9 / 56) := by
  unfold inWay
  apply lt_of_le_of_lt (ConstructionN.circDist_le_abs_sub_int _ 1)
  norm_num

/-- Distinct disparities may coincide modulo one after the reciprocal-gap
time; the same-lap separation bound must retain its integer labels. -/
theorem distinct_readings_return : inWay 8 7 1 ∧ inWay 8 8 1 := by
  norm_num [inWay, circDist]

#print axioms group_with_exact_deadline
#print axioms zero_lap_can_recapture
#print axioms missed_deadline
#print axioms distinct_readings_return

end LRC.PinchTransport.Regression
