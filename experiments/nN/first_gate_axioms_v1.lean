import LonelyRunner.LRC.Spec.FirstGateN

#print axioms LRC.FirstGate.zone_width
#print axioms LRC.FirstGate.faster_zone_width
#print axioms LRC.FirstGate.opening_increment
#print axioms LRC.FirstGate.move_lt_nine_of_le_seven
#print axioms LRC.FirstGate.nearest_inWay
#print axioms LRC.FirstGate.nearest_opening
#print axioms LRC.FirstGate.lonely_above_seven_iff
#print axioms LRC.FirstGate.move_ge_nine
#print axioms LRC.FirstGate.forced_nearest_move
#print axioms LRC.FirstGate.nearest_clear_first_window
#print axioms LRC.FirstGate.first_crossing_below_eight
#print axioms LRC.FirstGate.crossing_iff_visits_nine
#print axioms LRC.FirstGate.crossing_forces_nearest_setter
#print axioms LRC.FirstGate.terminal_gate_equivalences

namespace LRC.FirstGate.Regression
open MomentIterationN

/-- This is a LOCAL two-move counterexample to deriving a visit to 9 from
width alone. It does not start at R=1 and is not a counterexample to the
empirical seven-reading gate claim from that start. Times below are R/8. -/
theorem local_skip_first :
    move 8 ({1, 45 / 44, 9 / 5} : Finset ℝ) (7 / 8) = 11 / 10 := by
  classical
  apply le_antisymm
  · unfold move
    rw [Finset.fold_max_le]
    refine ⟨by norm_num, ?_⟩
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl <;>
      norm_num [inWay, nextOpening, circDist, Int.fract]
  · have h := nextOpening_le_move (n := 8) (d := 45 / 44)
      (t := 7 / 8) (ds := {1, 45 / 44, 9 / 5}) (by simp)
      (by norm_num [inWay, circDist, Int.fract])
    norm_num [nextOpening] at h
    exact h

theorem local_skip_second :
    move 8 ({1, 45 / 44, 9 / 5} : Finset ℝ) (11 / 10) = 85 / 72 := by
  classical
  apply le_antisymm
  · unfold move
    rw [Finset.fold_max_le]
    refine ⟨by norm_num, ?_⟩
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl <;>
      norm_num [inWay, nextOpening, circDist, Int.fract]
  · have h := nextOpening_le_move (n := 8) (d := 9 / 5)
      (t := 11 / 10) (ds := {1, 45 / 44, 9 / 5}) (by simp)
      (by norm_num [inWay, circDist, Int.fract])
    norm_num [nextOpening] at h
    exact h

theorem local_skip_straddles : (11 : ℝ) / 10 < 9 / 8 ∧ (9 : ℝ) / 8 < 85 / 72 := by
  norm_num

#print axioms local_skip_first
#print axioms local_skip_second
#print axioms local_skip_straddles
end LRC.FirstGate.Regression
