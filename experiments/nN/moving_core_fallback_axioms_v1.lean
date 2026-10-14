import LonelyRunner.LRC.Spec.MovingCoreFallbackN

#print axioms LRC.MovingCoreWindows.window_endpoints_of_cross
#print axioms LRC.MovingCoreWindows.obstruction_labels_of_cross
#print axioms LRC.MovingCoreWindows.family_isolated_of_residual
#print axioms LRC.MovingCoreFallback.laps
#print axioms LRC.MovingCoreFallback.residual_clear
#print axioms LRC.MovingCoreFallback.core_clear
#print axioms LRC.MovingCoreFallback.family_isolated

namespace LRC.MovingCoreFallback.Regression

noncomputable def core : Fin 6 → ℝ :=
  ![1, 29 / 10, 55 / 14, 253 / 50, 32 / 5, 7]

theorem beyond_previous_face :
    (1953 : ℝ) * (55 / 14) < 1105 * 7 := by norm_num

set_option maxHeartbeats 1000000 in
/-- A complete added-speed family across the previous sufficient boundary. -/
theorem all_added_readings {V : ℝ} (hV : 7 ≤ V) :
    ∃ t : ℝ, 0 < t ∧ (8 : ℝ)⁻¹ ≤ circDist (V * t) ∧
      ∀ i, (8 : ℝ)⁻¹ ≤ circDist (core i * t) := by
  apply family_isolated core (b := 7) (c := 55 / 14) (e := 253 / 50)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hV
  · intro i
    fin_cases i <;> norm_num [core]
  · intro w i
    fin_cases w <;> fin_cases i <;>
      norm_num [MovingCoreWindows.laps, MovingCoreWindows.setter,
        MovingCoreWindows.opening, core]
  · intro w i
    fin_cases w <;> fin_cases i <;>
      norm_num [MovingCoreWindows.laps, MovingCoreWindows.closing, core]
  · norm_num
  · norm_num
  · intro i
    fin_cases i <;> norm_num [laps, core]
  · intro i
    fin_cases i <;> norm_num [laps, core]

/-- At V=7.21 all three early windows really are swallowed, with labels 1,4,6. -/
theorem residual_example :
    (7 : ℝ) < 721 / 100 ∧ 7 * (721 / 100 : ℝ) < 9 * 7 ∧
    31 * (55 / 14 : ℝ) < 17 * (721 / 100) ∧
    31 * (721 / 100 : ℝ) < 33 * 7 ∧
    47 * (253 / 50 : ℝ) < 33 * (721 / 100) ∧
    47 * (721 / 100 : ℝ) < 49 * 7 := by norm_num

/-- The old named replacement misses the old core window in this example. -/
theorem old_replacement_too_late :
    (63 : ℝ) / 7 < 65 / (721 / 100) := by norm_num

#print axioms core
#print axioms beyond_previous_face
#print axioms all_added_readings
#print axioms residual_example
#print axioms old_replacement_too_late

end LRC.MovingCoreFallback.Regression
