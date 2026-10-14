import LonelyRunner.LRC.Spec.MovingCoreWindowsN
import LonelyRunner.LRC.Spec.VariableCoreReplacementN

#print axioms LRC.MovingCoreWindows.opening
#print axioms LRC.MovingCoreWindows.closing
#print axioms LRC.MovingCoreWindows.setter
#print axioms LRC.MovingCoreWindows.laps
#print axioms LRC.MovingCoreWindows.window_endpoints
#print axioms LRC.MovingCoreWindows.window_clear
#print axioms LRC.MovingCoreWindows.obstruction_labels
#print axioms LRC.MovingCoreWindows.rescue
#print axioms LRC.MovingCoreWindows.family_isolated

namespace LRC.MovingCoreWindows.Regression

noncomputable def neighbouringCore : Fin 6 → ℝ :=
  ![1, 73 / 25, 397 / 100, 253 / 50, 321 / 50, 699 / 100]

/-- This family is outside the previous rectangular region. -/
theorem outside_old_region :
    VariableCoreReplacement.upper 5 < neighbouringCore 5 := by
  change (2350 : ℝ) / 337 < 699 / 100
  norm_num

set_option maxHeartbeats 1000000 in
/-- A neighbouring core beyond the old boundary, uniformly in the added speed. -/
theorem neighbouring_family {V : ℝ} (hV : 699 / 100 ≤ V) :
    ∃ t : ℝ, 0 < t ∧ (8 : ℝ)⁻¹ ≤ circDist (V * t) ∧
      ∀ i, (8 : ℝ)⁻¹ ≤ circDist (neighbouringCore i * t) := by
  apply family_isolated neighbouringCore
    (b := 699 / 100) (c := 397 / 100) (e := 253 / 50)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hV
  · intro i
    fin_cases i <;> norm_num [neighbouringCore]
  · intro w i
    fin_cases w <;> fin_cases i <;> norm_num [laps, setter, opening, neighbouringCore]
  · intro w i
    fin_cases w <;> fin_cases i <;> norm_num [laps, closing, neighbouringCore]

#print axioms neighbouringCore
#print axioms outside_old_region
#print axioms neighbouring_family

end LRC.MovingCoreWindows.Regression
