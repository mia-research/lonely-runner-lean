import LonelyRunner.LRC.Spec.MovingCoreTwoGuardsN

#print axioms LRC.MovingCoreTwoGuards.derived_guards
#print axioms LRC.MovingCoreTwoGuards.family_isolated
#print axioms LRC.MovingCoreTwoGuards.laterLaps
#print axioms LRC.MovingCoreTwoGuards.later_derived_guards
#print axioms LRC.MovingCoreTwoGuards.family_isolated_later
#print axioms LRC.MovingCoreTwoGuards.isolation_or_two_obstructions

namespace LRC.MovingCoreTwoGuards.Regression
noncomputable def core : Fin 6 → ℝ := ![1, 29 / 10, 55 / 14, 253 / 50, 69 / 10, 7]

theorem beyond_old_fifth_guard : (63 : ℝ) * (253 / 50) < 49 * (69 / 10) := by
  norm_num

set_option maxHeartbeats 1000000 in
theorem later_family {V : ℝ} (hV : 7 ≤ V) :
    ∃ t : ℝ, 0 < t ∧ (8 : ℝ)⁻¹ ≤ circDist (V * t) ∧
      ∀ i, (8 : ℝ)⁻¹ ≤ circDist (core i * t) := by
  apply family_isolated_later core (b := 7) (c := 55 / 14) (e := 253 / 50)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hV
  · intro i
    fin_cases i <;> norm_num [core]
  · rfl
  · rfl
  · rfl
  · intro w i
    fin_cases w <;> fin_cases i <;>
      norm_num [MovingCoreWindows.laps, MovingCoreWindows.setter, MovingCoreWindows.opening, core]
  · intro w i
    fin_cases w <;> fin_cases i <;>
      norm_num [MovingCoreWindows.laps, MovingCoreWindows.closing, core]
  · change (49 : ℝ) * (29 / 10) ≤ 31 * (253 / 50)
    norm_num
  · change (65 : ℝ) * (253 / 50) ≤ 49 * (69 / 10)
    norm_num

#print axioms core
#print axioms beyond_old_fifth_guard
#print axioms later_family
end LRC.MovingCoreTwoGuards.Regression
