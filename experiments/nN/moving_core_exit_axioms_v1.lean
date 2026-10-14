import LonelyRunner.LRC.Spec.MovingCoreExitN

#print axioms LRC.MovingCoreExit.clear_at_exit
#print axioms LRC.MovingCoreExit.cLaps
#print axioms LRC.MovingCoreExit.c_guards
#print axioms LRC.MovingCoreExit.c_family
#print axioms LRC.MovingCoreExit.fLaps
#print axioms LRC.MovingCoreExit.f_guards
#print axioms LRC.MovingCoreExit.f_family
#print axioms LRC.MovingCoreExit.f_c_guard_derived
#print axioms LRC.MovingCoreExit.f_family_two_guards
#print axioms LRC.MovingCoreExit.b_guards
#print axioms LRC.MovingCoreExit.b_family
#print axioms LRC.MovingCoreExit.highFLaps
#print axioms LRC.MovingCoreExit.high_f_ratio
#print axioms LRC.MovingCoreExit.high_f_guards
#print axioms LRC.MovingCoreExit.high_f_family
#print axioms LRC.MovingCoreExit.late_c_guards
#print axioms LRC.MovingCoreExit.late_c_family
#print axioms LRC.MovingCoreExit.a_branch_family

namespace LRC.MovingCoreExit.Regression
noncomputable def coreC : Fin 6 → ℝ := ![1, 33 / 10, 55 / 14, 253 / 50, 32 / 5, 7]
noncomputable def coreF : Fin 6 → ℝ := ![1, 29 / 10, 55 / 14, 253 / 50, 669 / 100, 7]

theorem old_c_obstruction :
    (31 : ℝ) * (253 / 50) < 49 * (33 / 10) ∧
      (49 : ℝ) * (33 / 10) < 33 * (253 / 50) := by norm_num

theorem old_f_obstruction :
    (63 : ℝ) * (253 / 50) < 49 * (669 / 100) ∧
      (49 : ℝ) * (669 / 100) < 65 * (253 / 50) := by norm_num

set_option maxHeartbeats 1000000 in
theorem all_V_c {V : ℝ} (hV : 7 ≤ V) :
    ∃ t : ℝ, 0 < t ∧ (8 : ℝ)⁻¹ ≤ circDist (V * t) ∧
      ∀ i, (8 : ℝ)⁻¹ ≤ circDist (coreC i * t) := by
  apply c_family coreC (b := 7) (c := 55 / 14) (e := 253 / 50)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hV
  · intro i
    fin_cases i <;> norm_num [coreC]
  · rfl
  · rfl
  · rfl
  · intro w i
    fin_cases w <;> fin_cases i <;>
      norm_num [MovingCoreWindows.laps, MovingCoreWindows.setter, MovingCoreWindows.opening, coreC]
  · intro w i
    fin_cases w <;> fin_cases i <;>
      norm_num [MovingCoreWindows.laps, MovingCoreWindows.closing, coreC]
  · change (31 : ℝ) * (253 / 50) ≤ 49 * (33 / 10)
    norm_num
  · norm_num
  · change (41 : ℝ) * (32 / 5) ≤ 71 * (55 / 14)
    norm_num

set_option maxHeartbeats 1000000 in
theorem all_V_f {V : ℝ} (hV : 7 ≤ V) :
    ∃ t : ℝ, 0 < t ∧ (8 : ℝ)⁻¹ ≤ circDist (V * t) ∧
      ∀ i, (8 : ℝ)⁻¹ ≤ circDist (coreF i * t) := by
  apply f_family coreF (b := 7) (c := 55 / 14) (e := 253 / 50) (f := 669 / 100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hV
  · intro i
    fin_cases i <;> norm_num [coreF]
  · rfl
  · rfl
  · rfl
  · rfl
  · intro w i
    fin_cases w <;> fin_cases i <;>
      norm_num [MovingCoreWindows.laps, MovingCoreWindows.setter, MovingCoreWindows.opening, coreF]
  · intro w i
    fin_cases w <;> fin_cases i <;>
      norm_num [MovingCoreWindows.laps, MovingCoreWindows.closing, coreF]
  · norm_num
  · norm_num
  · change (65 : ℝ) * (29 / 10) ≤ 31 * (669 / 100)
    norm_num
  · norm_num
  · norm_num

#print axioms coreC
#print axioms coreF
#print axioms old_c_obstruction
#print axioms old_f_obstruction
#print axioms all_V_c
#print axioms all_V_f

noncomputable def coreHighF : Fin 6 → ℝ := ![1, 33 / 10, 55 / 14, 253 / 50, 137 / 20, 7]

/-- Both earlier f-closing guards fail in this example. -/
theorem both_old_closings_fail :
    (71 : ℝ) * (55 / 14) < 41 * (137 / 20) ∧
    (71 : ℝ) * 7 < 73 * (137 / 20) := by norm_num

set_option maxHeartbeats 1000000 in
theorem all_V_high_f {V : ℝ} (hV : 7 ≤ V) :
    ∃ t : ℝ, 0 < t ∧ (8 : ℝ)⁻¹ ≤ circDist (V * t) ∧
      ∀ i, (8 : ℝ)⁻¹ ≤ circDist (coreHighF i * t) := by
  apply a_branch_family coreHighF (b := 7) (c := 55 / 14) (e := 253 / 50) (f := 137 / 20)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hV
  · intro i
    fin_cases i <;> norm_num [coreHighF]
  · rfl
  · rfl
  · rfl
  · rfl
  · intro w i
    fin_cases w <;> fin_cases i <;>
      norm_num [MovingCoreWindows.laps, MovingCoreWindows.setter, MovingCoreWindows.opening, coreHighF]
  · intro w i
    fin_cases w <;> fin_cases i <;>
      norm_num [MovingCoreWindows.laps, MovingCoreWindows.closing, coreHighF]
  · change (31 : ℝ) * (253 / 50) ≤ 49 * (33 / 10)
    norm_num
  · norm_num

#print axioms coreHighF
#print axioms both_old_closings_fail
#print axioms all_V_high_f
end LRC.MovingCoreExit.Regression
