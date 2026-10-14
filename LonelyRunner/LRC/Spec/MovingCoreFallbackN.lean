import LonelyRunner.LRC.Spec.MovingCoreWindowsN

/-!
# Changed-lap replacement beyond the first moving-core rescue

The replacement is R = 49/e (ordinary time R/8), with core labels
(1,3,4,6,7,8). All region guards are explicit linear inequalities.
This is a sufficient mechanism region, not an exhaustive arrangement cover.
-/

namespace LRC.MovingCoreFallback

def laps : Fin 6 → ℤ := ![1, 3, 4, 6, 7, 8]

/-- The residual obstruction interval is clear at the new setter's exit. -/
theorem residual_clear {b c e V : ℝ} (he : 0 < e)
    (hce : 1105 * e ≤ 1519 * c) (hbe : 2401 * b ≤ 3337 * e)
    (hlo : 31 * c / 17 < V) (hhi : V < 49 * b / 47) :
    (8 : ℝ)⁻¹ ≤ circDist (V * ((49 / e) / 8)) := by
  have hl : 65 ≤ V * (49 / e) := by
    rw [← mul_div_assoc, le_div_iff₀ he]
    linarith
  have hu : V * (49 / e) ≤ 71 := by
    rw [← mul_div_assoc, div_le_iff₀ he]
    linarith
  apply TwoPinner.clear_of_band (N := 8) <;> norm_num <;> nlinarith

/-- Exact core band guards for this named replacement. -/
theorem core_clear (d : Fin 6 → ℝ) {e : ℝ} (he : 0 < e)
    (hlo : ∀ i, (8 * (laps i : ℝ) + 1) * e ≤ 49 * d i)
    (hhi : ∀ i, 49 * d i ≤ (8 * (laps i : ℝ) + 7) * e) :
    ∀ i, (8 : ℝ)⁻¹ ≤ circDist (d i * ((49 / e) / 8)) := by
  intro i
  have hl : 8 * (laps i : ℝ) + 1 ≤ d i * (49 / e) := by
    rw [← mul_div_assoc, le_div_iff₀ he]
    nlinarith [hlo i]
  have hu : d i * (49 / e) ≤ 8 * (laps i : ℝ) + 7 := by
    rw [← mul_div_assoc, div_le_iff₀ he]
    nlinarith [hhi i]
  apply TwoPinner.clear_of_band (N := laps i) <;> nlinarith

/-- All added readings V ≥ b are covered, not just sampled residual values.
The early windows either supply isolation or force the residual interval.
The new guards cover that entire interval at one explicitly named instant. -/
theorem family_isolated (d : Fin 6 → ℝ) {b c e V : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hb7 : b ≤ 7) (he : 101 / 20 ≤ e)
    (hcross : 51 * b ≤ 91 * c) (hV : b ≤ V) (hd : ∀ i, 0 < d i)
    (hlo : ∀ w i, (8 * (MovingCoreWindows.laps w i : ℝ) + 1) *
      MovingCoreWindows.setter c e w ≤ MovingCoreWindows.opening w * d i)
    (hhi : ∀ w i, MovingCoreWindows.closing w * d i ≤
      (8 * (MovingCoreWindows.laps w i : ℝ) + 7) * b)
    (hce : 1105 * e ≤ 1519 * c) (hbe : 2401 * b ≤ 3337 * e)
    (hflo : ∀ i, (8 * (laps i : ℝ) + 1) * e ≤ 49 * d i)
    (hfhi : ∀ i, 49 * d i ≤ (8 * (laps i : ℝ) + 7) * e) :
    ∃ t : ℝ, 0 < t ∧ (8 : ℝ)⁻¹ ≤ circDist (V * t) ∧
      ∀ i, (8 : ℝ)⁻¹ ≤ circDist (d i * t) := by
  apply MovingCoreWindows.family_isolated_of_residual d hb hc hb7 he hcross hV hd hlo hhi
  intro hvlo hvhi
  have hep : 0 < e := by linarith
  exact ⟨(49 / e) / 8, div_pos (div_pos (by norm_num) hep) (by norm_num),
    residual_clear hep hce hbe hvlo hvhi, core_clear d hep hflo hfhi⟩

end LRC.MovingCoreFallback
