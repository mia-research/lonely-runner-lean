import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Cascade
import Fresh.CascadeLandingG
import Fresh.SelfMoverCommon
import Fresh.SelfMoverAllCommon

/-!
# The ratio condition as a landing: every arrangement whose readings lie within a factor of seven

Written 2026-10-23.  New file.  For any arrangement `v` and subject `k`, if the least disparity `m` of `k` is attained and every disparity lies
in `[m, 7 m]`, then `1/(8m)` is the first isolation instant and the cascade from `1/(8m)` fixes at once there.  At `t = 1/(8m)` the reading
`d` has `d t = d/(8m) ∈ [1/8, 7/8]`, which is clear; before it, the least reading is in the way.  This holds for any number of movers.
Grades: [L].
-/

open Classical

namespace Fresh.OneMover

open Fresh

theorem ratio_firstIso (v : Fin 8 → ℝ) (k : Fin 8) (m : ℝ) (hm : 0 < m)
    (hmem : ∃ i, i ≠ k ∧ |v i - v k| = m)
    (hr : ∀ i, i ≠ k → m ≤ |v i - v k| ∧ |v i - v k| ≤ 7 * m) :
    FirstIso v k (1 / (8 * m)) := by
  have hT : 0 < 1 / (8 * m) := by positivity
  refine ⟨?_, ?_⟩
  · intro i hik
    obtain ⟨h1, h2⟩ := hr i hik
    have e : |v i - v k| * (1 / (8 * m)) = |v i - v k| / (8 * m) := by ring
    have hc : (1 / 8 : ℝ) ≤ distInt (|v i - v k| * (1 / (8 * m))) := by
      apply Fresh.Localisation.clear_of_window 0
      · push_cast; rw [e, le_div_iff₀ (by positivity)]; nlinarith
      · push_cast; rw [e, div_le_iff₀ (by positivity)]; nlinarith
    rcases abs_cases (v i - v k) with ⟨ha, _⟩ | ⟨ha, _⟩
    · rw [ha] at hc; exact hc
    · rw [ha] at hc
      have : (-(v i - v k)) * (1 / (8 * m)) = -((v i - v k) * (1 / (8 * m))) := by ring
      rw [this, Fresh.Localisation.distInt_neg] at hc; exact hc
  · intro s hs0 hs
    by_contra hlt
    push Not at hlt
    obtain ⟨i, hik, him⟩ := hmem
    have h := hs i hik
    have hin := inway_before hm hs0 hlt
    have : distInt ((v i - v k) * s) = distInt (m * s) := by
      rcases abs_cases (v i - v k) with ⟨ha, _⟩ | ⟨ha, _⟩
      · rw [ha] at him; rw [him]
      · rw [ha] at him
        have e2 : (v i - v k) = -m := by linarith
        rw [e2, neg_mul, Fresh.Localisation.distInt_neg]
    rw [this] at h
    linarith

/-- **The ratio condition as a landing.** -/
theorem ratio_lands (v : Fin 8 → ℝ) (k : Fin 8) (m : ℝ) (hm : 0 < m)
    (hmem : ∃ i, i ≠ k ∧ |v i - v k| = m)
    (hr : ∀ i, i ≠ k → m ≤ |v i - v k| ∧ |v i - v k| ≤ 7 * m) :
    Lands v k m := by
  have ham : m ∈ disparitySet v k := by
    obtain ⟨i, hik, him⟩ := hmem
    exact Finset.mem_image.mpr ⟨i, Finset.mem_erase.mpr ⟨hik, Finset.mem_univ _⟩, him⟩
  exact lands_of_first v k m (1 / (8 * m)) ham (by positivity) (ratio_firstIso v k m hm hmem hr)

#print axioms ratio_firstIso
#print axioms ratio_lands

end Fresh.OneMover
