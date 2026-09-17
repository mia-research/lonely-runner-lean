import LonelyRunner.LRC.Cascade.Iteration

/-!
# Runners in the way together

Part of the cascade artefact (`LRC/Cascade/`).  Threshold `1/n`.

Manuscript Appendix A, item 4 (H1).  The development record states it as: same-side runners are in the
way together only where their connecting difference is within `1/4` of a lap line.  The manuscript gives
the sharper form and records it as proved but **not formalised**; it is formalised here.

The content is the triangle inequality for the circle metric, which the tree did not have:
`circDist (x − y) ≤ circDist x + circDist y` (`circDist_sub_le`).  Two runners each within `1/n` of the
subject put their connecting difference within `2/n` of a lap line, and within `1/n` when they are on
the same side of it.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Together

open ConstructionN MomentIterationN

variable {n : ℕ} [Fact (2 ≤ n)]

/-- **The triangle inequality for the circle metric.**  `circDist` is the distance to the nearest
integer, so a difference is at most the sum of the two distances. -/
theorem circDist_sub_le (x y : ℝ) : circDist (x - y) ≤ circDist x + circDist y := by
  obtain ⟨j, hj⟩ := circDist_eq_abs_sub_some_int x
  obtain ⟨k, hk⟩ := circDist_eq_abs_sub_some_int y
  have h := circDist_le_abs_sub_int (x - y) (j - k)
  have e : x - y - ((j - k : ℤ) : ℝ) = (x - (j : ℝ)) - (y - (k : ℝ)) := by push_cast; ring
  rw [e] at h
  calc circDist (x - y) ≤ |(x - (j : ℝ)) - (y - (k : ℝ))| := h
    _ ≤ |x - (j : ℝ)| + |y - (k : ℝ)| := abs_sub _ _
    _ = circDist x + circDist y := by rw [← hj, ← hk]

/-- **Two runners in the way together (H1).**  If the runners at differences `d` and `e` are both in the
way at `t`, their connecting difference `d − e` is within `2/n` of a lap line at `t`. -/
theorem connecting_difference_near_lap {d e t : ℝ} (hd : inWay n d t) (he : inWay n e t) :
    circDist ((d - e) * t) < 2 * (n : ℝ)⁻¹ := by
  have e1 : (d - e) * t = d * t - e * t := by ring
  rw [e1]
  exact lt_of_le_of_lt (circDist_sub_le _ _) (by unfold inWay at hd he; linarith)

/-- **The same-side form.**  If both runners sit on the same side of the lap line — both fractional parts
below `1/n`, or both above `1 − 1/n` — the connecting difference is within `1/n` of it. -/
theorem connecting_difference_same_side {d e t : ℝ}
    (h : (Int.fract (d * t) < (n : ℝ)⁻¹ ∧ Int.fract (e * t) < (n : ℝ)⁻¹) ∨
         (1 - (n : ℝ)⁻¹ < Int.fract (d * t) ∧ 1 - (n : ℝ)⁻¹ < Int.fract (e * t))) :
    circDist ((d - e) * t) < (n : ℝ)⁻¹ := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hh0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
  have e1 : (d - e) * t = d * t - e * t := by ring
  have key : circDist (d * t - e * t) ≤ |Int.fract (d * t) - Int.fract (e * t)| := by
    have hx : Int.fract (d * t) = d * t - (⌊d * t⌋ : ℝ) := rfl
    have hy : Int.fract (e * t) = e * t - (⌊e * t⌋ : ℝ) := rfl
    have h2 := circDist_le_abs_sub_int (d * t - e * t) (⌊d * t⌋ - ⌊e * t⌋)
    have e2 : d * t - e * t - ((⌊d * t⌋ - ⌊e * t⌋ : ℤ) : ℝ)
        = Int.fract (d * t) - Int.fract (e * t) := by rw [hx, hy]; push_cast; ring
    rw [e2] at h2; exact h2
  rw [e1]
  refine lt_of_le_of_lt key ?_
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := Int.fract_nonneg (d * t); have := Int.fract_nonneg (e * t)
    rw [abs_lt]; constructor <;> linarith
  · have := Int.fract_lt_one (d * t); have := Int.fract_lt_one (e * t)
    rw [abs_lt]; constructor <;> linarith

end Together
