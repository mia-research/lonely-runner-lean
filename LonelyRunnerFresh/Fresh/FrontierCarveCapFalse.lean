import Mathlib
import Fresh.FrontierFamilyCapV2

/-!
# `FrontierCarveCap` is false: an explicit counterexample, native

Written 2026-11-06.  New file; nothing existing is edited.  `Fresh.FrontierFamilyCapV2.FrontierCarveCap`
(the OWED classifier: a carve of `[1,7]` by six sorted readings with `47/7 < ρ₆ < 7` and `15 < ρ₇` forces the
seam `31/ρ₆ ≤ 73/ρ₇`) is refuted by the readings

  ρ₂ = 2767/1000, ρ₃ = 749/200, ρ₄ = 957/200, ρ₅ = 123/20, ρ₆ = 683/100, ρ₇ = 11889/500.

They carve `[1,7]` (a chain of 21 zones, each overlapping the next strictly; `carve_ce`), `ρ₆ = 6.83` lies in
`(47/7, 7)`, `ρ₇ = 23.778 > 15`, and `31/ρ₆ > 73/ρ₇`.  The seam interval `(73/ρ₇, 31/ρ₆)` is covered by the
zones of `ρ₂, ρ₃, ρ₄, ρ₅, ρ₆` (the routing caveat in the docstring of `FrontierFamilyCapV2`, realised).  The exact
cascade (`experiments/n8/frontier_seam_cascade_v1.py`) lands this arrangement at `R = 6500/683` in `W₁` after 24 moves.
The chain below is `experiments/n8/frontier_seam_cover_v1.py`.
-/

namespace Fresh.FrontierCarveCapFalse

open Fresh.FrontierFamilyCapV2

/-- The six readings, as a finite set. -/
noncomputable def ceSet : Finset ℝ := ({ (2767 / 1000 : ℝ), (749 / 200 : ℝ), (957 / 200 : ℝ), (123 / 20 : ℝ), (683 / 100 : ℝ), (11889 / 500 : ℝ) } : Finset ℝ)

theorem mem2 : (2767 / 1000 : ℝ) ∈ ceSet := by simp [ceSet]
theorem mem3 : (749 / 200 : ℝ) ∈ ceSet := by simp [ceSet]
theorem mem4 : (957 / 200 : ℝ) ∈ ceSet := by simp [ceSet]
theorem mem5 : (123 / 20 : ℝ) ∈ ceSet := by simp [ceSet]
theorem mem6 : (683 / 100 : ℝ) ∈ ceSet := by simp [ceSet]
theorem mem7 : (11889 / 500 : ℝ) ∈ ceSet := by simp [ceSet]

set_option maxHeartbeats 4000000 in
/-- The counterexample carves `[1,7]`: a chain of 21 zones, each overlapping the next strictly. -/
theorem carve_ce : CarvesOneSeven ceSet := by
  intro R hlo hhi
  rcases lt_or_ge R (12500 / 11889 : ℝ) with s0 | s0'
  · exact ⟨(11889 / 500 : ℝ), mem7, 3, by push_cast; constructor <;> linarith⟩
  rcases lt_or_ge R (900 / 683 : ℝ) with s1 | s1'
  · exact ⟨(683 / 100 : ℝ), mem6, 1, by push_cast; constructor <;> linarith⟩
  rcases lt_or_ge R (60 / 41 : ℝ) with s2 | s2'
  · exact ⟨(123 / 20 : ℝ), mem5, 1, by push_cast; constructor <;> linarith⟩
  rcases lt_or_ge R (600 / 319 : ℝ) with s3 | s3'
  · exact ⟨(957 / 200 : ℝ), mem4, 1, by push_cast; constructor <;> linarith⟩
  rcases lt_or_ge R (1800 / 749 : ℝ) with s4 | s4'
  · exact ⟨(749 / 200 : ℝ), mem3, 1, by push_cast; constructor <;> linarith⟩
  rcases lt_or_ge R (1700 / 683 : ℝ) with s5 | s5'
  · exact ⟨(683 / 100 : ℝ), mem6, 2, by push_cast; constructor <;> linarith⟩
  rcases lt_or_ge R (340 / 123 : ℝ) with s6 | s6'
  · exact ⟨(123 / 20 : ℝ), mem5, 2, by push_cast; constructor <;> linarith⟩
  rcases lt_or_ge R (9000 / 2767 : ℝ) with s7 | s7'
  · exact ⟨(2767 / 1000 : ℝ), mem2, 1, by push_cast; constructor <;> linarith⟩
  rcases lt_or_ge R (3400 / 957 : ℝ) with s8 | s8'
  · exact ⟨(957 / 200 : ℝ), mem4, 2, by push_cast; constructor <;> linarith⟩
  rcases lt_or_ge R (2500 / 683 : ℝ) with s9 | s9'
  · exact ⟨(683 / 100 : ℝ), mem6, 3, by push_cast; constructor <;> linarith⟩
  rcases lt_or_ge R (44500 / 11889 : ℝ) with s10 | s10'
  · exact ⟨(11889 / 500 : ℝ), mem7, 11, by push_cast; constructor <;> linarith⟩
  rcases lt_or_ge R (500 / 123 : ℝ) with s11 | s11'
  · exact ⟨(123 / 20 : ℝ), mem5, 3, by push_cast; constructor <;> linarith⟩
  rcases lt_or_ge R (3400 / 749 : ℝ) with s12 | s12'
  · exact ⟨(749 / 200 : ℝ), mem3, 2, by push_cast; constructor <;> linarith⟩
  rcases lt_or_ge R (3300 / 683 : ℝ) with s13 | s13'
  · exact ⟨(683 / 100 : ℝ), mem6, 4, by push_cast; constructor <;> linarith⟩
  rcases lt_or_ge R (5000 / 957 : ℝ) with s14 | s14'
  · exact ⟨(957 / 200 : ℝ), mem4, 3, by push_cast; constructor <;> linarith⟩
  rcases lt_or_ge R (220 / 41 : ℝ) with s15 | s15'
  · exact ⟨(123 / 20 : ℝ), mem5, 4, by push_cast; constructor <;> linarith⟩
  rcases lt_or_ge R (21500 / 3963 : ℝ) with s16 | s16'
  · exact ⟨(11889 / 500 : ℝ), mem7, 16, by push_cast; constructor <;> linarith⟩
  rcases lt_or_ge R (17000 / 2767 : ℝ) with s17 | s17'
  · exact ⟨(2767 / 1000 : ℝ), mem2, 2, by push_cast; constructor <;> linarith⟩
  rcases lt_or_ge R (5000 / 749 : ℝ) with s18 | s18'
  · exact ⟨(749 / 200 : ℝ), mem3, 3, by push_cast; constructor <;> linarith⟩
  rcases lt_or_ge R (200 / 29 : ℝ) with s19 | s19'
  · exact ⟨(957 / 200 : ℝ), mem4, 4, by push_cast; constructor <;> linarith⟩
  exact ⟨(683 / 100 : ℝ), mem6, 6, by push_cast; constructor <;> linarith⟩

/-- **`FrontierCarveCap` is false.** -/
theorem not_frontierCarveCap : ¬ FrontierCarveCap := by
  intro h
  have := h (2767 / 1000) (749 / 200) (957 / 200) (123 / 20) (683 / 100) (11889 / 500)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) carve_ce
  norm_num at this

#print axioms carve_ce
#print axioms not_frontierCarveCap

end Fresh.FrontierCarveCapFalse
