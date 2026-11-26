import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Cascade
import Fresh.OneMoverA
import Fresh.SelfMoverCommon
import Fresh.APLaw

/-!
# The AP-neighbourhood landing law: the arrangement statement for an end subject

Written 2026-10-23.  New file.  `apLaw_core`: for relative readings `x_i = i + e_i` (`|e_i| ≤ 1/64`) one of three chambers holds and gives the first clear instant
(`C1`: `x7 ≤ 7 x1`, `T = (0 + 1/8)/x1`; `C3`: `7 x1 < x7`, `3 x5 ≤ 5 x3`, `T = (1 + 1/8)/x3`; `C5`: `7 x1 < x7`, `5 x3 < 3 x5`, `T = (3 + 1/8)/x5`).
`apLaw_end0` / `apLaw_end7`: the same for the arrangement with the subject at the left / right end of the AP, every speed deviated by at most `1/128`
(so relative readings deviate by at most `1/64`), as `FirstIso` and then `Lands`.  Grades: [L].
-/

open Classical

namespace Fresh.OneMover

open Fresh

theorem apLaw_core (x1 x2 x3 x4 x5 x6 x7 : ℝ) (b1l : -(1/64 : ℝ) ≤ x1 - 1) (b1u : x1 - 1 ≤ (1/64 : ℝ)) (b2l : -(1/64 : ℝ) ≤ x2 - 2) (b2u : x2 - 2 ≤ (1/64 : ℝ)) (b3l : -(1/64 : ℝ) ≤ x3 - 3) (b3u : x3 - 3 ≤ (1/64 : ℝ)) (b4l : -(1/64 : ℝ) ≤ x4 - 4) (b4u : x4 - 4 ≤ (1/64 : ℝ)) (b5l : -(1/64 : ℝ) ≤ x5 - 5) (b5u : x5 - 5 ≤ (1/64 : ℝ)) (b6l : -(1/64 : ℝ) ≤ x6 - 6) (b6u : x6 - 6 ≤ (1/64 : ℝ)) (b7l : -(1/64 : ℝ) ≤ x7 - 7) (b7u : x7 - 7 ≤ (1/64 : ℝ)) :
    ∃ T : ℝ, 0 < T ∧ Clear7 x1 x2 x3 x4 x5 x6 x7 T ∧ (∀ s : ℝ, 0 < s → s < T → ¬ Clear7 x1 x2 x3 x4 x5 x6 x7 s) ∧
      ((x7 ≤ 7 * x1 ∧ T = ((0 : ℝ) + 1 / 8) / x1) ∨
       (7 * x1 < x7 ∧ 3 * x5 ≤ 5 * x3 ∧ T = ((1 : ℝ) + 1 / 8) / x3) ∨
       (7 * x1 < x7 ∧ 5 * x3 < 3 * x5 ∧ T = ((3 : ℝ) + 1 / 8) / x5)) := by
  have p1 : 0 < x1 := by linarith
  have p3 : 0 < x3 := by linarith
  have p5 : 0 < x5 := by linarith
  by_cases hA : 7 * x1 < x7
  · by_cases hB : 3 * x5 ≤ 5 * x3
    · obtain ⟨h1, h2⟩ := apLawC3 x1 x2 x3 x4 x5 x6 x7 b1l b1u b2l b2u b3l b3u b4l b4u b5l b5u b6l b6u b7l b7u hA hB
      refine ⟨_, by positivity, h1, h2, Or.inr (Or.inl ⟨hA, hB, rfl⟩)⟩
    · push Not at hB
      have hB' : 5 * x3 < 3 * x5 := by linarith
      obtain ⟨h1, h2⟩ := apLawC5 x1 x2 x3 x4 x5 x6 x7 b1l b1u b2l b2u b3l b3u b4l b4u b5l b5u b6l b6u b7l b7u hA hB'
      refine ⟨_, by positivity, h1, h2, Or.inr (Or.inr ⟨hA, hB', rfl⟩)⟩
  · push Not at hA
    have p2 : 0 < x2 := by linarith
    have p4 : 0 < x4 := by linarith
    have p6 : 0 < x6 := by linarith
    have p7 : 0 < x7 := by linarith
    refine ⟨((0 : ℝ) + 1 / 8) / x1, by positivity, ?_, ?_, Or.inl ⟨hA, rfl⟩⟩
    · refine ⟨?_1, ?_2, ?_3, ?_4, ?_5, ?_6, ?_7⟩
      · exact clear_at_end (d := x1) (d' := x1) (M := (0 : ℝ)) p1 (0 : ℤ) (by push_cast; linarith) (by push_cast; linarith)
      · exact clear_at_end (d := x1) (d' := x2) (M := (0 : ℝ)) p1 (0 : ℤ) (by push_cast; linarith) (by push_cast; linarith)
      · exact clear_at_end (d := x1) (d' := x3) (M := (0 : ℝ)) p1 (0 : ℤ) (by push_cast; linarith) (by push_cast; linarith)
      · exact clear_at_end (d := x1) (d' := x4) (M := (0 : ℝ)) p1 (0 : ℤ) (by push_cast; linarith) (by push_cast; linarith)
      · exact clear_at_end (d := x1) (d' := x5) (M := (0 : ℝ)) p1 (0 : ℤ) (by push_cast; linarith) (by push_cast; linarith)
      · exact clear_at_end (d := x1) (d' := x6) (M := (0 : ℝ)) p1 (0 : ℤ) (by push_cast; linarith) (by push_cast; linarith)
      · exact clear_at_end (d := x1) (d' := x7) (M := (0 : ℝ)) p1 (0 : ℤ) (by push_cast; linarith) (by push_cast; linarith)
    · intro s hs0 hsT hcl
      obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hcl
      have up : x1 * s < (0 : ℝ) + 1 / 8 := zone_hi p1 hsT
      have hw : distInt (x1 * s) < 1 / 8 := inWay_of_window (0 : ℤ) (by push_cast; nlinarith [mul_pos p1 hs0]) (by push_cast; linarith)
      linarith [c1]
#print axioms apLaw_core

end Fresh.OneMover
