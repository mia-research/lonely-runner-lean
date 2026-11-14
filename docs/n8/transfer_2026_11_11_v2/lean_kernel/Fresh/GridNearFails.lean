import Mathlib
import Fresh.Framework

/-!
# An arrangement that is not within `d/8` of any grid (E775)

Written 2026-11-02.  New file; nothing existing is edited.  Owner (2026-11-02): *"Prove (A)"*, where (A) (E774) is: every
admissible arrangement is within `d/8` of some grid, `|w j - (v₀ + idx j * d)| ≤ d/8` with `idx` a complete residue
system mod 8 (`IsGrid`).

* `NearGrid w`: `w` is within `d/8` of a grid of step `d`.
* `not_nearGrid_w9`: `(1, 2, 3, 4, 5, 6, 7, 9)` is not.  Each unit gap forces the same index step `a`, the gap `2` forces
  `2a`, so the indices of the speeds `1` and `9` differ by `8a` and share a residue.

Grades: [L].  No counting or covering step.
-/

namespace Fresh.GridNearFails

open Fresh

/-- `w` lies within `d/8` of a grid of step `d` (`IsGrid` with a deviation of at most `d/8` per runner). -/
def NearGrid (w : Fin 8 → ℝ) : Prop :=
  ∃ (d v₀ : ℝ) (idx : Fin 8 → ℤ), 0 < d ∧ CompleteResidues idx ∧ ∀ j, |w j - (v₀ + (idx j : ℝ) * d)| ≤ d / 8

/-- The arrangement `(1, 2, 3, 4, 5, 6, 7, 9)`. -/
noncomputable def w9 : Fin 8 → ℝ := ![1, 2, 3, 4, 5, 6, 7, 9]

theorem int_eq_of_close {m n : ℤ} {d : ℝ} (hd : 0 < d) (h1 : (m : ℝ) * d - n * d < d) (h2 : (n : ℝ) * d - m * d < d) :
    m = n := by
  have a : ((m - n : ℤ) : ℝ) * d < 1 * d := by push_cast; linarith
  have b : ((n - m : ℤ) : ℝ) * d < 1 * d := by push_cast; linarith
  have a' : ((m - n : ℤ) : ℝ) < 1 := lt_of_mul_lt_mul_right a hd.le
  have b' : ((n - m : ℤ) : ℝ) < 1 := lt_of_mul_lt_mul_right b hd.le
  have a'' : m - n < 1 := by exact_mod_cast a'
  have b'' : n - m < 1 := by exact_mod_cast b'
  omega

/-- **`(1, ..., 7, 9)` is not within `d/8` of any grid** [L]. -/
theorem not_nearGrid_w9 : ¬ NearGrid w9 := by
  rintro ⟨d, v₀, idx, hd, hc, h⟩
  have H : ∀ j, -(d / 8) ≤ w9 j - (v₀ + (idx j : ℝ) * d) ∧ w9 j - (v₀ + (idx j : ℝ) * d) ≤ d / 8 :=
    fun j => abs_le.mp (h j)
  obtain ⟨a0, b0⟩ := H 0; obtain ⟨a1, b1⟩ := H 1; obtain ⟨a2, b2⟩ := H 2; obtain ⟨a3, b3⟩ := H 3
  obtain ⟨a4, b4⟩ := H 4; obtain ⟨a5, b5⟩ := H 5; obtain ⟨a6, b6⟩ := H 6; obtain ⟨a7, b7⟩ := H 7
  simp [w9] at a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7
  have e1 : idx 2 - idx 1 = idx 1 - idx 0 := int_eq_of_close hd (by push_cast; linarith) (by push_cast; linarith)
  have e2 : idx 3 - idx 2 = idx 1 - idx 0 := int_eq_of_close hd (by push_cast; linarith) (by push_cast; linarith)
  have e3 : idx 4 - idx 3 = idx 1 - idx 0 := int_eq_of_close hd (by push_cast; linarith) (by push_cast; linarith)
  have e4 : idx 5 - idx 4 = idx 1 - idx 0 := int_eq_of_close hd (by push_cast; linarith) (by push_cast; linarith)
  have e5 : idx 6 - idx 5 = idx 1 - idx 0 := int_eq_of_close hd (by push_cast; linarith) (by push_cast; linarith)
  have e6 : idx 7 - idx 6 = 2 * (idx 1 - idx 0) :=
    int_eq_of_close hd (by push_cast; linarith) (by push_cast; linarith)
  have hr : idx 7 % 8 = idx 0 % 8 := by omega
  exact absurd (hc 7 0 hr) (by decide)

#print axioms int_eq_of_close
#print axioms not_nearGrid_w9

end Fresh.GridNearFails
