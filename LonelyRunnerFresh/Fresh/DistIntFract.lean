import Mathlib
import Fresh.Framework

/-!
# `distInt` is the distance to the nearest integer through the fractional part

Written 2026-10-25.  New file.  `distInt_eq_fract`: `distInt x = min (fract x) (1 - fract x)`.  This is the form the ported order-six and order-seven files use (`circDist`).  Grade [L].
-/

namespace Fresh

theorem distInt_eq_fract (x : ℝ) : distInt x = min (Int.fract x) (1 - Int.fract x) := by
  unfold distInt
  have hf := Int.floor_add_fract x
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  by_cases h : Int.fract x < 1 / 2
  · have hr : round x = ⌊x⌋ := by
      rw [round_eq, Int.floor_eq_iff]
      constructor <;> linarith
    rw [hr, min_eq_left (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · push_neg at h
    have hr : round x = ⌊x⌋ + 1 := by
      rw [round_eq, Int.floor_eq_iff]
      push_cast
      constructor <;> linarith
    rw [hr, min_eq_right (by linarith), abs_of_nonpos (by push_cast; linarith)]
    push_cast
    linarith

#print axioms distInt_eq_fract

end Fresh
