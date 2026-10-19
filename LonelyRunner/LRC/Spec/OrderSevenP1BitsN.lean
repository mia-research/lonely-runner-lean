import LonelyRunner.LRC.Spec.OrderSevenU5SoundN
import LonelyRunner.LRC.Spec.OrderSevenP1DataN

namespace LRC.O7U5

theorem p210_eq : P210 = 2 ^ 210 := by decide +kernel

theorem ub_bits {b x : Nat} (h : (UB b).testBit x = true) : x < 210 := by
  by_contra hx
  have hlt : UB b < 2 ^ x := by
    have := Nat.mod_lt (UBALL >>> (210 * b)) (show 0 < P210 by rw [p210_eq]; positivity)
    rw [p210_eq] at this
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [Nat.testBit_eq_false_of_lt hlt] at h; simp at h

end LRC.O7U5
