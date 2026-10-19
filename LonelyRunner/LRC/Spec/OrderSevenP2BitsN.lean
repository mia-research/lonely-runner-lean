import LonelyRunner.LRC.Spec.OrderSevenP2SoundN

namespace LRC.O7P2

theorem pw_eq : PW = 2 ^ 245 := by decide +kernel

theorem ab_bits {b x : Nat} (h : (AB b).testBit x = true) : x < 245 := by
  by_contra hx
  have hlt : AB b < 2 ^ x := by
    have := Nat.mod_lt (ABALL >>> (245 * b)) (show 0 < PW by rw [pw_eq]; positivity)
    rw [pw_eq] at this
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [Nat.testBit_eq_false_of_lt hlt] at h; simp at h

end LRC.O7P2
