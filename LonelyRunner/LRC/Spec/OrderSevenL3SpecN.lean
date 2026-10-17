import LonelyRunner.LRC.Spec.OrderSevenL3CoreN

/-!
# Order seven, level 3: what the masks mean (kernel-checked)

* `maskL3_spec`: for `i, j < 294`, bit `j` of `maskL3 i` is set iff `GridOK 3 (unitL3 j) (unitL3 i)`.
* `maskL3_small`: no bit at or above 294 is set.
* `unitL3_idx`: every unit `u < 343` is `unitL3 (u - 1 - u / 7)`, and `unitL3 i` is a unit below 343 for `i < 294`.
* `allR_append`: `allR` splits over consecutive ranges.

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option exponentiation.threshold 400

namespace LRC.O7L3
open LRC.O7Grid

def maskSpecB : Bool :=
  allR 294 0 fun i => allR 294 0 fun j => (maskL3 i).testBit j == decide (GridOK 3 (unitL3 j) (unitL3 i))

theorem maskSpecB_ok : maskSpecB = true := by decide +kernel

theorem maskL3_spec {i j : ℕ} (hi : i < 294) (hj : j < 294) :
    (maskL3 i).testBit j = true ↔ GridOK 3 (unitL3 j) (unitL3 i) := by
  have h := allR_spec _ _ _ (allR_spec _ _ _ maskSpecB_ok i (Nat.zero_le _) (by omega)) j (Nat.zero_le _) (by omega)
  simp only [beq_iff_eq] at h
  rw [h]; simp

def smallB : Bool := allR 294 0 fun i => decide (maskL3 i < 2 ^ 294)

theorem smallB_ok : smallB = true := by decide +kernel

theorem maskL3_small {i j : ℕ} (hi : i < 294) (hj : 294 ≤ j) : (maskL3 i).testBit j = false := by
  have h := allR_spec _ _ _ smallB_ok i (Nat.zero_le _) (by omega)
  simp only [decide_eq_true_eq] at h
  exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hj))

def idxB : Bool :=
  allR 343 0 fun u => u % 7 == 0 || (unitL3 (u - 1 - u / 7) == u && decide (u - 1 - u / 7 < 294))

theorem idxB_ok : idxB = true := by decide +kernel

theorem unitL3_idx {u : ℕ} (hu : u < 343) (h7 : u % 7 ≠ 0) :
    unitL3 (u - 1 - u / 7) = u ∧ u - 1 - u / 7 < 294 := by
  have h := allR_spec _ _ _ idxB_ok u (Nat.zero_le _) (by omega)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact absurd h h7
  · exact h

def unitB : Bool := allR 294 0 fun i => decide (unitL3 i < 343) && unitL3 i % 7 != 0

theorem unitB_ok : unitB = true := by decide +kernel

theorem unitL3_unit {i : ℕ} (hi : i < 294) : unitL3 i < 343 ∧ unitL3 i % 7 ≠ 0 := by
  have h := allR_spec _ _ _ unitB_ok i (Nat.zero_le _) (by omega)
  simpa [Bool.and_eq_true, bne_iff_ne] using h

theorem unitL3_zero : unitL3 0 = 1 := by decide +kernel

theorem allR_append : ∀ (m n i : ℕ) (f : ℕ → Bool), allR (m + n) i f = (allR m i f && allR n (i + m) f)
  | 0, n, i, f => by simp [allR]
  | m + 1, n, i, f => by
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [allR]
    rw [allR_append m n (i + 1) f, show i + 1 + m = i + (m + 1) by omega, Bool.and_assoc]

end LRC.O7L3
