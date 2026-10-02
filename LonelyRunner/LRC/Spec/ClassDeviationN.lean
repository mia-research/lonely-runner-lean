import LonelyRunner.LRC.Spec.IntegerGridN
import LonelyRunner.LRC.Spec.PinchOpenN
import LonelyRunner.LRC.Spec.TwoPinnerN

/-!
# A class instant sees a reading only through its deviation, scaled by the class

2026-10-02 (running log E307).  At the AP scale `d` the class instants are `t = a/(8d)`, `a` an integer (`R = a` in
`R = 8·d·t`).  A reading `x = d·(8n + ε)` (`n` an integer, `ε` its deviation from the grid slot `0`) sits there at
`a·ε` eighths of a lap, whatever `n` is: the lap is invisible and the deviation is scaled by the class.

* `circDist_class_deviation`: `circDist (x·t) = circDist (a·ε/8)`.
* `class_blocked`: `|a·ε| < 1` ⇒ in the way.
* `class_clear_of_band`, `class_clear_of_band_neg`: `1 ≤ a·ε ≤ 7` (or `−7 ≤ a·ε ≤ −1`) ⇒ clear.
* `lapped_fastest`: for the lapped fastest of B1 (`n = 1`, `|ε| < 1`): in the way at class `a = 1`, and clear at class `a`
  as soon as `1 ≤ a·|ε| ≤ 7`.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.ClassDeviation

theorem circDist_class_deviation {d ε : ℝ} (hd : 0 < d) (n a : ℤ) :
    circDist (d * (8 * (n : ℝ) + ε) * ((a : ℝ) / (8 * d))) = circDist ((a : ℝ) * ε / 8) := by
  have e : d * (8 * (n : ℝ) + ε) * ((a : ℝ) / (8 * d)) = (a : ℝ) * ε / 8 + ((a * n : ℤ) : ℝ) := by
    push_cast; field_simp; ring
  rw [e, LRC.PinchOpen.circDist_add_int_po]

theorem class_blocked {d ε : ℝ} (hd : 0 < d) (n a : ℤ) (h : |(a : ℝ) * ε| < 1) :
    circDist (d * (8 * (n : ℝ) + ε) * ((a : ℝ) / (8 * d))) < (8 : ℝ)⁻¹ := by
  rw [circDist_class_deviation hd n a]
  have := ConstructionN.circDist_le_abs_sub_int ((a : ℝ) * ε / 8) 0
  simp only [Int.cast_zero, sub_zero] at this
  have h8 : |(a : ℝ) * ε / 8| = |(a : ℝ) * ε| / 8 := by rw [abs_div]; norm_num
  rw [h8] at this
  linarith

theorem class_clear_of_band {d ε : ℝ} (hd : 0 < d) (n a : ℤ) (h1 : 1 ≤ (a : ℝ) * ε) (h2 : (a : ℝ) * ε ≤ 7) :
    (8 : ℝ)⁻¹ ≤ circDist (d * (8 * (n : ℝ) + ε) * ((a : ℝ) / (8 * d))) := by
  rw [circDist_class_deviation hd n a]
  exact LRC.TwoPinner.clear_of_band (N := 0) (by push_cast; linarith) (by push_cast; linarith)

theorem class_clear_of_band_neg {d ε : ℝ} (hd : 0 < d) (n a : ℤ) (h1 : (a : ℝ) * ε ≤ -1)
    (h2 : -7 ≤ (a : ℝ) * ε) :
    (8 : ℝ)⁻¹ ≤ circDist (d * (8 * (n : ℝ) + ε) * ((a : ℝ) / (8 * d))) := by
  rw [circDist_class_deviation hd n a]
  have e : (a : ℝ) * ε / 8 = -(((-a : ℤ) : ℝ) * ε / 8) := by push_cast; ring
  rw [e, LRC.PinchOpen.circDist_neg_po]
  exact LRC.TwoPinner.clear_of_band (N := 0) (by push_cast; linarith) (by push_cast; linarith)

/-- The lapped fastest runner: in the way at class `1` when `|ε| < 1`, clear at class `a` once `1 ≤ a·|ε| ≤ 7`. -/
theorem lapped_fastest {d ε : ℝ} (hd : 0 < d) (hε : |ε| < 1) :
    circDist (d * (8 * ((1 : ℤ) : ℝ) + ε) * (((1 : ℤ) : ℝ) / (8 * d))) < (8 : ℝ)⁻¹ := by
  apply class_blocked hd 1 1
  simpa using hε

end LRC.ClassDeviation
