import Mathlib

/-!
# The cascade's three move types: sweep down, bridge up, bridge down

2026-09-27.  Running record: `RUNNING_LOG_order8_v1.md` E142.

A move of the cascade ends at a runner `a`'s exit from its lap-`k` window, `R = (8k+1)/s_a` (positions `s·R` in eighths).
The next move is set by a runner `b` whose window contains that point: `8l − 1 < s_b·R < 8l + 1`.  Because the speeds are
ordered, the laps are ordered at every instant, and so:

* `lap_lt_of_faster`: a faster runner in the window is on a later lap (`k < l`): a **bridge up**;
* `lap_le_of_slower`: a slower runner is on the same or an earlier lap (`l ≤ k`): a **sweep step** or a **bridge down**;
* `sweep_ratio`: a sweep step (slower runner, same lap) needs `s_a(8k − 1) < s_b(8k + 1)`: consecutive ratio below
  `ρ_k = (8k+1)/(8k−1)`;
* `sweep_ratio_mono`: `ρ_{k+1} < ρ_k`, so a gap that stops a sweep on lap `k` stops it on every later lap.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.SweepBridge

/-- **Bridge up.**  At `a`'s exit on lap `k`, a faster runner inside its own lap-`l` window is on a later lap. -/
theorem lap_lt_of_faster {sa sb : ℝ} {k l : ℤ} (ha : 0 < sa) (hab : sa < sb)
    (hw : sb * ((8 * k + 1) / sa) < 8 * l + 1) (hk : 0 ≤ k) : k < l := by
  have h1 : (8 * k + 1 : ℝ) < sb * ((8 * k + 1) / sa) := by
    rw [mul_div_assoc', lt_div_iff₀ ha]
    have : (0 : ℝ) < 8 * k + 1 := by have : (0 : ℝ) ≤ k := by exact_mod_cast hk
                                     linarith
    nlinarith
  have : (8 * k + 1 : ℝ) < 8 * l + 1 := lt_trans h1 hw
  have : (k : ℝ) < l := by linarith
  exact_mod_cast this

/-- **Sweep step or bridge down.**  A slower runner inside its lap-`l` window at `a`'s exit is on lap `l ≤ k`. -/
theorem lap_le_of_slower {sa sb : ℝ} {k l : ℤ} (ha : 0 < sa) (hba : sb < sa)
    (hw : (8 * l - 1 : ℝ) < sb * ((8 * k + 1) / sa)) (hk : 0 ≤ k) : l ≤ k := by
  have h1 : sb * ((8 * k + 1) / sa) < (8 * k + 1 : ℝ) := by
    rw [mul_div_assoc', div_lt_iff₀ ha]
    have : (0 : ℝ) < 8 * k + 1 := by have : (0 : ℝ) ≤ k := by exact_mod_cast hk
                                     linarith
    nlinarith
  have : (8 * l - 1 : ℝ) < 8 * k + 1 := lt_trans hw h1
  have : (8 * l : ℤ) < 8 * k + 2 := by exact_mod_cast (by linarith : (8 * l : ℝ) < 8 * k + 2)
  omega

/-- **A sweep step needs a close ratio.**  A runner in its lap-`k` window at `a`'s lap-`k` exit satisfies
`s_a(8k − 1) < s_b(8k + 1)`. -/
theorem sweep_ratio {sa sb : ℝ} {k : ℤ} (ha : 0 < sa)
    (hw : (8 * k - 1 : ℝ) < sb * ((8 * k + 1) / sa)) : sa * (8 * k - 1) < sb * (8 * k + 1) := by
  rw [mul_div_assoc', lt_div_iff₀ ha] at hw
  linarith

/-- **Sweeps narrow with the lap.**  `(8k+9)/(8k+7) < (8k+1)/(8k−1)` for `k ≥ 1` (denominators positive); the cross-multiplied form holds for every `k`. -/
theorem sweep_ratio_mono (k : ℝ) : (8 * k + 9) * (8 * k - 1) < (8 * k + 1) * (8 * k + 7) := by
  nlinarith

/-- A consecutive ratio that stops a lap-`k` sweep stops every later one: if `s_b(8k+1) ≤ s_a(8k−1)` then
`s_b(8k+9) ≤ s_a(8k+7)`. -/
theorem sweep_stop_persists {sa sb k : ℝ} (hb : 0 < sb) (hk : 1 ≤ k)
    (h : sb * (8 * k + 1) ≤ sa * (8 * k - 1)) : sb * (8 * k + 9) ≤ sa * (8 * k + 7) := by
  have hm := sweep_ratio_mono k
  have hpos : (0 : ℝ) < 8 * k - 1 := by linarith
  -- sa ≥ sb (8k+1)/(8k-1) and (8k+1)/(8k-1) > (8k+9)/(8k+7)
  have : sb * (8 * k + 9) * (8 * k - 1) ≤ sa * (8 * k + 7) * (8 * k - 1) := by nlinarith
  nlinarith

end LRC.SweepBridge
