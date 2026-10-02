import LonelyRunner.LRC.Spec.Order8SkeletonN
import LonelyRunner.LRC.ConstructionN.Band

/-!
# The grid through `D = 1` of an integer arrangement

2026-10-02 (running log E297).  An integer arrangement sits exactly on the grid: no deviation.

* `clear_rational_iff`: a reading `d` is clear at `t = k/(8m)` exactly when `d·k` is at distance at least `m` from every
  multiple of `8m` (equivalently `d·k mod 8m ∈ [m, 7m]`).
* `clear_of_dvd_not_dvd`: if `m ∣ d·k` and `8m ∤ d·k` then `d` is clear at `k/(8m)`.
* `clear_two_adic`: a reading with `2^e ∣ d` and `2^(e+3) ∤ d` is clear at `k/2^(e+3)` for every odd `k`
  (the runners of 2-adic valuation `v, v−1, v−2`, `e = v−2`, of the 2-adic refinement).
* `lonely8_of_no_multiple_of_eight`: no reading divisible by `8` ⇒ lonely at `1/8`.
* `lonely8_two_adic_window`: the same after scaling, every reading's 2-adic valuation in `[e, e+2]`.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.IntegerGrid

open LRC.Order8Skeleton

theorem clear_rational_iff {m : ℕ} (hm : 0 < m) (d k : ℤ) :
    (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * ((k : ℝ) / (8 * m))) ↔ ∀ z : ℤ, (m : ℤ) ≤ |d * k - 8 * m * z| := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have e : (d : ℝ) * ((k : ℝ) / (8 * m)) = ((d : ℝ) * k / m) / ((8 : ℕ) : ℝ) := by
    push_cast; field_simp
  rw [e]
  have h := ConstructionN.band_identity 8 (by norm_num) ((d : ℝ) * k / m)
  have h8 : (((8 : ℕ) : ℝ))⁻¹ = (8 : ℝ)⁻¹ := by norm_num
  rw [h8] at h
  rw [h]
  apply forall_congr'
  intro z
  have e2 : |(d : ℝ) * k / m - ((8 : ℕ) : ℝ) * z| = |(d : ℝ) * k - 8 * m * z| / m := by
    rw [show (d : ℝ) * k / m - ((8 : ℕ) : ℝ) * z = ((d : ℝ) * k - 8 * m * z) / m by
      push_cast; field_simp, abs_div, abs_of_pos hm0]
  rw [e2, le_div_iff₀ hm0, one_mul]
  constructor
  · intro h1; exact_mod_cast h1
  · intro h1; exact_mod_cast h1

theorem clear_of_dvd_not_dvd {m : ℕ} (hm : 0 < m) {d k : ℤ} (h1 : (m : ℤ) ∣ d * k)
    (h2 : ¬ (8 * m : ℤ) ∣ d * k) : (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * ((k : ℝ) / (8 * m))) := by
  rw [clear_rational_iff hm]
  intro z
  obtain ⟨q, hq⟩ := h1
  have hq8 : ¬ (8 : ℤ) ∣ q := by
    rintro ⟨r, rfl⟩
    exact h2 ⟨r, by rw [hq]; ring⟩
  have hne : q - 8 * z ≠ 0 := by
    intro h; apply hq8; exact ⟨z, by linarith⟩
  have e : d * k - 8 * m * z = m * (q - 8 * z) := by rw [hq]; ring
  rw [e, abs_mul, Int.abs_natCast]
  have : (1 : ℤ) ≤ |q - 8 * z| := Int.one_le_abs hne
  nlinarith [Int.natCast_pos.mpr hm]

theorem clear_two_adic (e : ℕ) {d k : ℤ} (hk : Odd k) (h1 : (2 : ℤ) ^ e ∣ d) (h2 : ¬ (2 : ℤ) ^ (e + 3) ∣ d) :
    (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * ((k : ℝ) / ((2 : ℝ) ^ (e + 3)))) := by
  have hm : 0 < 2 ^ e := by positivity
  have h8 : ((2 : ℝ) ^ (e + 3)) = 8 * ((2 ^ e : ℕ) : ℝ) := by push_cast; ring
  rw [h8]
  apply clear_of_dvd_not_dvd hm
  · push_cast; exact Dvd.dvd.mul_right h1 k
  · intro h
    apply h2
    have hc : IsCoprime ((2 : ℤ) ^ (e + 3)) k := by
      apply IsCoprime.pow_left
      obtain ⟨r, rfl⟩ := hk
      exact ⟨-r, 1, by ring⟩
    have h' : (2 : ℤ) ^ (e + 3) ∣ d * k := by push_cast at h; rwa [show (8 : ℤ) * 2 ^ e = 2 ^ (e + 3) by ring] at h
    exact hc.dvd_of_dvd_mul_right h'

theorem lonely8_of_no_multiple_of_eight (S : Finset ℕ) (h : ∀ d ∈ S, ¬ 8 ∣ d) : Lonely8 S := by
  refine ⟨1 / 8, by norm_num, fun d hd => ?_⟩
  have e : (d : ℝ) * (1 / 8) = ((d : ℤ) : ℝ) / ((8 : ℕ) : ℝ) := by push_cast; ring
  rw [e]
  have := ConstructionN.circDist_int_div (n := 8) (by norm_num) (c := (d : ℤ)) (by exact_mod_cast h d hd)
  simpa using this

theorem lonely8_two_adic_window (S : Finset ℕ) (e : ℕ)
    (h1 : ∀ d ∈ S, (2 : ℕ) ^ e ∣ d) (h2 : ∀ d ∈ S, ¬ (2 : ℕ) ^ (e + 3) ∣ d) : Lonely8 S := by
  refine ⟨1 / 2 ^ (e + 3), by positivity, fun d hd => ?_⟩
  have := clear_two_adic e (d := (d : ℤ)) (k := 1) (by decide) (by exact_mod_cast h1 d hd)
    (by exact_mod_cast h2 d hd)
  simpa using this

end LRC.IntegerGrid
