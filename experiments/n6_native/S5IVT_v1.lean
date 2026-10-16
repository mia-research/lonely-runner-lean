import LonelyRunner.LRC.Spec.OrderSixSixRestN

/-!
# The intermediate-value box lemma (n6_native, E113)

Runners 2–5 with `v_k = v₂ + d_k v₁` (`d_k ≥ 0`) read `y + d_k P` at every instant, where `y` is runner 2's reading and
`P = v₁t` runner 1's. If on an interval `[pa, pb]` of `P` of length at least `v₁/v₂`, inside one band of runner 1, with fixed
laps the lower envelope `ℓ(P) = max(1/6, m_k + 1/6 − d_k P)` lies below the upper envelope `u(P) = min(5/6, m_k + 5/6 − d_k P)`,
then some instant is lonely: `f(t) = v₂t − ℓ(v₁t)` rises by at least 1 over one lap of runner 2 (`ℓ` is antitone), so it
takes an integer value `n`; there runner 2 reads `n + ℓ` and runner `k` reads `n + ℓ + d_k P`.
-/

namespace LRC.S6Native
open LRC.S7Native LRC.S8Native

/-- Lower and upper envelopes of the band constraints of runners 2..5 in runner 2's reading. -/
noncomputable def envL (d3 d4 d5 : ℝ) (m3 m4 m5 : ℤ) (P : ℝ) : ℝ :=
  max (1 / 6) (max ((m3 : ℝ) + 1 / 6 - d3 * P) (max ((m4 : ℝ) + 1 / 6 - d4 * P) ((m5 : ℝ) + 1 / 6 - d5 * P)))

noncomputable def envU (d3 d4 d5 : ℝ) (m3 m4 m5 : ℤ) (P : ℝ) : ℝ :=
  min (5 / 6) (min ((m3 : ℝ) + 5 / 6 - d3 * P) (min ((m4 : ℝ) + 5 / 6 - d4 * P) ((m5 : ℝ) + 5 / 6 - d5 * P)))

theorem envL_anti {d3 d4 d5 : ℝ} (h3 : 0 ≤ d3) (h4 : 0 ≤ d4) (h5 : 0 ≤ d5) (m3 m4 m5 : ℤ) {P Q : ℝ} (hPQ : P ≤ Q) :
    envL d3 d4 d5 m3 m4 m5 Q ≤ envL d3 d4 d5 m3 m4 m5 P := by
  unfold envL
  have a := mul_le_mul_of_nonneg_left hPQ h3
  have b := mul_le_mul_of_nonneg_left hPQ h4
  have c := mul_le_mul_of_nonneg_left hPQ h5
  apply max_le_max le_rfl (max_le_max (by linarith) (max_le_max (by linarith) (by linarith)))

theorem envL_cont (d3 d4 d5 : ℝ) (m3 m4 m5 : ℤ) : Continuous (envL d3 d4 d5 m3 m4 m5) := by
  unfold envL; fun_prop

set_option maxHeartbeats 1000000 in
/-- **The intermediate-value box lemma.** -/
theorem ivt_box {v1 v2 v3 v4 v5 d3 d4 d5 pa pb : ℝ} {n1 m3 m4 m5 : ℤ} (h1 : 0 < v1) (h2 : 0 < v2)
    (hd3 : 0 ≤ d3) (hd4 : 0 ≤ d4) (hd5 : 0 ≤ d5)
    (hv3 : v3 = v2 + d3 * v1) (hv4 : v4 = v2 + d4 * v1) (hv5 : v5 = v2 + d5 * v1)
    (hlen : v1 / v2 ≤ pb - pa)
    (hP1 : ∀ P, pa ≤ P → P ≤ pb → (n1 : ℝ) + 1 / 6 ≤ P ∧ P ≤ (n1 : ℝ) + 5 / 6)
    (hLU : ∀ P, pa ≤ P → P ≤ pb → envL d3 d4 d5 m3 m4 m5 P ≤ envU d3 d4 d5 m3 m4 m5 P) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  set L := envL d3 d4 d5 m3 m4 m5 with hLdef
  set f : ℝ → ℝ := fun t => v2 * t - L (v1 * t) with hf
  have hfc : Continuous f := by
    rw [hf]; exact (continuous_const.mul continuous_id).sub ((envL_cont d3 d4 d5 m3 m4 m5).comp (continuous_const.mul continuous_id))
  set t0 := pa / v1 with ht0
  set t1 := t0 + 1 / v2 with ht1
  have hv2i : 0 < 1 / v2 := by positivity
  have hα : 0 < v1 / v2 := by positivity
  have ht01 : t0 ≤ t1 := by rw [ht1]; linarith
  have hP0 : v1 * t0 = pa := by rw [ht0]; field_simp
  have hP1' : v1 * t1 = pa + v1 / v2 := by rw [ht1, mul_add, hP0]; field_simp
  have hrise : f t0 + 1 ≤ f t1 := by
    simp only [hf]
    rw [hP0, hP1']
    have hanti := envL_anti hd3 hd4 hd5 m3 m4 m5 (show pa ≤ pa + v1 / v2 by linarith)

    have : v2 * t1 = v2 * t0 + 1 := by rw [ht1, mul_add]; field_simp
    linarith
  set n : ℤ := ⌈f t0⌉ with hn
  have hn1 : f t0 ≤ n := Int.le_ceil _
  have hn2 : (n : ℝ) ≤ f t1 := by have := Int.ceil_lt_add_one (f t0); linarith
  obtain ⟨t, ⟨htl, htr⟩, hft⟩ := intermediate_value_Icc ht01 hfc.continuousOn ⟨hn1, hn2⟩
  set P := v1 * t with hP
  have hPa : pa ≤ P := by rw [hP, ← hP0]; exact mul_le_mul_of_nonneg_left htl h1.le
  have hPb : P ≤ pb := by
    have : P ≤ pa + v1 / v2 := by rw [hP, ← hP1']; exact mul_le_mul_of_nonneg_left htr h1.le
    linarith
  have hy : v2 * t = n + L P := by simp only [hf] at hft; linarith
  have hLU' := hLU P hPa hPb
  obtain ⟨hb1, hb2⟩ := hP1 P hPa hPb

  -- envelope facts
  have l1 : (1 / 6 : ℝ) ≤ L P := by rw [hLdef]; unfold envL; exact le_max_left _ _
  have l3 : (m3 : ℝ) + 1 / 6 - d3 * P ≤ L P := by
    rw [hLdef]; unfold envL; exact le_max_of_le_right (le_max_left _ _)
  have l4 : (m4 : ℝ) + 1 / 6 - d4 * P ≤ L P := by
    rw [hLdef]; unfold envL; exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have l5 : (m5 : ℝ) + 1 / 6 - d5 * P ≤ L P := by
    rw [hLdef]; unfold envL; exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  have u1 : envU d3 d4 d5 m3 m4 m5 P ≤ 5 / 6 := by unfold envU; exact min_le_left _ _
  have u3 : envU d3 d4 d5 m3 m4 m5 P ≤ (m3 : ℝ) + 5 / 6 - d3 * P := by
    unfold envU; exact min_le_of_right_le (min_le_left _ _)
  have u4 : envU d3 d4 d5 m3 m4 m5 P ≤ (m4 : ℝ) + 5 / 6 - d4 * P := by
    unfold envU; exact min_le_of_right_le (min_le_of_right_le (min_le_left _ _))
  have u5 : envU d3 d4 d5 m3 m4 m5 P ≤ (m5 : ℝ) + 5 / 6 - d5 * P := by
    unfold envU; exact min_le_of_right_le (min_le_of_right_le (min_le_right _ _))
  refine ⟨t, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hP]; exact clear_of_band (p := n1) hb1 hb2
  · rw [hy]; apply clear_of_band (p := n) <;> linarith
  · have : v3 * t = (n + m3 : ℤ) + (L P + d3 * P - m3) := by
      rw [hv3, add_mul, hy, mul_assoc, ← hP]; push_cast; ring
    rw [this]; apply clear_of_band (p := n + m3) <;> push_cast <;> linarith
  · have : v4 * t = (n + m4 : ℤ) + (L P + d4 * P - m4) := by
      rw [hv4, add_mul, hy, mul_assoc, ← hP]; push_cast; ring
    rw [this]; apply clear_of_band (p := n + m4) <;> push_cast <;> linarith
  · have : v5 * t = (n + m5 : ℤ) + (L P + d5 * P - m5) := by
      rw [hv5, add_mul, hy, mul_assoc, ← hP]; push_cast; ring
    rw [this]; apply clear_of_band (p := n + m5) <;> push_cast <;> linarith

end LRC.S6Native

#print axioms LRC.S6Native.ivt_box
