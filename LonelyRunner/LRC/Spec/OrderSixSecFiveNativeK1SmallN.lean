import LonelyRunner.LRC.Spec.OrderSixSecFiveNativeK2N

-- Moved into the tree 2026-10-17 from `experiments/n6_native/S5K1Small_v1.lean` (log E113–E114); the shared pair-window
-- lemmas come from `OrderSixSecFiveNativeK2N`.

/-!
# §5, k = 1 (`v₃ = v₂ + v₁`), `α = v₁/v₂ ≤ 1/50` (n6_native, E114)

Shared lemmas from `S5Cert_v1.lean` (pair windows, `s5_fold_x`, `exists_p`, `exists_j0`, `s5_uniform_j0`,
`step_meets_arc`) and `S5IVT_v1.lean` (`ivt_box`), then:
* `k1_leafP`: the pair-window fold at the lap with runner 1 at `p`, runner 5 folded with `v₄/(3v₅) ≤ μ₀`;
* the uniform window at `j₀` when `12(v₄ − v₂) ≥ 5v₂`;
* runner-4 leaves (`μ₀ = 1/3`) for `λ = (v₄ − v₂)/v₁ ≤ 25/14`, `[16/5, 8]`, `[20, 45/2]`, and the step lemma for
  `λ ∈ [8, 20]` and `λ ≥ 45/2`;
* the strip `λ ∈ [25/14, 16/5]`: runner-5 fold leaves (`μ₀ = 266/1250`) when `3v₅ ≥ 5v₂`; else an `ivt_box` tree over
  `(λ, λ₅)`, `λ₅ = (v₅ − v₂)/v₁ ≤ 30`; else runner 5 swept into a 4-runner interval.
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


/-! ### k = 1 leaves -/

set_option maxHeartbeats 1000000 in
/-- **The k = 1 pair-window fold at `p`.** `p = v₁(j + 1/6)/v₂`, `L = (v₄ − v₂)/v₁`; with `v₄/(3v₅) ≤ μ₀ ≤ 2/3 − p`,
`1/6 ≤ p ≤ 2/3`, and `L p ∈ [m − (2/3 − p) + μ₀, m + 2/3 − μ₀]`, lonely. -/
theorem k1_leafP {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (hv3 : v3 = v2 + v1) (h34 : v3 < v4)
    (h45 : v4 < v5) (hα : 50 * v1 ≤ v2) (j : ℕ) (m : ℤ) (μ0 : ℝ) (hμ : (v4 : ℝ) / (3 * v5) ≤ μ0)
    (hp1 : 1 / 6 ≤ (v1 : ℝ) * ((j : ℝ) + 1 / 6) / v2) (hp2 : (v1 : ℝ) * ((j : ℝ) + 1 / 6) / v2 ≤ 2 / 3 - μ0)
    (hp3 : (v1 : ℝ) * ((j : ℝ) + 1 / 6) / v2 ≤ 2 / 3)
    (hlo : (m : ℝ) - (2 / 3 - (v1 : ℝ) * ((j : ℝ) + 1 / 6) / v2) + μ0 ≤
      ((v4 : ℝ) - v2) / v1 * ((v1 : ℝ) * ((j : ℝ) + 1 / 6) / v2))
    (hhi : ((v4 : ℝ) - v2) / v1 * ((v1 : ℝ) * ((j : ℝ) + 1 / 6) / v2) ≤ m + 2 / 3 - μ0) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have h1R : (0 : ℝ) < v1 := by exact_mod_cast h0
  have h2R : (0 : ℝ) < v2 := by exact_mod_cast (show 0 < v2 by omega)
  have hv3R : (v3 : ℝ) = v2 + v1 := by rw [hv3]; push_cast; ring
  have h3R : (0 : ℝ) < v3 := by rw [hv3R]; linarith
  have h23R : (v2 : ℝ) ≤ v3 := by rw [hv3R]; linarith
  have h34R : (v3 : ℝ) ≤ v4 := by exact_mod_cast h34.le
  have h45R : (v4 : ℝ) ≤ v5 := by exact_mod_cast h45.le
  have h4R : (0 : ℝ) < v4 := by linarith
  have hαR : 50 * (v1 : ℝ) ≤ v2 := by exact_mod_cast hα
  set u : ℝ := (j : ℝ) + 1 / 6 with hu
  have hu0 : 0 < u := by positivity
  set p : ℝ := (v1 : ℝ) * u / v2 with hp
  set L : ℝ := ((v4 : ℝ) - v2) / v1 with hL
  set μ : ℝ := (v4 : ℝ) / (3 * v5) with hμd
  have e3 : (v3 : ℝ) * ((u + 2 / 3) / v3 - u / v2) = 2 / 3 - p := by rw [hp, hv3R]; field_simp; ring
  have hsw : 0 ≤ (u + 2 / 3) / v3 - u / v2 := by
    have : 0 < (v3 : ℝ) * ((u + 2 / 3) / v3 - u / v2) := by
      rw [e3]; have : (0 : ℝ) < μ := by rw [hμd]; exact div_pos h4R (by linarith)
      linarith
    exact (pos_of_mul_pos_right this h3R.le).le
  have hw4 : 2 / 3 - p ≤ (v4 : ℝ) * ((u + 2 / 3) / v3 - u / v2) := by
    have : (v3 : ℝ) * ((u + 2 / 3) / v3 - u / v2) ≤ v4 * ((u + 2 / 3) / v3 - u / v2) :=
      mul_le_mul_of_nonneg_right h34R hsw
    linarith
  have ex : (v4 : ℝ) * (u / v2) = u + L * p := by rw [hL, hp]; field_simp; ring
  have hj56 : (j : ℝ) + 5 / 6 = u + 2 / 3 := by rw [hu]; ring
  refine s5_fold_x (j := (j : ℤ)) (n1 := 0) (M := (j : ℤ) + m) (by positivity) h1R h2R h23R h4R h45R ?_ ?_ ?_ ?_ ?_
  · push_cast; rw [← hu, mul_div_assoc']; linarith
  · push_cast; rw [hj56]
    have a : (v1 : ℝ) * ((u + 2 / 3) / v3) ≤ v1 * ((u + 2 / 3) / v2) := by
      apply mul_le_mul_of_nonneg_left _ h1R.le
      exact div_le_div_of_nonneg_left (by positivity) h2R h23R
    have b : (v1 : ℝ) * ((u + 2 / 3) / v2) = p + 2 / 3 * (v1 / v2) := by rw [hp]; field_simp
    have c : (v1 : ℝ) / v2 ≤ 1 / 50 := by rw [div_le_iff₀ h2R]; linarith
    linarith
  · push_cast; rw [← hu, hj56]; linarith
  · push_cast; rw [← hu, hj56, ex]; linarith
  · push_cast; rw [← hu, ex]; linarith

/-- **Uniform window at `j₀`**, k = 1, `α ≤ 1/50`, `12(v₄ − v₂) ≥ 5v₂`. -/
theorem k1_uniform {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (hv3 : v3 = v2 + v1) (h34 : v3 < v4)
    (h45 : v4 < v5) (hsmall : 3 * v1 < v3) (hα : 50 * v1 ≤ v2) (hU : 17 * v2 ≤ 12 * v4) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  obtain ⟨j0, hj0a, hj0b⟩ := exists_j0 (v2 := v2) h0
  refine s5_uniform_j0 h0 h12 (by omega) h34 h45.le hsmall hj0a hj0b ?_
  have h1R : (0 : ℝ) < v1 := by exact_mod_cast h0
  have h2R : (0 : ℝ) < v2 := by exact_mod_cast (show 0 < v2 by omega)
  have hv3R : (v3 : ℝ) = v2 + v1 := by rw [hv3]; push_cast; ring
  have h3R : (0 : ℝ) < v3 := by rw [hv3R]; linarith
  have hUR : 17 * (v2 : ℝ) ≤ 12 * v4 := by exact_mod_cast hU
  have hαR : 50 * (v1 : ℝ) ≤ v2 := by exact_mod_cast hα
  have h4R : (0 : ℝ) < v4 := by linarith
  have hb : (v1 : ℝ) * (6 * j0 + 1) < v2 + 6 * v1 := by exact_mod_cast hj0b
  set u0 : ℝ := (j0 : ℝ) + 1 / 6 with hu0
  have hj56 : (j0 : ℝ) + 5 / 6 = u0 + 2 / 3 := by rw [hu0]; ring
  rw [hj56]
  have e3 : (v3 : ℝ) * ((u0 + 2 / 3) / v3 - u0 / v2) = 2 / 3 - v1 * u0 / v2 := by rw [hv3R]; field_simp; ring
  have hp0 : (v1 : ℝ) * u0 / v2 < 1 / 6 + v1 / v2 := by
    rw [hu0, div_lt_iff₀ h2R]; field_simp; nlinarith
  have hR : (2 / 3 - (1 / 6 + (v1 : ℝ) / v2)) / v3 ≤ (u0 + 2 / 3) / v3 - u0 / v2 := by
    rw [div_le_iff₀ h3R]; nlinarith
  refine le_trans ?_ hR
  rw [div_le_div_iff₀ (by positivity) h3R]
  set r : ℝ := (v1 : ℝ) / v2 with hr
  have hr1 : r ≤ 1 / 50 := by rw [hr, div_le_iff₀ h2R]; linarith
  have hr0 : 0 ≤ r := by positivity
  have hv1 : (v1 : ℝ) = r * v2 := by rw [hr]; field_simp
  rw [hv3R, hv1]
  have hA : (0 : ℝ) ≤ 1 / 2 - r := by linarith
  have := mul_le_mul_of_nonneg_left hUR hA
  nlinarith [mul_nonneg hr0 h2R.le]

set_option maxHeartbeats 1000000 in
/-- **A k = 1 leaf on an interval of `p`**: `L = (v₄ − v₂)/v₁ ∈ [l₀, l₁]`, `p ∈ [pa, pb]` of length `≥ 1/50 ≥ α`,
`m − 2/3 + μ₀ ≤ (l₀ − 1) pa`, `l₁ pb ≤ m + 2/3 − μ₀`, `pb ≤ 2/3 − μ₀`. -/
theorem k1_leafI {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (hv3 : v3 = v2 + v1) (h34 : v3 < v4)
    (h45 : v4 < v5) (hα : 50 * v1 ≤ v2) (μ0 : ℝ) (hμ : (v4 : ℝ) / (3 * v5) ≤ μ0) (m : ℤ) (pa pb l0 l1 : ℝ)
    (hpa : 1 / 6 ≤ pa) (hpb : pb ≤ 2 / 3 - μ0) (hlen : 1 / 50 ≤ pb - pa) (hl0 : 1 ≤ l0)
    (hL0 : l0 ≤ ((v4 : ℝ) - v2) / v1) (hL1 : ((v4 : ℝ) - v2) / v1 ≤ l1)
    (hA : (m : ℝ) - 2 / 3 + μ0 ≤ (l0 - 1) * pa) (hB : l1 * pb ≤ m + 2 / 3 - μ0) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have h1R : (0 : ℝ) < v1 := by exact_mod_cast h0
  have h2R : (0 : ℝ) < v2 := by exact_mod_cast (show 0 < v2 by omega)
  have hαR : 50 * (v1 : ℝ) ≤ v2 := by exact_mod_cast hα
  have hα' : (v1 : ℝ) / v2 ≤ 1 / 50 := by rw [div_le_iff₀ h2R]; linarith
  have hαp : (0 : ℝ) < (v1 : ℝ) / v2 := by positivity
  have hμ0 : 0 ≤ μ0 := le_trans (by positivity) hμ
  obtain ⟨j, hj1, hj2⟩ := exists_p hαp (pa := pa) (pb := pb) (by linarith) (by linarith)
  have e : (v1 : ℝ) / v2 * ((j : ℝ) + 1 / 6) = (v1 : ℝ) * ((j : ℝ) + 1 / 6) / v2 := by ring
  rw [e] at hj1 hj2
  set p := (v1 : ℝ) * ((j : ℝ) + 1 / 6) / v2 with hp
  set L := ((v4 : ℝ) - v2) / v1 with hL
  refine k1_leafP h0 h12 hv3 h34 h45 hα j m μ0 hμ (by linarith) (by linarith) (by linarith) ?_ ?_
  · have := mul_le_mul (show l0 - 1 ≤ L - 1 by linarith) hj1 (by linarith) (by linarith)
    nlinarith
  · have := mul_le_mul hL1 hj2 (by linarith) (by linarith)
    linarith

set_option maxHeartbeats 2000000 in
/-- **The runner-4 step lemma, k = 1**: `L ≥ 8` and (`L ≤ 20`, or `L ≥ 45/2` with `12(v₄ − v₂) < 5v₂`). From the lap
`j₀`, runner 4's offset `L p = β u` (`β = (v₄ − v₂)/v₂`) steps by `β` per lap and lands in `[M + 1/3 − β, M + 1/3]`
while `p ≤ min(1/3, 2/3 − β)`. -/
theorem k1_step {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (hv3 : v3 = v2 + v1) (h34 : v3 < v4)
    (h45 : v4 < v5) (hα : 50 * v1 ≤ v2) (hL8 : 8 * v1 ≤ v4 - v2)
    (hcase : v4 - v2 ≤ 20 * v1 ∨ (45 * v1 ≤ 2 * (v4 - v2) ∧ 12 * (v4 - v2) < 5 * v2)) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have h1R : (0 : ℝ) < v1 := by exact_mod_cast h0
  have h2R : (0 : ℝ) < v2 := by exact_mod_cast (show 0 < v2 by omega)
  have hαR : 50 * (v1 : ℝ) ≤ v2 := by exact_mod_cast hα
  have h42 : v2 ≤ v4 := by omega
  have hdR : ((v4 - v2 : ℕ) : ℝ) = (v4 : ℝ) - v2 := by push_cast [Nat.cast_sub h42]; ring
  have hL8R : 8 * (v1 : ℝ) ≤ (v4 : ℝ) - v2 := by rw [← hdR]; exact_mod_cast hL8
  obtain ⟨j0, hj0a, hj0b⟩ := exists_j0 (v2 := v2) h0
  set β : ℝ := ((v4 : ℝ) - v2) / v2 with hβ
  set L : ℝ := ((v4 : ℝ) - v2) / v1 with hL
  have hβ0 : 0 < β := by rw [hβ]; apply div_pos _ h2R; linarith
  have hLβ : L * ((v1 : ℝ) / v2) = β := by rw [hL, hβ]; field_simp
  have hL8' : 8 ≤ L := by rw [hL, le_div_iff₀ h1R]; linarith
  set u0 : ℝ := (j0 : ℝ) + 1 / 6 with hu0
  have hp0a : 1 / 6 ≤ (v1 : ℝ) / v2 * u0 := by
    rw [hu0]; have : (v2 : ℝ) ≤ v1 * (6 * j0 + 1) := by exact_mod_cast hj0a
    rw [div_mul_eq_mul_div, le_div_iff₀ h2R]; linarith
  have hp0b : (v1 : ℝ) / v2 * u0 < 1 / 6 + 1 / 50 := by
    rw [hu0]; have : (v1 : ℝ) * (6 * j0 + 1) < v2 + 6 * v1 := by exact_mod_cast hj0b
    rw [div_mul_eq_mul_div, div_lt_iff₀ h2R]; nlinarith
  obtain ⟨n, M, hM1, hM2, hn⟩ := step_meets_arc (β * u0 - (1 / 3 - β)) hβ0
  -- p at the lap j0 + n, and the bounds on it
  have hnα : (n : ℝ) * ((v1 : ℝ) / v2) = (n * β) / L := by
    rw [← hLβ]; have : 0 < L := by linarith
    field_simp
  have hp_le : (v1 : ℝ) / v2 * (u0 + n) < 1 / 6 + 1 / 50 + (1 + β) / L := by
    have hL0 : 0 < L := by linarith
    have : (n * β) / L ≤ (1 + β) / L := div_le_div_of_nonneg_right (by linarith) hL0.le
    nlinarith
  have hbounds : (1 / 6 + 1 / 50 + (1 + β) / L ≤ 1 / 3) ∧ (1 / 6 + 1 / 50 + (1 + β) / L ≤ 2 / 3 - β) := by
    have hL0 : 0 < L := by linarith
    rcases hcase with hc | ⟨hc1, hc2⟩
    · have hc' : (v4 : ℝ) - v2 ≤ 20 * v1 := by rw [← hdR]; exact_mod_cast hc
      have hL20 : L ≤ 20 := by rw [hL, div_le_iff₀ h1R]; linarith
      have hβL : β ≤ L / 50 := by
        rw [← hLβ]; have : (v1 : ℝ) / v2 ≤ 1 / 50 := by rw [div_le_iff₀ h2R]; linarith
        nlinarith
      constructor
      · 
        have : (1 + β) / L ≤ (1 + L / 50) / L := div_le_div_of_nonneg_right (by linarith) hL0.le
        have : (1 + L / 50) / L ≤ 1 / 8 + 1 / 50 := by
          rw [div_le_iff₀ hL0]; nlinarith
        linarith
      · have : (1 + β) / L ≤ (1 + L / 50) / L := div_le_div_of_nonneg_right (by linarith) hL0.le
        have h2 : (1 + L / 50) / L + L / 50 ≤ 2 / 3 - 1 / 6 - 1 / 50 := by
          rw [div_add' _ _ _ hL0.ne', div_le_iff₀ hL0]; nlinarith
        linarith
    · have hc1' : 45 * (v1 : ℝ) ≤ 2 * ((v4 : ℝ) - v2) := by rw [← hdR]; exact_mod_cast hc1
      have hc2' : 12 * ((v4 : ℝ) - v2) < 5 * v2 := by rw [← hdR]; exact_mod_cast hc2
      have hL45 : 45 / 2 ≤ L := by rw [hL, le_div_iff₀ h1R]; linarith
      have hβ5 : β < 5 / 12 := by rw [hβ, div_lt_iff₀ h2R]; linarith
      have : (1 + β) / L ≤ (17 / 12) / (45 / 2) := by
        rw [div_le_div_iff₀ hL0 (by norm_num)]; nlinarith
      constructor <;> norm_num at this ⊢ <;> linarith
  obtain ⟨hb1, hb2⟩ := hbounds
  refine k1_leafP h0 h12 hv3 h34 h45 hα (j0 + n) M (1 / 3) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [div_le_iff₀ (by have : (0 : ℝ) < v5 := by exact_mod_cast (show 0 < v5 by omega)
                        positivity)]
    have : (v4 : ℝ) ≤ v5 := by exact_mod_cast h45.le
    linarith
  all_goals (push_cast; rw [show (v1 : ℝ) * ((j0 : ℝ) + n + 1 / 6) / v2 = (v1 : ℝ) / v2 * (u0 + n) by rw [hu0]; ring])
  · have : 0 ≤ (v1 : ℝ) / v2 * n := by positivity
    nlinarith
  · linarith
  · linarith
  · rw [show ((v4 : ℝ) - v2) / v1 * ((v1 : ℝ) / v2 * (u0 + n)) = β * (u0 + n) by rw [← hLβ]; ring]
    nlinarith
  · rw [show ((v4 : ℝ) - v2) / v1 * ((v1 : ℝ) / v2 * (u0 + n)) = β * (u0 + n) by rw [← hLβ]; ring]
    nlinarith


/-! ### The strip: envelopes, term-wise bounds, the `(λ, λ₅)` tree, the runner-5 sweep -/

/-- Lower bound of `a·X·P` for `X ∈ [x0, x1]`, `P ∈ [pa, pb]`, all nonnegative. -/
def tlo (a : ℤ) (x0 x1 pa pb : ℚ) : ℚ := if 0 ≤ a then a * x0 * pa else a * x1 * pb

theorem tlo_sound {a : ℤ} {x0 x1 pa pb : ℚ} {X P : ℝ} (hx0 : 0 ≤ (x0 : ℝ)) (hpa : 0 ≤ (pa : ℝ))
    (hX0 : (x0 : ℝ) ≤ X) (hX1 : X ≤ x1) (hP0 : (pa : ℝ) ≤ P) (hP1 : P ≤ pb) :
    ((tlo a x0 x1 pa pb : ℚ) : ℝ) ≤ a * X * P := by
  unfold tlo
  split_ifs with ha
  · have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
    push_cast
    have : (x0 : ℝ) * pa ≤ X * P := mul_le_mul hX0 hP0 hpa (le_trans hx0 hX0)
    nlinarith
  · have ha' : (a : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge ha)
    push_cast
    have : X * P ≤ (x1 : ℝ) * pb := mul_le_mul hX1 hP1 (le_trans hpa hP0) (le_trans (le_trans hx0 hX0) hX1)
    nlinarith

/-- One pairwise condition `0 ≤ c + aP + bλP + eλ₅P`, checked term-wise. -/
def pairOK (c : ℚ) (a b e : ℤ) (l0 l1 k0 k1 pa pb : ℚ) : Bool :=
  decide (0 ≤ c + tlo a 1 1 pa pb + tlo b l0 l1 pa pb + tlo e k0 k1 pa pb)

theorem pairOK_sound {c : ℚ} {a b e : ℤ} {l0 l1 k0 k1 pa pb : ℚ} (h : pairOK c a b e l0 l1 k0 k1 pa pb = true)
    {lv kv P : ℝ} (hl0 : 0 ≤ (l0 : ℝ)) (hk0 : 0 ≤ (k0 : ℝ)) (hpa : 0 ≤ (pa : ℝ))
    (h1 : (l0 : ℝ) ≤ lv) (h2 : lv ≤ l1) (h3 : (k0 : ℝ) ≤ kv) (h4 : kv ≤ k1) (hP0 : (pa : ℝ) ≤ P) (hP1 : P ≤ pb) :
    0 ≤ (c : ℝ) + a * P + b * lv * P + e * kv * P := by
  unfold pairOK at h
  rw [decide_eq_true_eq] at h
  have h' : ((0 : ℚ) : ℝ) ≤ ((c + tlo a 1 1 pa pb + tlo b l0 l1 pa pb + tlo e k0 k1 pa pb : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  have t1 := tlo_sound (a := a) (x0 := 1) (x1 := 1) (X := 1) (P := P) (by norm_num) hpa (by norm_num) (by norm_num) hP0 hP1
  have t2 := tlo_sound (a := b) (X := lv) (P := P) hl0 hpa h1 h2 hP0 hP1
  have t3 := tlo_sound (a := e) (X := kv) (P := P) hk0 hpa h3 h4 hP0 hP1
  push_cast at t1
  linarith

/-- The leaf check of the `(λ, λ₅)` tree: runner 1 in band `n1`, interval length `≥ 1/50`, all 16 pairs. -/
def sLeafOK (l0 l1 k0 k1 : ℚ) (n1 m3 m4 m5 : ℤ) (pa pb : ℚ) : Bool :=
  decide (0 ≤ l0) && decide (0 ≤ k0) && decide (0 ≤ pa) && decide ((n1 : ℚ) + 1 / 6 ≤ pa) &&
    decide (pb ≤ (n1 : ℚ) + 5 / 6) && decide (1 / 50 ≤ pb - pa) &&
    -- uppers: 5/6 | m3+5/6 - P | m4+5/6 - λP | m5+5/6 - λ5P ; lowers: 1/6 | m3+1/6 - P | m4+1/6 - λP | m5+1/6 - λ5P
    pairOK (5 / 6 - 1 / 6) 0 0 0 l0 l1 k0 k1 pa pb && pairOK (5 / 6 - (m3 + 1 / 6)) 1 0 0 l0 l1 k0 k1 pa pb &&
    pairOK (5 / 6 - (m4 + 1 / 6)) 0 1 0 l0 l1 k0 k1 pa pb && pairOK (5 / 6 - (m5 + 1 / 6)) 0 0 1 l0 l1 k0 k1 pa pb &&
    pairOK (m3 + 5 / 6 - 1 / 6) (-1) 0 0 l0 l1 k0 k1 pa pb && pairOK (m3 + 5 / 6 - (m3 + 1 / 6)) 0 0 0 l0 l1 k0 k1 pa pb &&
    pairOK (m3 + 5 / 6 - (m4 + 1 / 6)) (-1) 1 0 l0 l1 k0 k1 pa pb && pairOK (m3 + 5 / 6 - (m5 + 1 / 6)) (-1) 0 1 l0 l1 k0 k1 pa pb &&
    pairOK (m4 + 5 / 6 - 1 / 6) 0 (-1) 0 l0 l1 k0 k1 pa pb && pairOK (m4 + 5 / 6 - (m3 + 1 / 6)) 1 (-1) 0 l0 l1 k0 k1 pa pb &&
    pairOK (m4 + 5 / 6 - (m4 + 1 / 6)) 0 0 0 l0 l1 k0 k1 pa pb && pairOK (m4 + 5 / 6 - (m5 + 1 / 6)) 0 (-1) 1 l0 l1 k0 k1 pa pb &&
    pairOK (m5 + 5 / 6 - 1 / 6) 0 0 (-1) l0 l1 k0 k1 pa pb && pairOK (m5 + 5 / 6 - (m3 + 1 / 6)) 1 0 (-1) l0 l1 k0 k1 pa pb &&
    pairOK (m5 + 5 / 6 - (m4 + 1 / 6)) 0 1 (-1) l0 l1 k0 k1 pa pb && pairOK (m5 + 5 / 6 - (m5 + 1 / 6)) 0 0 0 l0 l1 k0 k1 pa pb

set_option maxHeartbeats 4000000 in
theorem sLeaf_sound {l0 l1 k0 k1 : ℚ} {n1 m3 m4 m5 : ℤ} {pa pb : ℚ} (h : sLeafOK l0 l1 k0 k1 n1 m3 m4 m5 pa pb = true)
    {lv kv : ℝ} (h1 : (l0 : ℝ) ≤ lv) (h2 : lv ≤ l1) (h3 : (k0 : ℝ) ≤ kv) (h4 : kv ≤ k1) :
    (1 / 50 : ℝ) ≤ (pb : ℝ) - pa ∧
    (∀ P : ℝ, (pa : ℝ) ≤ P → P ≤ pb → (n1 : ℝ) + 1 / 6 ≤ P ∧ P ≤ (n1 : ℝ) + 5 / 6) ∧
    (∀ P : ℝ, (pa : ℝ) ≤ P → P ≤ pb → envL 1 lv kv m3 m4 m5 P ≤ envU 1 lv kv m3 m4 m5 P) := by
  unfold sLeafOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl0, hk0⟩, hpa⟩, hn1⟩, hn2⟩, hlen⟩, q1⟩, q2⟩, q3⟩, q4⟩, q5⟩, q6⟩, q7⟩, q8⟩, q9⟩, q10⟩,
    q11⟩, q12⟩, q13⟩, q14⟩, q15⟩, q16⟩ := h
  have hl0' : (0 : ℝ) ≤ l0 := by exact_mod_cast hl0
  have hk0' : (0 : ℝ) ≤ k0 := by exact_mod_cast hk0
  have hpa' : (0 : ℝ) ≤ pa := by exact_mod_cast hpa
  refine ⟨?_, ?_, ?_⟩
  · have : ((1 / 50 : ℚ) : ℝ) ≤ ((pb - pa : ℚ) : ℝ) := by exact_mod_cast hlen
    push_cast at this; exact this
  · intro P hP0 hP1
    have a : (((n1 : ℚ) + 1 / 6 : ℚ) : ℝ) ≤ (pa : ℝ) := by exact_mod_cast hn1
    have b : (pb : ℝ) ≤ (((n1 : ℚ) + 5 / 6 : ℚ) : ℝ) := by exact_mod_cast hn2
    push_cast at a b; constructor <;> linarith
  · intro P hP0 hP1
    have S := fun {c : ℚ} {a b e : ℤ} (hq : pairOK c a b e l0 l1 k0 k1 pa pb = true) =>
      pairOK_sound hq hl0' hk0' hpa' h1 h2 h3 h4 hP0 hP1
    have r1 := S q1; have r2 := S q2; have r3 := S q3; have r4 := S q4; have r5 := S q5; have r6 := S q6
    have r7 := S q7; have r8 := S q8; have r9 := S q9; have r10 := S q10; have r11 := S q11; have r12 := S q12
    have r13 := S q13; have r14 := S q14; have r15 := S q15; have r16 := S q16
    push_cast at r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16
    unfold envL envU
    simp only [max_le_iff, le_min_iff]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;> nlinarith

inductive T6
  | L (n1 m3 m4 m5 : ℤ) (pa pb : ℚ)
  | E
  | S (d : ℕ) (l r : T6)

def chk6 : T6 → ℚ → ℚ → ℚ → ℚ → Bool
  | .L n1 m3 m4 m5 pa pb, l0, l1, k0, k1 => sLeafOK l0 l1 k0 k1 n1 m3 m4 m5 pa pb
  | .E, l0, _, _, k1 => decide (k1 < l0)
  | .S d l r, l0, l1, k0, k1 =>
    if d = 0 then chk6 l l0 ((l0 + l1) / 2) k0 k1 && chk6 r ((l0 + l1) / 2) l1 k0 k1
    else chk6 l l0 l1 k0 ((k0 + k1) / 2) && chk6 r l0 l1 ((k0 + k1) / 2) k1

theorem chk6_sound (T : T6) : ∀ (l0 l1 k0 k1 : ℚ), chk6 T l0 l1 k0 k1 = true → ∀ {lv kv : ℝ},
    (l0 : ℝ) ≤ lv → lv ≤ l1 → (k0 : ℝ) ≤ kv → kv ≤ k1 → lv < kv →
    ∃ n1 m3 m4 m5 : ℤ, ∃ pa pb : ℚ, (1 / 50 : ℝ) ≤ (pb : ℝ) - pa ∧
      (∀ P : ℝ, (pa : ℝ) ≤ P → P ≤ pb → (n1 : ℝ) + 1 / 6 ≤ P ∧ P ≤ (n1 : ℝ) + 5 / 6) ∧
      (∀ P : ℝ, (pa : ℝ) ≤ P → P ≤ pb → envL 1 lv kv m3 m4 m5 P ≤ envU 1 lv kv m3 m4 m5 P) := by
  induction T with
  | L n1 m3 m4 m5 pa pb =>
    intro l0 l1 k0 k1 h lv kv h1 h2 h3 h4 _
    exact ⟨n1, m3, m4, m5, pa, pb, sLeaf_sound h h1 h2 h3 h4⟩
  | E =>
    intro l0 l1 k0 k1 h lv kv h1 h2 h3 h4 h5
    simp only [chk6, decide_eq_true_eq] at h
    have : (k1 : ℝ) < l0 := by exact_mod_cast h
    linarith
  | S d l r ihl ihr =>
    intro l0 l1 k0 k1 h lv kv h1 h2 h3 h4 h5
    simp only [chk6] at h
    split_ifs at h with hd
    · simp only [Bool.and_eq_true] at h
      rcases le_total lv (((l0 + l1) / 2 : ℚ) : ℝ) with hm | hm
      · exact ihl _ _ _ _ h.1 h1 hm h3 h4 h5
      · exact ihr _ _ _ _ h.2 hm h2 h3 h4 h5
    · simp only [Bool.and_eq_true] at h
      rcases le_total kv (((k0 + k1) / 2 : ℚ) : ℝ) with hm | hm
      · exact ihl _ _ _ _ h.1 h1 h2 h3 hm h5
      · exact ihr _ _ _ _ h.2 h1 h2 hm h4 h5


open T6 in
noncomputable def treeS : T6 :=
  (S 1 (S 1 (S 0 (S 1 (S 0 (S 1 (L 0 0 0 0 (1/6) (14/75)) (L 0 0 0 1 (323/1200) (347/1200))) (S 1 (L 0 0 0 0 (1/6) (14/75)) (S 0 (S 1 (L 0 1 1 2 (113/300) (119/300)) (L 0 0 0 1 (109/600) (121/600))) (S 1 (L 0 0 1 1 (323/1200) (347/1200)) (L 0 0 0 1 (239/1200) (263/1200)))))) (L 0 0 0 1 (1/6) (14/75))) (S 1 (S 0 (S 1 (L 0 0 0 0 (1/6) (14/75)) (S 0 (S 1 (L 0 0 1 1 (287/1200) (311/1200)) (L 0 0 0 1 (133/600) (29/120))) (L 0 0 1 1 (127/600) (139/600)))) (S 1 (L 0 0 0 0 (1/6) (14/75)) (L 0 0 1 1 (23/120) (127/600)))) (S 0 (L 0 0 0 1 (1/6) (14/75)) (S 1 (L 0 0 1 2 (377/1200) (401/1200)) (L 0 0 0 1 (1/6) (14/75)))))) (S 0 (S 1 (S 0 (S 1 (L 0 0 0 2 (31/150) (17/75)) (L 0 0 0 2 (1/6) (14/75))) (S 1 (L 0 0 0 2 (263/1200) (287/1200)) (L 0 0 0 2 (103/600) (23/120)))) (S 0 (S 1 (L 0 0 0 2 (1/6) (14/75)) (L 0 0 0 3 (239/1200) (263/1200))) (S 1 (L 0 0 0 2 (1/6) (14/75)) (L 0 0 0 3 (31/150) (17/75))))) (S 1 (S 0 (S 1 (L 0 0 1 3 (181/600) (193/600)) (L 0 0 0 2 (109/600) (121/600))) (S 1 (L 0 0 1 3 (181/600) (193/600)) (L 0 0 1 3 (37/150) (4/15)))) (S 0 (S 1 (L 0 0 0 2 (1/6) (14/75)) (S 0 (L 0 0 0 3 (251/1200) (11/48)) (S 1 (L 0 0 0 3 (257/1200) (281/1200)) (L 0 0 0 3 (59/300) (13/60))))) (S 1 (L 0 0 0 2 (1/6) (14/75)) (L 0 0 1 4 (77/300) (83/300))))))) (S 1 (S 0 (S 1 (S 0 (S 1 (L 0 0 0 3 (209/1200) (233/1200)) (L 0 0 0 3 (1/6) (14/75))) (S 1 (L 0 0 0 3 (43/240) (239/1200)) (L 0 0 0 3 (1/6) (14/75)))) (S 0 (S 1 (L 0 0 0 4 (59/300) (13/60)) (L 0 0 0 4 (43/240) (239/1200))) (S 1 (S 0 (L 0 0 0 4 (239/1200) (263/1200)) (S 1 (L 0 0 0 4 (121/600) (133/600)) (L 0 0 0 4 (23/120) (127/600)))) (L 0 0 0 4 (109/600) (121/600))))) (S 1 (S 0 (S 1 (L 0 0 0 3 (221/1200) (49/240)) (L 0 0 0 3 (1/6) (14/75))) (S 1 (S 0 (L 0 0 0 3 (14/75) (31/150)) (L 0 0 1 5 (353/1200) (377/1200))) (L 0 0 0 3 (1/6) (14/75)))) (S 0 (S 1 (S 0 (S 1 (L 0 0 0 4 (49/240) (269/1200)) (L 0 0 0 4 (233/1200) (257/1200))) (S 1 (L 0 0 0 4 (31/150) (17/75)) (L 0 0 0 4 (59/300) (13/60)))) (S 0 (S 1 (L 0 0 0 4 (221/1200) (49/240)) (L 0 0 0 4 (53/300) (59/300))) (S 1 (L 0 0 0 4 (14/75) (31/150)) (L 0 0 0 4 (53/300) (59/300))))) (S 1 (S 0 (S 1 (L 0 0 1 5 (71/300) (77/300)) (L 0 0 0 4 (59/300) (13/60))) (S 1 (L 0 0 1 4 (221/1200) (49/240)) (L 0 0 1 4 (53/300) (59/300)))) (S 0 (S 1 (L 0 0 0 4 (227/1200) (251/1200)) (L 0 0 0 4 (43/240) (239/1200))) (S 1 (L 0 0 1 5 (13/60) (71/300)) (L 0 0 0 4 (109/600) (121/600)))))))) (S 0 (S 1 (S 0 (S 1 (L 0 0 0 4 (1/6) (14/75)) (S 0 (S 1 (L 0 0 0 5 (233/1200) (257/1200)) (L 0 0 0 5 (14/75) (31/150))) (S 1 (L 0 0 0 5 (233/1200) (257/1200)) (L 0 0 0 5 (14/75) (31/150))))) (S 1 (L 0 0 0 4 (1/6) (14/75)) (S 0 (S 1 (L 0 0 0 5 (59/300) (13/60)) (L 0 0 0 5 (227/1200) (251/1200))) (S 1 (L 0 0 0 5 (239/1200) (263/1200)) (L 0 0 0 5 (23/120) (127/600)))))) (S 0 (S 1 (S 0 (L 0 0 0 5 (43/240) (239/1200)) (S 1 (L 0 0 0 5 (109/600) (121/600)) (L 0 0 0 5 (209/1200) (233/1200)))) (S 0 (L 0 0 0 5 (1/6) (14/75)) (S 1 (L 0 0 0 5 (203/1200) (227/1200)) (L 0 0 0 5 (1/6) (14/75))))) (S 1 (S 0 (S 1 (L 0 0 0 5 (109/600) (121/600)) (L 0 0 0 5 (53/300) (59/300))) (S 1 (L 0 0 0 5 (221/1200) (49/240)) (L 0 0 0 5 (53/300) (59/300)))) (S 0 (S 1 (L 0 0 0 5 (203/1200) (227/1200)) (L 0 0 0 5 (1/6) (14/75))) (S 1 (L 0 0 0 5 (103/600) (23/120)) (L 0 0 0 5 (1/6) (14/75))))))) (S 1 (S 0 (S 1 (S 0 (S 1 (L 0 0 0 4 (203/1200) (227/1200)) (L 0 0 0 4 (1/6) (14/75))) (S 1 (L 0 0 0 4 (203/1200) (227/1200)) (L 0 0 0 4 (1/6) (14/75)))) (S 0 (S 1 (L 0 0 0 5 (239/1200) (263/1200)) (L 0 0 0 5 (23/120) (127/600))) (S 1 (L 0 0 1 8 (187/600) (199/600)) (L 0 0 1 8 (359/1200) (383/1200))))) (S 1 (S 0 (S 1 (L 0 0 0 4 (103/600) (23/120)) (L 0 0 0 4 (1/6) (14/75))) (S 1 (L 0 0 0 4 (209/1200) (233/1200)) (L 0 0 0 4 (1/6) (14/75)))) (S 0 (S 1 (L 0 0 1 7 (323/1200) (347/1200)) (L 0 0 1 7 (311/1200) (67/240))) (S 1 (L 0 0 1 6 (17/75) (37/150)) (L 0 0 1 7 (311/1200) (67/240)))))) (S 0 (S 1 (S 0 (S 1 (L 0 0 0 5 (14/75) (31/150)) (L 0 0 0 5 (43/240) (239/1200))) (S 1 (L 0 0 0 5 (14/75) (31/150)) (L 0 0 0 5 (43/240) (239/1200)))) (S 0 (S 1 (L 0 0 0 5 (103/600) (23/120)) (L 0 0 0 5 (1/6) (14/75))) (S 1 (L 0 0 0 5 (209/1200) (233/1200)) (S 0 (L 0 0 0 5 (1/6) (14/75)) (S 1 (L 0 0 0 5 (203/1200) (227/1200)) (L 0 0 0 5 (1/6) (14/75))))))) (S 1 (S 0 (S 1 (L 0 0 1 8 (347/1200) (371/1200)) (L 0 0 1 8 (67/240) (359/1200))) (S 1 (L 0 0 1 8 (347/1200) (371/1200)) (L 0 0 1 7 (29/120) (157/600)))) (S 0 (S 1 (L 0 0 1 10 (413/1200) (437/1200)) (S 0 (S 1 (L 0 0 0 5 (203/1200) (227/1200)) (L 0 0 0 5 (1/6) (14/75))) (L 0 0 1 10 (401/1200) (17/48)))) (S 1 (L 0 0 1 9 (371/1200) (79/240)) (L 0 0 1 8 (157/600) (169/600))))))))))


theorem treeS_ok : chk6 treeS (25 / 14) (16 / 5) (25 / 14) 30 = true := by decide +kernel

/-! ### The runner-5 sweep (`λ₅ > 30`, `3v₅ < 5v₂`) -/

noncomputable def envL4 (d4 : ℝ) (m3 m4 : ℤ) (P : ℝ) : ℝ :=
  max (1 / 6) (max ((m3 : ℝ) + 1 / 6 - 1 * P) ((m4 : ℝ) + 1 / 6 - d4 * P))
noncomputable def envU4 (d4 : ℝ) (m3 m4 : ℤ) (P : ℝ) : ℝ :=
  min (5 / 6) (min ((m3 : ℝ) + 5 / 6 - 1 * P) ((m4 : ℝ) + 5 / 6 - d4 * P))

theorem env_comb {d4 d5 P : ℝ} {m3 m4 m5 : ℤ} (h44 : envL4 d4 m3 m4 P ≤ envU4 d4 m3 m4 P)
    (h5a : (m5 : ℝ) + 1 / 6 - d5 * P ≤ envU4 d4 m3 m4 P) (h5b : envL4 d4 m3 m4 P ≤ (m5 : ℝ) + 5 / 6 - d5 * P) :
    envL 1 d4 d5 m3 m4 m5 P ≤ envU 1 d4 d5 m3 m4 m5 P := by
  unfold envL4 envU4 at *
  unfold envL envU
  simp only [max_le_iff, le_min_iff] at *
  obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, ⟨c1, c2, c3⟩⟩ := h44
  obtain ⟨d1, d2, d3⟩ := h5a
  obtain ⟨e1, e2, e3⟩ := h5b
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;> linarith

theorem envU4_lip {d4 : ℝ} (hd : 1 ≤ d4) (m3 m4 : ℤ) {P Q : ℝ} (hPQ : P ≤ Q) :
    envU4 d4 m3 m4 P - d4 * (Q - P) ≤ envU4 d4 m3 m4 Q := by
  unfold envU4
  have hq : 0 ≤ Q - P := by linarith
  have a : min (5 / 6 : ℝ) (min ((m3 : ℝ) + 5 / 6 - 1 * P) ((m4 : ℝ) + 5 / 6 - d4 * P)) ≤ 5 / 6 := min_le_left _ _
  have b : min (5 / 6 : ℝ) (min ((m3 : ℝ) + 5 / 6 - 1 * P) ((m4 : ℝ) + 5 / 6 - d4 * P)) ≤ (m3 : ℝ) + 5 / 6 - 1 * P :=
    min_le_of_right_le (min_le_left _ _)
  have c : min (5 / 6 : ℝ) (min ((m3 : ℝ) + 5 / 6 - 1 * P) ((m4 : ℝ) + 5 / 6 - d4 * P)) ≤ (m4 : ℝ) + 5 / 6 - d4 * P :=
    min_le_of_right_le (min_le_right _ _)
  apply le_min (by nlinarith) (le_min (by nlinarith) (by nlinarith))

theorem envL4_anti {d4 : ℝ} (hd : 0 ≤ d4) (m3 m4 : ℤ) {P Q : ℝ} (hPQ : P ≤ Q) :
    envL4 d4 m3 m4 Q ≤ envL4 d4 m3 m4 P := by
  unfold envL4
  have := mul_le_mul_of_nonneg_left hPQ hd
  exact max_le_max le_rfl (max_le_max (by linarith) (by linarith))

theorem envU4_cont (d4 : ℝ) (m3 m4 : ℤ) : Continuous (envU4 d4 m3 m4) := by unfold envU4; fun_prop

set_option maxHeartbeats 2000000 in
/-- **The runner-5 sweep.** Runners 1–4 fit on `[pa, pb]`; runner 5's offset `d₅P` moves faster than the envelopes
(`d₅ > d₄ ≥ 1`). Some lap `m₅` and a sub-interval of length `2/(3d₅)` admit all five. -/
theorem sweep5 {d4 d5 pa pb : ℝ} {m3 m4 : ℤ} (hd4 : 1 ≤ d4) (hd45 : d4 < d5)
    (h4 : ∀ P, pa ≤ P → P ≤ pb → envL4 d4 m3 m4 P ≤ envU4 d4 m3 m4 P)
    (hlen : 1 / (d5 - d4) + 2 / (3 * d5) ≤ pb - pa) :
    ∃ m5 : ℤ, ∃ q : ℝ, pa ≤ q ∧ q + 2 / (3 * d5) ≤ pb ∧
      ∀ P, q ≤ P → P ≤ q + 2 / (3 * d5) → envL 1 d4 d5 m3 m4 m5 P ≤ envU 1 d4 d5 m3 m4 m5 P := by
  have hd5 : 0 < d5 := by linarith
  have hgap : 0 < d5 - d4 := by linarith
  set h : ℝ → ℝ := fun P => d5 * P + envU4 d4 m3 m4 P with hh
  have hc : Continuous h := by rw [hh]; exact (continuous_const.mul continuous_id).add (envU4_cont d4 m3 m4)
  have hrise : ∀ P Q, P ≤ Q → h P + (d5 - d4) * (Q - P) ≤ h Q := by
    intro P Q hPQ; simp only [hh]; have := envU4_lip hd4 m3 m4 hPQ; nlinarith
  set m5 : ℤ := ⌈h pa - 1 / 6⌉ with hm5
  have hm1 : h pa ≤ (m5 : ℝ) + 1 / 6 := by have := Int.le_ceil (h pa - 1 / 6); linarith
  have hm2 : (m5 : ℝ) + 1 / 6 < h pa + 1 := by have := Int.ceil_lt_add_one (h pa - 1 / 6); linarith
  set Q1 := pa + 1 / (d5 - d4) with hQ1
  have hQ1a : pa ≤ Q1 := by rw [hQ1]; have : 0 < 1 / (d5 - d4) := by positivity
                            linarith
  have hhQ : (m5 : ℝ) + 1 / 6 ≤ h Q1 := by
    have := hrise pa Q1 hQ1a
    have e : (d5 - d4) * (Q1 - pa) = 1 := by rw [hQ1]; field_simp; ring
    linarith
  obtain ⟨q, ⟨hq1, hq2⟩, hqv⟩ := intermediate_value_Icc hQ1a hc.continuousOn ⟨hm1, hhQ⟩
  have hw : 0 < 2 / (3 * d5) := by positivity
  refine ⟨m5, q, hq1, by linarith, fun P hP1 hP2 => ?_⟩
  have hPa : pa ≤ P := by linarith
  have hPb : P ≤ pb := by linarith
  have hqv' : d5 * q + envU4 d4 m3 m4 q = (m5 : ℝ) + 1 / 6 := hqv
  apply env_comb (h4 P hPa hPb)
  · have h' : d5 * q + envU4 d4 m3 m4 q + (d5 - d4) * (P - q) ≤ d5 * P + envU4 d4 m3 m4 P := hrise q P hP1
    have := mul_nonneg hgap.le (show 0 ≤ P - q by linarith); linarith
  · have a := envL4_anti (d4 := d4) (by linarith) m3 m4 hP1
    have b := h4 q (by linarith) (by linarith)
    have : d5 * (P - q) ≤ 2 / 3 := by
      have := mul_le_mul_of_nonneg_left (show P - q ≤ 2 / (3 * d5) by linarith) hd5.le
      rw [show d5 * (2 / (3 * d5)) = 2 / 3 by field_simp] at this; exact this
    linarith

/-- The 4-runner leaf check for the sweep: runner 1 in band, the 9 pairs, and the length bound. -/
def r5LeafOK (l0 l1 : ℚ) (n1 m3 m4 : ℤ) (pa pb : ℚ) : Bool :=
  decide (1 ≤ l0) && decide (0 ≤ pa) && decide ((n1 : ℚ) + 1 / 6 ≤ pa) && decide (pb ≤ (n1 : ℚ) + 5 / 6) &&
    decide (l1 < 30) && decide (1 / (30 - l1) + 2 / 90 ≤ pb - pa) &&
    pairOK (5 / 6 - 1 / 6) 0 0 0 l0 l1 0 0 pa pb && pairOK (5 / 6 - (m3 + 1 / 6)) 1 0 0 l0 l1 0 0 pa pb &&
    pairOK (5 / 6 - (m4 + 1 / 6)) 0 1 0 l0 l1 0 0 pa pb &&
    pairOK (m3 + 5 / 6 - 1 / 6) (-1) 0 0 l0 l1 0 0 pa pb && pairOK (m3 + 5 / 6 - (m3 + 1 / 6)) 0 0 0 l0 l1 0 0 pa pb &&
    pairOK (m3 + 5 / 6 - (m4 + 1 / 6)) (-1) 1 0 l0 l1 0 0 pa pb &&
    pairOK (m4 + 5 / 6 - 1 / 6) 0 (-1) 0 l0 l1 0 0 pa pb && pairOK (m4 + 5 / 6 - (m3 + 1 / 6)) 1 (-1) 0 l0 l1 0 0 pa pb &&
    pairOK (m4 + 5 / 6 - (m4 + 1 / 6)) 0 0 0 l0 l1 0 0 pa pb

set_option maxHeartbeats 4000000 in
theorem r5Leaf_sound {l0 l1 : ℚ} {n1 m3 m4 : ℤ} {pa pb : ℚ} (h : r5LeafOK l0 l1 n1 m3 m4 pa pb = true)
    {lv : ℝ} (h1 : (l0 : ℝ) ≤ lv) (h2 : lv ≤ l1) :
    1 ≤ lv ∧ (1 / (30 - (l1 : ℝ)) + 2 / 90 ≤ (pb : ℝ) - pa) ∧ (l1 : ℝ) < 30 ∧
    (∀ P : ℝ, (pa : ℝ) ≤ P → P ≤ pb → (n1 : ℝ) + 1 / 6 ≤ P ∧ P ≤ (n1 : ℝ) + 5 / 6) ∧
    (∀ P : ℝ, (pa : ℝ) ≤ P → P ≤ pb → envL4 lv m3 m4 P ≤ envU4 lv m3 m4 P) := by
  unfold r5LeafOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl0, hpa⟩, hn1⟩, hn2⟩, hl30⟩, hlen⟩, q1⟩, q2⟩, q3⟩, q4⟩, q5⟩, q6⟩, q7⟩, q8⟩, q9⟩ := h
  have hl0' : (1 : ℝ) ≤ l0 := by exact_mod_cast hl0
  have hpa' : (0 : ℝ) ≤ pa := by exact_mod_cast hpa
  refine ⟨by linarith, ?_, by exact_mod_cast hl30, ?_, ?_⟩
  · have : ((1 / (30 - l1) + 2 / 90 : ℚ) : ℝ) ≤ ((pb - pa : ℚ) : ℝ) := by exact_mod_cast hlen
    push_cast at this; exact this
  · intro P hP0 hP1
    have a : (((n1 : ℚ) + 1 / 6 : ℚ) : ℝ) ≤ (pa : ℝ) := by exact_mod_cast hn1
    have b : (pb : ℝ) ≤ (((n1 : ℚ) + 5 / 6 : ℚ) : ℝ) := by exact_mod_cast hn2
    push_cast at a b; constructor <;> linarith
  · intro P hP0 hP1
    have S := fun {c : ℚ} {a b e : ℤ} (hq : pairOK c a b e l0 l1 0 0 pa pb = true) =>
      pairOK_sound (kv := 0) hq (by linarith) (by norm_num) hpa' h1 h2 (by norm_num) (by norm_num) hP0 hP1
    have r1 := S q1; have r2 := S q2; have r3 := S q3; have r4 := S q4; have r5 := S q5; have r6 := S q6
    have r7 := S q7; have r8 := S q8; have r9 := S q9
    push_cast at r1 r2 r3 r4 r5 r6 r7 r8 r9
    unfold envL4 envU4
    simp only [max_le_iff, le_min_iff]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> nlinarith

theorem r5_ok1 : r5LeafOK (25 / 14) (349 / 140) 0 0 0 (1 / 6) (78067 / 346590) = true := by decide +kernel
theorem r5_ok2 : r5LeafOK (349 / 140) (16 / 5) 0 0 1 (12707 / 48240) (1731 / 5360) = true := by decide +kernel


/-! ### The strip and the small-α theorem -/

set_option maxHeartbeats 4000000 in
/-- **The strip `λ ∈ [25/14, 16/5]`**, k = 1, `α ≤ 1/50`. -/
theorem k1_strip {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (hv3 : v3 = v2 + v1) (h34 : v3 < v4)
    (h45 : v4 < v5) (hα : 50 * v1 ≤ v2) (hLa : 25 / 14 ≤ ((v4 : ℝ) - v2) / v1) (hLb : ((v4 : ℝ) - v2) / v1 ≤ 16 / 5) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have h1R : (0 : ℝ) < v1 := by exact_mod_cast h0
  have h2R : (0 : ℝ) < v2 := by exact_mod_cast (show 0 < v2 by omega)
  have hv3R : (v3 : ℝ) = v2 + v1 := by rw [hv3]; push_cast; ring
  have h34R : (v3 : ℝ) < v4 := by exact_mod_cast h34
  have h45R : (v4 : ℝ) < v5 := by exact_mod_cast h45
  have hαR : 50 * (v1 : ℝ) ≤ v2 := by exact_mod_cast hα
  have h5R : (0 : ℝ) < v5 := by linarith
  set L : ℝ := ((v4 : ℝ) - v2) / v1 with hL
  set L5 : ℝ := ((v5 : ℝ) - v2) / v1 with hL5
  have hLL5 : L < L5 := by rw [hL, hL5]; exact div_lt_div_of_pos_right (by linarith) h1R
  have hv4L : (v4 : ℝ) = v2 + L * v1 := by rw [hL]; field_simp; ring
  have hv5L : (v5 : ℝ) = v2 + L5 * v1 := by rw [hL5]; field_simp; ring
  rcases le_or_gt (5 * (v2 : ℝ)) (3 * v5) with hγ | hγ
  · -- runner 5 at least 5/3 of runner 2: fold leaves with μ₀ = 133/625
    have hμ : (v4 : ℝ) / (3 * v5) ≤ 133 / 625 := by
      rw [div_le_iff₀ (by positivity)]
      have : (v4 : ℝ) ≤ v2 + 16 / 5 * v1 := by rw [hv4L]; nlinarith
      nlinarith
    rcases le_or_gt L (12 / 5) with hL1 | hL1
    · exact k1_leafI h0 h12 hv3 h34 h45 hα (133 / 625) hμ 0 (1 / 6) (14 / 75) (25 / 14) (12 / 5)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) hLa hL1 (by norm_num) (by norm_num)
    · exact k1_leafI h0 h12 hv3 h34 h45 hα (133 / 625) hμ 1 (1024 / 2625) (2153 / 5250) (12 / 5) (16 / 5)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1.le hLb (by norm_num) (by norm_num)
  have hlenα : (v1 : ℝ) / v2 ≤ 1 / 50 := by rw [div_le_iff₀ h2R]; linarith
  rcases le_or_gt L5 30 with h30 | h30
  · -- the (λ, λ₅) tree
    obtain ⟨n1, m3, m4, m5, pa, pb, hlen, hP1, hLU⟩ := chk6_sound treeS _ _ _ _ treeS_ok (lv := L) (kv := L5)
      (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) hLL5
    exact ivt_box (d3 := 1) (d4 := L) (d5 := L5) h1R h2R (by norm_num) (by linarith) (by linarith)
      (by rw [hv3R]; ring) hv4L hv5L (by linarith) hP1 hLU
  · -- runner 5 swept
    have key : ∀ (l0 l1 : ℚ) (n1 m3 m4 : ℤ) (pa pb : ℚ), r5LeafOK l0 l1 n1 m3 m4 pa pb = true →
        (l0 : ℝ) ≤ L → L ≤ l1 →
        ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧
          (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
      intro l0 l1 n1 m3 m4 pa pb hok h1 h2
      obtain ⟨hL1', hlen, hl30, hP1, h4⟩ := r5Leaf_sound hok h1 h2
      have hgap : (30 : ℝ) - l1 ≤ L5 - L := by linarith
      have hlen' : 1 / (L5 - L) + 2 / (3 * L5) ≤ (pb : ℝ) - pa := by
        have a : 1 / (L5 - L) ≤ 1 / (30 - (l1 : ℝ)) := one_div_le_one_div_of_le (by linarith) hgap
        have b : 2 / (3 * L5) ≤ 2 / 90 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
        linarith
      obtain ⟨m5, q, hq1, hq2, hall⟩ := sweep5 hL1' hLL5 h4 hlen'
      have hsub : (v1 : ℝ) / v2 ≤ (q + 2 / (3 * L5)) - q := by
        rw [show (q + 2 / (3 * L5)) - q = 2 / (3 * L5) by ring, div_le_div_iff₀ h2R (by linarith)]
        have : L5 * v1 = (v5 : ℝ) - v2 := by rw [hL5]; field_simp
        nlinarith
      exact ivt_box (d3 := 1) (d4 := L) (d5 := L5) (pa := q) (pb := q + 2 / (3 * L5)) h1R h2R (by norm_num)
        (by linarith) (by linarith) (by rw [hv3R]; ring) hv4L hv5L hsub
        (fun P hP0 hP1' => hP1 P (by linarith) (by linarith)) hall
    rcases le_or_gt L (349 / 140) with hL1 | hL1
    · exact key _ _ _ _ _ _ _ r5_ok1 (by push_cast; linarith) (by push_cast; linarith)
    · exact key _ _ _ _ _ _ _ r5_ok2 (by push_cast; linarith) (by push_cast; linarith)

set_option maxHeartbeats 8000000 in
/-- **§5, `k = 1`, `v₂ ≥ 50 v₁`.** -/
theorem s5k1_small {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (hv3 : v3 = v2 + v1) (h34 : v3 < v4)
    (h45 : v4 < v5) (hsmall : 3 * v1 < v3) (hα : 50 * v1 ≤ v2) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have h1R : (0 : ℝ) < v1 := by exact_mod_cast h0
  have h2R : (0 : ℝ) < v2 := by exact_mod_cast (show 0 < v2 by omega)
  have hv3R : (v3 : ℝ) = v2 + v1 := by rw [hv3]; push_cast; ring
  have h34R : (v3 : ℝ) < v4 := by exact_mod_cast h34
  have h45R : (v4 : ℝ) ≤ v5 := by exact_mod_cast h45.le
  have h5R : (0 : ℝ) < v5 := by linarith
  have hμ3 : (v4 : ℝ) / (3 * v5) ≤ 1 / 3 := by rw [div_le_iff₀ (by positivity)]; linarith
  have h42 : v2 ≤ v4 := by omega
  have hdR : ((v4 - v2 : ℕ) : ℝ) = (v4 : ℝ) - v2 := by push_cast [Nat.cast_sub h42]; ring
  set L : ℝ := ((v4 : ℝ) - v2) / v1 with hL
  have hL1 : 1 ≤ L := by rw [hL, le_div_iff₀ h1R]; linarith
  have leafA := fun (m : ℤ) (pa pb l0 l1 : ℝ) (h1 : 1 / 6 ≤ pa) (h2 : pb ≤ 2 / 3 - 1 / 3) (h3 : 1 / 50 ≤ pb - pa)
      (h4 : 1 ≤ l0) (h5 : l0 ≤ L) (h6 : L ≤ l1) (h7 : (m : ℝ) - 2 / 3 + 1 / 3 ≤ (l0 - 1) * pa)
      (h8 : l1 * pb ≤ m + 2 / 3 - 1 / 3) =>
    k1_leafI h0 h12 hv3 h34 h45 hα (1 / 3) hμ3 m pa pb l0 l1 h1 h2 h3 h4 h5 h6 h7 h8
  have toN : ∀ c : ℕ, (c : ℝ) * v1 ≤ (v4 : ℝ) - v2 → c * v1 ≤ v4 - v2 := fun c h => by
    rw [← hdR] at h; exact_mod_cast h
  have toN' : ∀ c : ℕ, (v4 : ℝ) - v2 ≤ (c : ℝ) * v1 → v4 - v2 ≤ c * v1 := fun c h => by
    rw [← hdR] at h; exact_mod_cast h
  have Lle : ∀ c : ℝ, L ≤ c → (v4 : ℝ) - v2 ≤ c * v1 := fun c h => by rw [hL, div_le_iff₀ h1R] at h; linarith
  have Lge : ∀ c : ℝ, c ≤ L → c * v1 ≤ (v4 : ℝ) - v2 := fun c h => by rw [hL, le_div_iff₀ h1R] at h; linarith
  rcases le_or_gt L (25 / 14) with c1 | c1
  · exact leafA 0 (1 / 6) (14 / 75) 1 (25 / 14) (by norm_num) (by norm_num) (by norm_num) le_rfl hL1 c1
      (by norm_num) (by norm_num)
  rcases le_or_gt L (16 / 5) with c2 | c2
  · exact k1_strip h0 h12 hv3 h34 h45 hα c1.le c2
  rcases le_or_gt L (41 / 10) with c3 | c3
  · exact leafA 1 (10 / 33) (533 / 1650) (16 / 5) (41 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      c2.le c3 (by norm_num) (by norm_num)
  rcases le_or_gt L (113 / 20) with c4 | c4
  · exact leafA 1 (20 / 93) (1093 / 4650) (41 / 10) (113 / 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      c3.le c4 (by norm_num) (by norm_num)
  rcases le_or_gt L (71 / 10) with c5 | c5
  · exact leafA 1 (1 / 6) (14 / 75) (113 / 20) (71 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      c4.le c5 (by norm_num) (by norm_num)
  rcases le_or_gt L (159 / 20) with c6 | c6
  · exact leafA 2 (50 / 183) (2683 / 9150) (71 / 10) (159 / 20) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      c5.le c6 (by norm_num) (by norm_num)
  rcases le_or_gt L 8 with c7 | c7
  · exact leafA 2 (100 / 417) (5417 / 20850) (159 / 20) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      c6.le c7 (by norm_num) (by norm_num)
  rcases le_or_gt L 20 with c8 | c8
  · exact k1_step h0 h12 hv3 h34 h45 hα (toN 8 (by have := Lge 8 c7.le; push_cast; linarith))
      (Or.inl (toN' 20 (by have := Lle 20 c8; push_cast; linarith)))
  have leaves : ∀ (m : ℤ) (pa pb l0 l1 : ℝ), 1 / 6 ≤ pa → pb ≤ 1 / 3 → 1 / 50 ≤ pb - pa → 1 ≤ l0 → l0 ≤ L → L ≤ l1 →
      (m : ℝ) - 1 / 3 ≤ (l0 - 1) * pa → l1 * pb ≤ m + 1 / 3 →
      ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
        (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) :=
    fun m pa pb l0 l1 h1 h2 h3 h4 h5 h6 h7 h8 =>
      leafA m pa pb l0 l1 h1 (by linarith) h3 h4 h5 h6 (by linarith) (by linarith)
  rcases le_or_gt L (203 / 10) with d1 | d1
  · exact leaves 4 (11 / 57) (607 / 2850) 20 (203 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) c8.le d1 (by norm_num) (by norm_num)
  rcases le_or_gt L (103 / 5) with d2 | d2
  · exact leaves 4 (110 / 579) (6079 / 28950) (203 / 10) (103 / 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) d1.le d2 (by norm_num) (by norm_num)
  rcases le_or_gt L (209 / 10) with d3 | d3
  · exact leaves 4 (55 / 294) (761 / 3675) (103 / 5) (209 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) d2.le d3 (by norm_num) (by norm_num)
  rcases le_or_gt L (106 / 5) with d4 | d4
  · exact leaves 4 (110 / 597) (6097 / 29850) (209 / 10) (106 / 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num) d3.le d4 (by norm_num) (by norm_num)
  rcases le_or_gt L (43 / 2) with d5 | d5
  · exact leaves 4 (55 / 303) (3053 / 15150) (106 / 5) (43 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) d4.le d5 (by norm_num) (by norm_num)
  rcases le_or_gt L (87 / 4) with d6 | d6
  · exact leaves 4 (22 / 123) (1223 / 6150) (43 / 2) (87 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) d5.le d6 (by norm_num) (by norm_num)
  rcases le_or_gt L 22 with d7 | d7
  · exact leaves 4 (44 / 249) (2449 / 12450) (87 / 4) 22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) d6.le d7 (by norm_num) (by norm_num)
  rcases le_or_gt L (89 / 4) with d8 | d8
  · exact leaves 4 (11 / 63) (613 / 3150) 22 (89 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) d7.le d8 (by norm_num) (by norm_num)
  rcases le_or_gt L (45 / 2) with d9 | d9
  · exact leaves 4 (44 / 255) (491 / 2550) (89 / 4) (45 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) d8.le d9 (by norm_num) (by norm_num)
  by_cases hU : 17 * v2 ≤ 12 * v4
  · exact k1_uniform h0 h12 hv3 h34 h45 hsmall hα hU
  · push Not at hU
    refine k1_step h0 h12 hv3 h34 h45 hα (toN 8 (by have := Lge 8 (by linarith); push_cast; linarith))
      (Or.inr ⟨?_, by omega⟩)
    have := Lge (45 / 2) d9.le
    have : (45 : ℝ) * v1 ≤ 2 * ((v4 : ℝ) - v2) := by linarith
    rw [← hdR] at this; exact_mod_cast this

end LRC.S6Native


