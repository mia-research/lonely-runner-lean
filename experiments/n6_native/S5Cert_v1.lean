import LonelyRunner.LRC.Spec.OrderSixSixRestN

/-!
# §5 natively, k ≥ 2 (n6_native, E105–E106): pair windows at `j₀`, the pair-window fold, and the small-α part

§5: `D = v₃ − v₂ ∣ v₁`, `3v₁ < v₃`. Runners 2 and 3 on one lap `j` are clear together on
`P_j = [(j+1/6)/v₂, (j+5/6)/v₃]`. `j₀` is the first lap with runner 1 past `1/6` at the start of `P_j`
(`v₂ ≤ v₁(6j₀+1) < v₂ + 6v₁`); then runner 1 is clear across all of `P_{j₀}` (`3v₁ < v₃` alone), and runners 4, 5 are
folded by `window_two_uniform` when `P_{j₀}` is at least `2/(3v₄)` (`s5_uniform_j0`). `s5_pair_fold`: any sub-window
of `P_j` where runners 1 and 4 are in bands and which runner 5 sweeps for a third of a lap.
-/

namespace LRC.S6Native
open LRC.S7Native LRC.S8Native

/-- The first lap `j₀` with runner 1 past `1/6` at the start of `P_j`. -/
theorem exists_j0 {v1 v2 : ℕ} (h1 : 0 < v1) : ∃ j0 : ℕ, v2 ≤ v1 * (6 * j0 + 1) ∧ v1 * (6 * j0 + 1) < v2 + 6 * v1 := by
  have hex : ∃ j : ℕ, v2 ≤ v1 * (6 * j + 1) := ⟨v2, by nlinarith⟩
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h]; omega
  · have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    push Not at hmin
    have e : 6 * Nat.find hex + 1 = (6 * (Nat.find hex - 1) + 1) + 6 := by omega
    rw [e, mul_add]; omega

/-- **§5, the uniform pair window at `j₀`.** -/
theorem s5_uniform_j0 {v1 v2 v3 v4 v5 j0 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4) (h45 : v4 ≤ v5)
    (hsmall : 3 * v1 < v3) (hj0a : v2 ≤ v1 * (6 * j0 + 1)) (hj0b : v1 * (6 * j0 + 1) < v2 + 6 * v1)
    (hw : 2 / (3 * (v4 : ℝ)) ≤ ((j0 : ℝ) + 5 / 6) / v3 - ((j0 : ℝ) + 1 / 6) / v2) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have h1R : (0 : ℝ) < v1 := by exact_mod_cast h0
  have h2 : 0 < v2 := by omega
  have h2R : (0 : ℝ) < v2 := by exact_mod_cast h2
  have h3R : (0 : ℝ) < v3 := by exact_mod_cast (show 0 < v3 by omega)
  have h4R : (0 : ℝ) < v4 := by exact_mod_cast (show 0 < v4 by omega)
  refine s5_pair_window (j := (j0 : ℤ)) (m := 0) (by positivity) h1R h2R (by exact_mod_cast h23.le) h4R
    (by exact_mod_cast h45) (by push_cast; exact le_refl _) (by push_cast; exact le_refl _) ?_ ?_ (by push_cast; linarith)
  · push_cast
    rw [div_le_div_iff₀ h1R h2R]
    have : (v2 : ℝ) ≤ v1 * (6 * j0 + 1) := by exact_mod_cast hj0a
    nlinarith
  · push_cast
    rw [div_le_div_iff₀ h3R h1R]
    have hb : (v1 : ℝ) * (6 * j0 + 1) < v2 + 6 * v1 := by exact_mod_cast hj0b
    have hs : 3 * (v1 : ℝ) < v3 := by exact_mod_cast hsmall
    have h23R : (v2 : ℝ) < v3 := by exact_mod_cast h23
    nlinarith

/-- **§5, the pair-window fold.** On a sub-window `[a, b]` of `P_j` where runner 1 (lap `n₁`) and runner 4 (lap `m`)
read in their bands at both ends, runner 5 is folded if `b − a ≥ 1/(3v₅)`. -/
theorem s5_pair_fold {v1 v2 v3 v4 v5 a b : ℝ} {j n1 m : ℤ} (hj : 0 ≤ j) (h1 : 0 < v1) (h2 : 0 < v2) (h23 : v2 ≤ v3)
    (h4 : 0 < v4) (h5 : 0 < v5)
    (ha2 : ((j : ℝ) + 1 / 6) / v2 ≤ a) (hb3 : b ≤ ((j : ℝ) + 5 / 6) / v3)
    (ha1 : (n1 : ℝ) + 1 / 6 ≤ v1 * a) (hb1 : v1 * b ≤ n1 + 5 / 6)
    (ha4 : (m : ℝ) + 1 / 6 ≤ v4 * a) (hb4 : v4 * b ≤ m + 5 / 6)
    (hlen : 1 / (3 * v5) ≤ b - a) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have h3 : 0 < v3 := lt_of_lt_of_le h2 h23
  have hjR : (0 : ℝ) ≤ j := by exact_mod_cast hj
  obtain ⟨t, ht1, ht2, c5⟩ := fold_one (J₀ := a) (ℓ := b - a) h5 hlen
  have htb : t ≤ b := by linarith
  rw [div_le_iff₀ h2] at ha2; rw [le_div_iff₀ h3] at hb3
  have ht0 : 0 ≤ t := by nlinarith
  refine ⟨t, ?_, ?_, ?_, ?_, c5⟩
  · apply clear_of_band (p := n1) <;> nlinarith
  · apply clear_of_band (p := j) <;> nlinarith
  · apply clear_of_band (p := j) <;> nlinarith
  · apply clear_of_band (p := m) <;> nlinarith


/-! ### E106: small `α = v₁/v₂ ≤ 1/25` -/

/-- **A progression with step `σ ∈ (0, 1]` lands in `[m, m + σ]` within `⌈1/σ⌉` steps.** -/
theorem step_meets_arc {σ : ℝ} (x0 : ℝ) (h0 : 0 < σ) :
    ∃ n : ℕ, ∃ m : ℤ, (m : ℝ) ≤ x0 + n * σ ∧ x0 + n * σ ≤ m + σ ∧ (n : ℝ) * σ ≤ 1 + σ := by
  have hc : (0 : ℝ) ≤ ⌈x0⌉ - x0 := by linarith [Int.le_ceil x0]
  have hc1 : (⌈x0⌉ : ℝ) - x0 < 1 := by linarith [Int.ceil_lt_add_one x0]
  refine ⟨⌈(⌈x0⌉ - x0) / σ⌉₊, ⌈x0⌉, ?_, ?_, ?_⟩
  · have a := Nat.le_ceil ((⌈x0⌉ - x0) / σ)
    rw [div_le_iff₀ h0] at a; linarith
  · have b := Nat.ceil_lt_add_one (div_nonneg hc h0.le)
    have b' := mul_lt_mul_of_pos_right b h0
    rw [add_mul, div_mul_cancel₀ _ h0.ne', one_mul] at b'
    linarith
  · have b := Nat.ceil_lt_add_one (div_nonneg hc h0.le)
    have b' := mul_lt_mul_of_pos_right b h0
    rw [add_mul, div_mul_cancel₀ _ h0.ne', one_mul] at b'
    linarith

/-- **The pair-window fold, runner 4's stretch chosen.** On `P_j = [s₀, s₁]` with runner 1 clear across it, runner 4
starting at `x = v₄s₀` and sweeping `w = v₄(s₁ − s₀) ≥ μ = v₄/(3v₅)`: if `x ∈ [M + 1/6 − w + μ, M + 5/6 − μ]`, lonely. -/
theorem s5_fold_x {v1 v2 v3 v4 v5 : ℝ} {j n1 M : ℤ} (hj : 0 ≤ j) (h1 : 0 < v1) (h2 : 0 < v2) (h23 : v2 ≤ v3)
    (h4 : 0 < v4) (h45 : v4 ≤ v5)
    (ha1 : (n1 : ℝ) + 1 / 6 ≤ v1 * (((j : ℝ) + 1 / 6) / v2)) (hb1 : v1 * (((j : ℝ) + 5 / 6) / v3) ≤ n1 + 5 / 6)
    (hw : v4 / (3 * v5) ≤ v4 * (((j : ℝ) + 5 / 6) / v3 - ((j : ℝ) + 1 / 6) / v2))
    (hlo : (M : ℝ) + 1 / 6 - v4 * (((j : ℝ) + 5 / 6) / v3 - ((j : ℝ) + 1 / 6) / v2) + v4 / (3 * v5) ≤
      v4 * (((j : ℝ) + 1 / 6) / v2))
    (hhi : v4 * (((j : ℝ) + 1 / 6) / v2) ≤ (M : ℝ) + 5 / 6 - v4 / (3 * v5)) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have h3 : 0 < v3 := lt_of_lt_of_le h2 h23
  have h5 : 0 < v5 := lt_of_lt_of_le h4 h45
  set s0 := ((j : ℝ) + 1 / 6) / v2 with hs0
  set s1 := ((j : ℝ) + 5 / 6) / v3 with hs1
  set μ := v4 / (3 * v5) with hμ
  set x := v4 * s0 with hx
  set w := v4 * (s1 - s0) with hwd
  have hμ0 : 0 < μ := by positivity
  have hμ3 : μ ≤ 1 / 3 := by rw [hμ, div_le_iff₀ (by positivity)]; linarith
  set ya := max x ((M : ℝ) + 1 / 6) with hya
  set yb := min (x + w) ((M : ℝ) + 5 / 6) with hyb
  have hyab : μ ≤ yb - ya := by
    rw [hya, hyb]
    rcases le_total x ((M : ℝ) + 1 / 6) with hx1 | hx1 <;>
    rcases le_total (x + w) ((M : ℝ) + 5 / 6) with hx2 | hx2 <;>
    simp only [max_eq_left, max_eq_right, min_eq_left, min_eq_right, hx1, hx2] <;> linarith
  have hxa : x ≤ ya := le_max_left _ _
  have hyb2 : yb ≤ x + w := min_le_left _ _
  have hs01 : s0 ≤ s1 := by
    have : 0 ≤ w := le_trans hμ0.le hw
    rw [hwd] at this; nlinarith
  refine s5_pair_fold (j := j) (n1 := n1) (m := M) (a := ya / v4) (b := yb / v4) hj h1 h2 h23 h4 h5 ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← hs0, le_div_iff₀ h4]; linarith
  · rw [← hs1, div_le_iff₀ h4]; rw [hwd] at hyb2; linarith
  · have : v1 * s0 ≤ v1 * (ya / v4) := by
      apply mul_le_mul_of_nonneg_left _ h1.le; rw [le_div_iff₀ h4]; linarith
    linarith
  · have : v1 * (yb / v4) ≤ v1 * s1 := by
      apply mul_le_mul_of_nonneg_left _ h1.le; rw [div_le_iff₀ h4]; rw [hwd] at hyb2; linarith
    linarith
  · rw [mul_div_cancel₀ _ h4.ne']; exact le_max_right _ _
  · rw [mul_div_cancel₀ _ h4.ne']; exact min_le_right _ _
  · rw [← sub_div, le_div_iff₀ h4]
    have : 1 / (3 * v5) * v4 = μ := by rw [hμ]; field_simp
    linarith


/-- A progression point `α(j + 1/6)` in any interval `[pa, pb]` with `pb − pa ≥ α` and `pa ≥ α/6`. -/
theorem exists_p {α pa pb : ℝ} (hα : 0 < α) (hpa : α / 6 ≤ pa) (hlen : α ≤ pb - pa) :
    ∃ j : ℕ, pa ≤ α * ((j : ℝ) + 1 / 6) ∧ α * ((j : ℝ) + 1 / 6) ≤ pb := by
  have h0 : (0 : ℝ) ≤ pa / α - 1 / 6 := by rw [sub_nonneg, le_div_iff₀ hα]; linarith
  refine ⟨⌈pa / α - 1 / 6⌉₊, ?_, ?_⟩
  · have a := Nat.le_ceil (pa / α - 1 / 6)
    have : pa / α ≤ (⌈pa / α - 1 / 6⌉₊ : ℝ) + 1 / 6 := by linarith
    rw [div_le_iff₀ hα] at this; linarith
  · have b := Nat.ceil_lt_add_one h0
    have : (⌈pa / α - 1 / 6⌉₊ : ℝ) + 1 / 6 < pa / α + 1 := by linarith
    have h2 := mul_lt_mul_of_pos_left this hα
    have e : α * (pa / α + 1) = pa + α := by field_simp
    linarith

set_option maxHeartbeats 1000000 in
/-- **A leaf in `(p, λ)`.** `p = v₁(j + 1/6)/v₂` (runner 1 at the start of `P_j`), `λ = (v₄ − v₂)/v₁` (runner 4 reads
`j + 1/6 + λp` there); with `α = v₁/v₂ ≤ 1/25`, `D ≤ v₁/2`, `p ∈ [1/6, 2/3]` and `λp ∈ [m − 1/3 + p/2, m + 1/3]`, lonely
(runner 5 folded alone, worst case `μ = 1/3`). -/
theorem s5_leafP {v1 v2 v3 v4 v5 D : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (hv3 : v3 = v2 + D) (hD2 : 2 * D ≤ v1)
    (h34 : v3 < v4) (h45 : v4 < v5) (hα : 25 * v1 ≤ v2) (j : ℕ) (m : ℤ)
    (hp1 : 1 / 6 ≤ (v1 : ℝ) * ((j : ℝ) + 1 / 6) / v2) (hp2 : (v1 : ℝ) * ((j : ℝ) + 1 / 6) / v2 ≤ 2 / 3)
    (hlo : (m : ℝ) - 1 / 3 + (v1 : ℝ) * ((j : ℝ) + 1 / 6) / v2 / 2 ≤
      ((v4 : ℝ) - v2) / v1 * ((v1 : ℝ) * ((j : ℝ) + 1 / 6) / v2))
    (hhi : ((v4 : ℝ) - v2) / v1 * ((v1 : ℝ) * ((j : ℝ) + 1 / 6) / v2) ≤ m + 1 / 3) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have h1R : (0 : ℝ) < v1 := by exact_mod_cast h0
  have h2R : (0 : ℝ) < v2 := by exact_mod_cast (show 0 < v2 by omega)
  have hv3R : (v3 : ℝ) = v2 + D := by rw [hv3]; push_cast; ring
  have hD2R : 2 * (D : ℝ) ≤ v1 := by exact_mod_cast hD2
  have hD0R : (0 : ℝ) ≤ D := by positivity
  have h3R : (0 : ℝ) < v3 := by rw [hv3R]; linarith
  have h23R : (v2 : ℝ) ≤ v3 := by rw [hv3R]; linarith
  have h34R : (v3 : ℝ) ≤ v4 := by exact_mod_cast h34.le
  have h45R : (v4 : ℝ) ≤ v5 := by exact_mod_cast h45.le
  have h4R : (0 : ℝ) < v4 := by linarith
  have h5R : (0 : ℝ) < v5 := by linarith
  have hαR : 25 * (v1 : ℝ) ≤ v2 := by exact_mod_cast hα
  set u : ℝ := (j : ℝ) + 1 / 6 with hu
  have hu0 : 0 < u := by positivity
  set p : ℝ := (v1 : ℝ) * u / v2 with hp
  set L : ℝ := ((v4 : ℝ) - v2) / v1 with hL
  set μ : ℝ := (v4 : ℝ) / (3 * v5) with hμ
  have hμ3 : μ ≤ 1 / 3 := by rw [hμ, div_le_iff₀ (by positivity)]; linarith
  have hμ0 : 0 < μ := by positivity
  -- runner 3's sweep across P_j: 2/3 − D u / v₂ ≥ 2/3 − p/2
  have hDu : (D : ℝ) * u / v2 ≤ p / 2 := by
    rw [hp, div_le_iff₀ h2R]; field_simp; nlinarith
  have e3 : (v3 : ℝ) * ((u + 2 / 3) / v3 - u / v2) = 2 / 3 - (D : ℝ) * u / v2 := by
    rw [hv3R]; field_simp; ring
  have hsw : 0 ≤ (u + 2 / 3) / v3 - u / v2 := by
    have : 0 < (v3 : ℝ) * ((u + 2 / 3) / v3 - u / v2) := by rw [e3]; linarith
    exact (pos_of_mul_pos_right this h3R.le).le
  have hw4 : 2 / 3 - p / 2 ≤ (v4 : ℝ) * ((u + 2 / 3) / v3 - u / v2) := by
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
    have c : (v1 : ℝ) / v2 ≤ 1 / 25 := by rw [div_le_iff₀ h2R]; linarith
    linarith
  · push_cast; rw [← hu, hj56]; linarith
  · push_cast; rw [← hu, hj56, ex]; linarith
  · push_cast; rw [← hu, ex]; linarith


set_option maxHeartbeats 4000000 in
/-- **§5, `k ≥ 2`, small `α = v₁/v₂ ≤ 1/25`.** `v₄ ≥ 1.21 v₂`: the uniform window at `j₀`. Otherwise, with
`λ = (v₄ − v₂)/v₁`: `λ ≤ 5` by six leaves in `(p, λ)` (an interval of `p` of length `≥ 1/25 ≥ α` holds a progression
point); `λ > 5` by the step lemma (runner 4 steps by `β = (v₄ − v₂)/v₂ < 0.21` per pair window). -/
theorem s5_small_alpha {v1 v2 v3 v4 v5 D : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (hv3 : v3 = v2 + D) (hD0 : 0 < D)
    (hD2 : 2 * D ≤ v1)
    (h34 : v3 < v4) (h45 : v4 < v5) (hsmall : 3 * v1 < v3) (hα : 25 * v1 ≤ v2) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have h1R : (0 : ℝ) < v1 := by exact_mod_cast h0
  have h2R : (0 : ℝ) < v2 := by exact_mod_cast (show 0 < v2 by omega)
  have hv3R : (v3 : ℝ) = v2 + D := by rw [hv3]; push_cast; ring
  have hD2R : 2 * (D : ℝ) ≤ v1 := by exact_mod_cast hD2
  have hD0R : (0 : ℝ) ≤ D := by positivity
  have h3R : (0 : ℝ) < v3 := by rw [hv3R]; linarith
  have h34R : (v3 : ℝ) < v4 := by exact_mod_cast h34
  have h4R : (0 : ℝ) < v4 := by linarith
  have hαR : 25 * (v1 : ℝ) ≤ v2 := by exact_mod_cast hα
  have hα' : (v1 : ℝ) / v2 ≤ 1 / 25 := by rw [div_le_iff₀ h2R]; linarith
  have hαp : (0 : ℝ) < (v1 : ℝ) / v2 := by positivity
  obtain ⟨j0, hj0a, hj0b⟩ := exists_j0 (v2 := v2) h0
  have hp0a : 1 / 6 ≤ (v1 : ℝ) * ((j0 : ℝ) + 1 / 6) / v2 := by
    rw [le_div_iff₀ h2R]; have : (v2 : ℝ) ≤ v1 * (6 * j0 + 1) := by exact_mod_cast hj0a
    linarith
  have hp0b : (v1 : ℝ) * ((j0 : ℝ) + 1 / 6) / v2 < 1 / 6 + 1 / 25 := by
    rw [div_lt_iff₀ h2R]; have : (v1 : ℝ) * (6 * j0 + 1) < v2 + 6 * v1 := by exact_mod_cast hj0b
    nlinarith
  by_cases hU : 121 * v2 ≤ 100 * v4
  · refine s5_uniform_j0 h0 h12 (by omega) h34 h45.le hsmall hj0a hj0b ?_
    have hUR : 121 * (v2 : ℝ) ≤ 100 * v4 := by exact_mod_cast hU
    set u0 : ℝ := (j0 : ℝ) + 1 / 6 with hu0
    have hj56 : (j0 : ℝ) + 5 / 6 = u0 + 2 / 3 := by rw [hu0]; ring
    rw [hj56]
    have e3 : (v3 : ℝ) * ((u0 + 2 / 3) / v3 - u0 / v2) = 2 / 3 - (D : ℝ) * u0 / v2 := by
      rw [hv3R]; field_simp; ring
    have hDu : (D : ℝ) * u0 / v2 ≤ (v1 : ℝ) * u0 / v2 / 2 := by
      rw [div_le_iff₀ h2R]; field_simp; have : (0 : ℝ) ≤ u0 := by positivity
      nlinarith
    have key : 169 / 300 ≤ (v3 : ℝ) * ((u0 + 2 / 3) / v3 - u0 / v2) := by rw [e3]; linarith
    have hR : 169 / 300 / (v3 : ℝ) ≤ (u0 + 2 / 3) / v3 - u0 / v2 := by
      rw [div_le_iff₀ h3R]; linarith
    have hv3b : 50 * (v3 : ℝ) ≤ 51 * v2 := by rw [hv3R]; linarith
    refine le_trans ?_ hR
    rw [div_le_div_iff₀ (by positivity) h3R]; nlinarith
  push Not at hU
  have hUR : 100 * (v4 : ℝ) < 121 * v2 := by exact_mod_cast hU
  set L : ℝ := ((v4 : ℝ) - v2) / v1 with hL
  have hL0 : 0 ≤ L := by rw [hL]; apply div_nonneg _ h1R.le; rw [hv3R] at h34R; linarith
  -- the leaf with m = 1 on an interval [pa, pb] of p
  have leaf1 : ∀ (pa pb l0 l1 : ℝ), 1 / 6 ≤ pa → pb ≤ 2 / 3 → 1 / 25 ≤ pb - pa → 1 / 2 ≤ l0 → l0 ≤ L → L ≤ l1 →
      2 / 3 ≤ pa * (l0 - 1 / 2) → l1 * pb ≤ 4 / 3 →
      ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
        (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
    intro pa pb l0 l1 hpa hpb hlen hl0 hl0L hLl1 hA hB
    obtain ⟨j, hj1, hj2⟩ := exists_p hαp (pa := pa) (pb := pb) (by linarith) (by linarith)
    have e : (v1 : ℝ) / v2 * ((j : ℝ) + 1 / 6) = (v1 : ℝ) * ((j : ℝ) + 1 / 6) / v2 := by ring
    rw [e] at hj1 hj2
    refine s5_leafP h0 h12 hv3 hD2 h34 h45 hα j 1 (by linarith) (by linarith) ?_ ?_
    · have := mul_le_mul hj1 (show l0 - 1 / 2 ≤ L - 1 / 2 by linarith) (by linarith) (by linarith)
      push_cast; nlinarith
    · have := mul_le_mul hLl1 hj2 (by positivity) (by linarith)
      push_cast; linarith
  rcases le_or_gt L (8 / 5) with hL1 | hL1
  · -- m = 0 on p ∈ [1/6, 5/24]
    obtain ⟨j, hj1, hj2⟩ := exists_p hαp (pa := 1 / 6) (pb := 5 / 24) (by linarith) (by linarith)
    have e : (v1 : ℝ) / v2 * ((j : ℝ) + 1 / 6) = (v1 : ℝ) * ((j : ℝ) + 1 / 6) / v2 := by ring
    rw [e] at hj1 hj2
    refine s5_leafP h0 h12 hv3 hD2 h34 h45 hα j 0 hj1 (by linarith) ?_ ?_
    · push_cast; have : 0 ≤ L * ((v1 : ℝ) * ((j : ℝ) + 1 / 6) / v2) := mul_nonneg hL0 (by linarith)
      linarith
    · have := mul_le_mul hL1 hj2 (by linarith) (by norm_num)
      push_cast; linarith
  rcases le_or_gt L 2 with hL2 | hL2
  · exact leaf1 (20 / 33) (2 / 3) (8 / 5) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL1.le hL2
      (by norm_num) (by norm_num)
  rcases le_or_gt L (5 / 2) with hL3 | hL3
  · exact leaf1 (4 / 9) (8 / 15) 2 (5 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL2.le hL3
      (by norm_num) (by norm_num)
  rcases le_or_gt L 3 with hL4 | hL4
  · exact leaf1 (1 / 3) (4 / 9) (5 / 2) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL3.le hL4
      (by norm_num) (by norm_num)
  rcases le_or_gt L 4 with hL5 | hL5
  · exact leaf1 (4 / 15) (1 / 3) 3 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL4.le hL5
      (by norm_num) (by norm_num)
  rcases le_or_gt L 5 with hL6 | hL6
  · exact leaf1 (4 / 21) (4 / 15) 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hL5.le hL6
      (by norm_num) (by norm_num)
  -- λ > 5: the step lemma with step β = (v₄ − v₂)/v₂ < 0.21
  set β : ℝ := ((v4 : ℝ) - v2) / v2 with hβ
  have hβ0 : 0 < β := by rw [hβ]; apply div_pos _ h2R; rw [hv3R] at h34R; linarith
  have hβ1 : β < 21 / 100 := by rw [hβ, div_lt_iff₀ h2R]; linarith
  have hLβ : L * ((v1 : ℝ) / v2) = β := by rw [hL, hβ]; field_simp
  set u0 : ℝ := (j0 : ℝ) + 1 / 6 with hu0
  obtain ⟨n, M, hM1, hM2, hn⟩ := step_meets_arc (β * u0) hβ0
  have hp : ∀ x : ℝ, (v1 : ℝ) * x / v2 = (v1 : ℝ) / v2 * x := fun x => by ring
  have hnα : (n : ℝ) * ((v1 : ℝ) / v2) ≤ (1 + β) / 5 := by
    have : (v1 : ℝ) / v2 * 5 ≤ β := by rw [← hLβ]; nlinarith
    nlinarith
  refine s5_leafP h0 h12 hv3 hD2 h34 h45 hα (j0 + n) M ?_ ?_ ?_ ?_
  · push_cast; rw [hp, show (j0 : ℝ) + n + 1 / 6 = u0 + n by rw [hu0]; ring, mul_add]
    rw [hp] at hp0a
    have : 0 ≤ (v1 : ℝ) / v2 * n := by positivity
    linarith
  · push_cast; rw [hp, show (j0 : ℝ) + n + 1 / 6 = u0 + n by rw [hu0]; ring, mul_add]
    rw [hp] at hp0b
    nlinarith
  · push_cast; rw [hp, ← mul_assoc, hLβ, show (j0 : ℝ) + n + 1 / 6 = u0 + n by rw [hu0]; ring]
    rw [hp] at hp0b
    have : (v1 : ℝ) / v2 * (u0 + n) ≤ 2 / 3 := by nlinarith
    nlinarith
  · push_cast; rw [hp, ← mul_assoc, hLβ, show (j0 : ℝ) + n + 1 / 6 = u0 + n by rw [hu0]; ring]
    nlinarith

end LRC.S6Native

#print axioms LRC.S6Native.s5_small_alpha
