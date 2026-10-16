import LonelyRunner.LRC.Spec.OrderSixSixNativeN

/-!
# BHK §6 natively, the remaining cases, and all of §6 (n6_native, E101–E103)

Moved into the tree 2026-10-16 from `experiments/n6_native/S6Coset_v1.lean` and `S6Small_v1.lean`, the certificate
extended from `E < 15` to `E < 20`. With `g = gcd(v₁, D)`:
* `g ∤ v₄` — `s6_coset`: at the meeting times sharing one runner-1 phase, runner 4 steps by `gcd(v₄, g)/g ≤ 1/2`.
* `g ∣ v₄`, `E = D/g < 20` — `s6_small`: a `decide +kernel` certificate over the classes `(E, l)` (`c ≥ 5`) and the points
  `(E, c, δ, v₁/g)` (`c ≤ 4`), all checks at `M = 1/3`.
* `g ∣ v₄`, `E ≥ 20` — `s6_scaled`: `s6_branch` on `(v₁, …, v₄)/g` and the real speed `v₅/g`.
`lonely_6_native` is §6 in the dispatch's form.
-/

namespace LRC.S6Native
open LRC.S7Native LRC.S8Native

/-! ### `g ∤ v₄` (from `S6Coset_v1.lean`) -/

/-- **A progression with step in `(0, 1/2]` meets every closed half arc.** -/
theorem step_meets_half_arc {σ : ℝ} (x0 : ℝ) (h0 : 0 < σ) (h1 : σ ≤ 1 / 2) :
    ∃ n : ℕ, ∃ m : ℤ, (m : ℝ) ≤ x0 + n * σ ∧ x0 + n * σ ≤ m + 1 / 2 := by
  have hc : (0 : ℝ) ≤ ⌈x0⌉ - x0 := by linarith [Int.le_ceil x0]
  refine ⟨⌈(⌈x0⌉ - x0) / σ⌉₊, ⌈x0⌉, ?_, ?_⟩
  · have a := Nat.le_ceil ((⌈x0⌉ - x0) / σ)
    rw [div_le_iff₀ h0] at a; linarith
  · have b := Nat.ceil_lt_add_one (div_nonneg hc h0.le)
    have b' := mul_lt_mul_of_pos_right b h0
    rw [add_mul, div_mul_cancel₀ _ h0.ne', one_mul] at b'
    linarith

set_option maxHeartbeats 1000000 in
/-- **§6 with `gcd(v₁, D) ∤ v₄`.** `v₂ = cD`, `v₃ = (c+1)D` (`c ≥ 1`), `3v₁ < v₃`, `v₃ < v₄ ≤ v₅`, `D ∤ v₁`, and
`g = gcd(v₁, D)` not dividing `v₄`: some instant is lonely. -/
theorem s6_coset {v1 v2 v3 v4 v5 c D : ℕ} (h0 : 0 < v1) (h34 : v3 < v4) (h45 : v4 ≤ v5) (hc : 1 ≤ c)
    (hv2 : v2 = c * D) (hv3 : v3 = (c + 1) * D) (hsmall : 3 * v1 < v3) (hD0 : 0 < D) (hnd : ¬ D ∣ v1)
    (hg : ¬ Nat.gcd v1 D ∣ v4) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  set g := Nat.gcd v1 D with hgdef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ hD0
  obtain ⟨Dp, hDp⟩ : g ∣ D := Nat.gcd_dvd_right v1 D
  obtain ⟨a, ha⟩ : g ∣ v1 := Nat.gcd_dvd_left v1 D
  -- runner 1's phase: the orbit residue
  obtain ⟨k0, hk1, hk2⟩ := orbit_residue v1 D hD0 hnd
  set r := v1 * k0 % D with hr
  -- runner 4's step: d = gcd(v4, g) < g
  set d := Nat.gcd v4 g with hddef
  have hdg_dvd : d ∣ g := Nat.gcd_dvd_right v4 g
  have hdv4 : d ∣ v4 := Nat.gcd_dvd_left v4 g
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_right _ hg0
  have hdlt : d < g := by
    rcases lt_or_eq_of_le (Nat.le_of_dvd hg0 hdg_dvd) with h | h
    · exact h
    · exact absurd (h ▸ hdv4) hg
  have hd2 : 2 * d ≤ g := by
    obtain ⟨e, he⟩ := hdg_dvd
    have : 2 ≤ e := by
      rcases Nat.lt_or_ge e 2 with h | h
      · interval_cases e <;> simp at he <;> omega
      · exact h
    rw [he]; nlinarith
  obtain ⟨i, -, hi⟩ := Nat.exists_mul_mod_eq_gcd (k := g) (n := v4) hdlt
  set q := v4 * i / g with hq
  have hqi : v4 * i = g * q + d := by
    have := (Nat.div_add_mod (v4 * i) g).symm; rw [hi] at this; exact this
  -- real setup (as in s6_generic)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD0
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg0
  have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hv2R : (v2 : ℝ) = c * D := by rw [hv2]; push_cast; ring
  have hv3R : (v3 : ℝ) = (c + 1) * D := by rw [hv3]; push_cast; ring
  have h2p : (0 : ℝ) < v2 := by rw [hv2R]; positivity
  have h23 : (v2 : ℝ) ≤ v3 := by rw [hv2R, hv3R]; nlinarith
  have h3p : (0 : ℝ) < v3 := lt_of_lt_of_le h2p h23
  have h1p : (0 : ℝ) < v1 := by exact_mod_cast h0
  have h13 : 3 * (v1 : ℝ) < v3 := by exact_mod_cast hsmall
  have h34R : (v3 : ℝ) ≤ v4 := by exact_mod_cast h34.le
  have h45R : (v4 : ℝ) ≤ v5 := by exact_mod_cast h45
  have h4p : (0 : ℝ) < v4 := lt_of_lt_of_le h3p h34R
  have h5p : (0 : ℝ) < v5 := lt_of_lt_of_le h4p h45R
  set s0 : ℝ := 1 / (6 * v2) with hs0
  set s1 : ℝ := 5 / (6 * v3) with hs1
  set lam : ℝ := v4 * (s1 - s0) with hlam
  set μ : ℝ := v4 / (3 * v5) with hμ
  have hlam2 : (1 : ℝ) / 2 ≤ lam := by
    have hd : (0 : ℝ) ≤ s1 - s0 := by
      rw [hs0, hs1, sub_nonneg, div_le_div_iff₀ (by positivity) (by positivity)]; rw [hv2R, hv3R]; nlinarith
    have : (v3 : ℝ) * (s1 - s0) ≤ lam := by rw [hlam]; exact mul_le_mul_of_nonneg_right h34R hd
    have e : (v3 : ℝ) * (s1 - s0) = 5 / 6 - v3 / (6 * v2) := by rw [hs0, hs1]; field_simp
    have : (v3 : ℝ) / (6 * v2) ≤ 1 / 3 := by
      rw [div_le_iff₀ (by positivity), hv2R, hv3R]; nlinarith
    linarith
  have hμ3 : μ ≤ 1 / 3 := by rw [hμ, div_le_iff₀ (by positivity)]; linarith
  -- the step and the half arc
  set σ : ℝ := (d : ℝ) / g with hσ
  have hσ0 : 0 < σ := by rw [hσ]; have : (0 : ℝ) < d := by exact_mod_cast hd0
                         positivity
  have hσ1 : σ ≤ 1 / 2 := by
    rw [hσ, div_le_iff₀ hgR]; have : (2 * d : ℝ) ≤ g := by exact_mod_cast hd2
    linarith
  set x₀ : ℝ := 1 / 6 - lam + μ - v4 * s0 with hx₀
  obtain ⟨n, m, hm1, hm2⟩ := step_meets_half_arc ((v4 : ℝ) * k0 / D - x₀) hσ0 hσ1
  set k := k0 + Dp * (i * n) with hk
  set T : ℝ := (k : ℝ) / D with hT
  have hDpR : (D : ℝ) = g * Dp := by rw [hDp]; push_cast; ring
  have hDp0 : (0 : ℝ) < Dp := by
    have : (0 : ℝ) < g * Dp := by rw [← hDpR]; exact hDR
    exact pos_of_mul_pos_right this hgR.le
  have hT2 : (v2 : ℝ) * T = ((c * k : ℕ) : ℤ) := by rw [hT, hv2R]; push_cast; field_simp
  have hT3 : (v3 : ℝ) * T = (((c + 1) * k : ℕ) : ℤ) := by rw [hT, hv3R]; push_cast; field_simp
  have hT1 : (v1 : ℝ) * T = (((v1 * k0 / D + a * (i * n) : ℕ) : ℤ) : ℝ) + (r : ℝ) / D := by
    set Q1 := v1 * k0 / D with hQ1
    have hdm : (v1 : ℝ) * k0 = D * Q1 + r := by
      have := (Nat.div_add_mod (v1 * k0) D).symm
      exact_mod_cast this
    have hv1R : (v1 : ℝ) = g * a := by rw [ha]; push_cast; ring
    rw [hT, hk, Int.cast_natCast]
    simp only [Nat.cast_add, Nat.cast_mul]
    field_simp
    linear_combination hdm + ((Dp : ℝ) * i * n) * hv1R - ((a : ℝ) * i * n) * hDpR
  have hT4 : (v4 : ℝ) * T = (((q * n : ℕ) : ℤ) : ℝ) + ((v4 : ℝ) * k0 / D + n * σ) := by
    have e : (v4 : ℝ) * i = g * q + d := by exact_mod_cast hqi
    rw [hT, hk, hσ]; push_cast
    rw [hDpR]
    field_simp
    linear_combination (n : ℝ) * Dp * e
  have hp1a : (1 : ℝ) / 6 ≤ (r : ℝ) / D := by
    rw [le_div_iff₀ hDR]; have : (D : ℝ) ≤ 6 * r := by exact_mod_cast hk1
    linarith
  have hp1b : (r : ℝ) / D ≤ 5 / 9 := by
    rw [div_le_iff₀ hDR]; have : 9 * (r : ℝ) ≤ 5 * D := by exact_mod_cast hk2
    linarith
  have hx : (v4 : ℝ) / (6 * v2) = v4 * s0 := by rw [hs0]; ring
  refine s6_window_fold (m := m) h1p hDR h2p h23 h13 h34R h45R hT2 hT3 hT1 hT4 hp1a hp1b ?_ ?_ ?_
  · rw [hx]; linarith
  · rw [hx]; linarith
  · linarith

/-! ### `g ∣ v₄`, `E < 20` (from `S6Small_v1.lean`) -/

/-- Readings at a meeting time with orbit modulus `E = D/g`. -/
theorem readings_E {a w4 c E g : ℕ} (hg : 0 < g) (hcop : Nat.Coprime a E) (hE : 1 < E) {j : ℕ} (hjE : j < E)
    (l : ℤ) (hl : (w4 : ℤ) ≡ l * a [ZMOD E]) :
    ∃ T : ℝ, ∃ N1 N2 N3 N4 : ℤ, ((g * a : ℕ) : ℝ) * T = N1 + (j : ℝ) / E ∧
      ((c * (g * E) : ℕ) : ℝ) * T = N2 ∧ (((c + 1) * (g * E) : ℕ) : ℝ) * T = N3 ∧
      ((g * w4 : ℕ) : ℝ) * T = N4 + (l : ℝ) * j / E := by
  obtain ⟨T, N1, N2, N3, N4, h1, h2, h3, h4⟩ :=
    readings_at (v1 := a) (v2 := c * E) (v3 := (c + 1) * E) (v4 := w4) (c := c) (D := E) rfl rfl hcop hE hjE l hl
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  refine ⟨T / g, N1, N2, N3, N4, ?_, ?_, ?_, ?_⟩
  · rw [← h1]; push_cast; field_simp
  · rw [← h2]; push_cast; field_simp
  · rw [← h3]; push_cast; field_simp
  · rw [← h4]; push_cast; field_simp

section realclosers
variable {v1 v2 v3 v4 v5 T p1 p4 : ℝ} {N1 N2 N3 N4 : ℤ}

theorem lam_half (h2 : 0 < v2) (h23 : v2 ≤ v3) (h2h : v3 ≤ 2 * v2) (h34 : v3 ≤ v4) (h45 : v4 ≤ v5) :
    v4 / (3 * v5) ≤ v4 * (5 / (6 * v3) - 1 / (6 * v2)) := by
  have h3 : 0 < v3 := lt_of_lt_of_le h2 h23
  have h4 : 0 < v4 := lt_of_lt_of_le h3 h34
  have hμ : v4 / (3 * v5) ≤ 1 / 3 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hd : (0 : ℝ) ≤ 5 / (6 * v3) - 1 / (6 * v2) := by
    rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have : v3 * (5 / (6 * v3) - 1 / (6 * v2)) ≤ v4 * (5 / (6 * v3) - 1 / (6 * v2)) :=
    mul_le_mul_of_nonneg_right h34 hd
  have e : v3 * (5 / (6 * v3) - 1 / (6 * v2)) = 5 / 6 - v3 / (6 * v2) := by field_simp
  have : v3 / (6 * v2) ≤ 1 / 3 := by rw [div_le_iff₀ (by positivity)]; linarith
  linarith

/-- The window after the meeting time, readings given. -/
theorem closeA (h1 : 0 < v1) (h2 : 0 < v2) (h23 : v2 ≤ v3) (h2h : v3 ≤ 2 * v2) (h13 : 3 * v1 < v3)
    (h34 : v3 ≤ v4) (h45 : v4 ≤ v5)
    (hT1 : v1 * T = N1 + p1) (hT2 : v2 * T = N2) (hT3 : v3 * T = N3) (hT4 : v4 * T = N4 + p4)
    (hp1 : 1 / 6 ≤ p1) (hp2 : p1 ≤ 5 / 9) (m : ℤ)
    (hlow : (m : ℝ) + 1 / 6 ≤ p4 + 5 / 6 * (v4 / v3) - v4 / (3 * v5))
    (hup : p4 + (v4 / v3) * (v3 / v2) / 6 + v4 / (3 * v5) ≤ m + 5 / 6) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have h3 : 0 < v3 := lt_of_lt_of_le h2 h23
  have e1 : v4 * (5 / (6 * v3)) = 5 / 6 * (v4 / v3) := by field_simp
  have e2 : v4 / (6 * v2) = (v4 / v3) * (v3 / v2) / 6 := by field_simp
  have e3 : v4 * (1 / (6 * v2)) = v4 / (6 * v2) := by ring
  refine s6_window_fold (D := 1) (m := m) h1 one_pos h2 h23 h13 h34 h45 hT2 hT3 hT1 hT4 hp1 hp2 ?_ ?_
    (lam_half h2 h23 h2h h34 h45)
  · rw [mul_sub, e1, e3, e2]; linarith
  · rw [e2]; linarith

/-- The window before the meeting time, readings given. -/
theorem closeB (h1 : 0 < v1) (h2 : 0 < v2) (h23 : v2 ≤ v3) (h2h : v3 ≤ 2 * v2) (h13 : 3 * v1 < v3)
    (h34 : v3 ≤ v4) (h45 : v4 ≤ v5)
    (hT1 : v1 * T = N1 + p1) (hT2 : v2 * T = N2) (hT3 : v3 * T = N3) (hT4 : v4 * T = N4 + p4)
    (hp1 : 4 / 9 ≤ p1) (hp2 : p1 ≤ 5 / 6) (m : ℤ)
    (hlow : (m : ℝ) + 1 / 6 ≤ 1 - p4 + 5 / 6 * (v4 / v3) - v4 / (3 * v5))
    (hup : 1 - p4 + (v4 / v3) * (v3 / v2) / 6 + v4 / (3 * v5) ≤ m + 5 / 6) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have h3 : 0 < v3 := lt_of_lt_of_le h2 h23
  have e1 : v4 * (5 / (6 * v3)) = 5 / 6 * (v4 / v3) := by field_simp
  have e2 : v4 / (6 * v2) = (v4 / v3) * (v3 / v2) / 6 := by field_simp
  have e3 : v4 * (1 / (6 * v2)) = v4 / (6 * v2) := by ring
  refine s6_window_fold_before (D := 1) (m := m) h1 one_pos h2 h23 h13 h34 h45 hT2 hT3 hT1 hT4 hp1 hp2 ?_ ?_
    (lam_half h2 h23 h2h h34 h45)
  · rw [mul_sub, e1, e3, e2]; linarith
  · rw [e2]; linarith

/-- **A block of four runners in their bands on `[T + sa, T + sb]`, runner 5 folded.** -/
theorem closeF (h1 : 0 < v1) (h2 : 0 < v2) (h3 : 0 < v3) (h4 : 0 < v4) (h5 : 0 < v5) {sa sb : ℝ}
    {m1 m2 m3 m4 : ℤ}
    (hT1 : v1 * T = N1 + p1) (hT2 : v2 * T = N2) (hT3 : v3 * T = N3) (hT4 : v4 * T = N4 + p4)
    (a1 : (m1 : ℝ) + 1 / 6 ≤ p1 + v1 * sa) (b1 : p1 + v1 * sb ≤ m1 + 5 / 6)
    (a2 : (m2 : ℝ) + 1 / 6 ≤ v2 * sa) (b2 : v2 * sb ≤ m2 + 5 / 6)
    (a3 : (m3 : ℝ) + 1 / 6 ≤ v3 * sa) (b3 : v3 * sb ≤ m3 + 5 / 6)
    (a4 : (m4 : ℝ) + 1 / 6 ≤ p4 + v4 * sa) (b4 : p4 + v4 * sb ≤ m4 + 5 / 6)
    (h5l : 1 / (3 * v5) ≤ sb - sa) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  obtain ⟨t, ht1, ht2, c5⟩ := fold_one (J₀ := T + sa) (ℓ := sb - sa) h5 h5l
  set s := t - T with hs
  have hs1 : sa ≤ s := by rw [hs]; linarith
  have hs2 : s ≤ sb := by rw [hs]; linarith
  have ht : t = T + s := by rw [hs]; ring
  have m1' := mul_le_mul_of_nonneg_left hs1 h1.le
  have m1'' := mul_le_mul_of_nonneg_left hs2 h1.le
  have m2' := mul_le_mul_of_nonneg_left hs1 h2.le
  have m2'' := mul_le_mul_of_nonneg_left hs2 h2.le
  have m3' := mul_le_mul_of_nonneg_left hs1 h3.le
  have m3'' := mul_le_mul_of_nonneg_left hs2 h3.le
  have m4' := mul_le_mul_of_nonneg_left hs1 h4.le
  have m4'' := mul_le_mul_of_nonneg_left hs2 h4.le
  refine ⟨t, ?_, ?_, ?_, ?_, c5⟩
  · rw [ht, mul_add, hT1]; apply clear_of_band (p := N1 + m1) <;> push_cast <;> linarith
  · rw [ht, mul_add, hT2]; apply clear_of_band (p := N2 + m2) <;> push_cast <;> linarith
  · rw [ht, mul_add, hT3]; apply clear_of_band (p := N3 + m3) <;> push_cast <;> linarith
  · rw [ht, mul_add, hT4]; apply clear_of_band (p := N4 + m4) <;> push_cast <;> linarith

end realclosers

/-! ### The checker (ℚ, at `M = 1/3`) -/

/-- The lap for runner 4's band: `⌊x + 5Q₀/6 − 1/2⌋`. -/
def mA (x Qlo : ℚ) : ℤ := ⌊x + 5 / 6 * Qlo - 1 / 2⌋

/-- Window after: runner 1 reads `j/E ∈ [1/6, 5/9]`, runner 4 reads `x`; `Q ≥ Qlo`, `QU ≤ QUhi`, `M ≤ 1/3`. -/
def okA (E j : ℕ) (x Qlo QUhi : ℚ) : Bool :=
  decide (E ≤ 6 * j) && decide (9 * j ≤ 5 * E) && decide (x + QUhi / 6 + 1 / 3 ≤ (mA x Qlo : ℚ) + 5 / 6)

/-- Window before: runner 1 reads `j/E ∈ [4/9, 5/6]`, runner 4's mirrored reading `1 − x`. -/
def okB (E j : ℕ) (x Qlo QUhi : ℚ) : Bool :=
  decide (4 * E ≤ 9 * j) && decide (6 * j ≤ 5 * E) &&
    decide ((1 - x) + QUhi / 6 + 1 / 3 ≤ (mA (1 - x) Qlo : ℚ) + 5 / 6)

def regionOK (E l : ℕ) (Qlo QUhi : ℚ) : Bool :=
  (List.range E).any fun j => okA E j ((l : ℚ) * j / E) Qlo QUhi || okB E j ((l : ℚ) * j / E) Qlo QUhi

/-- `c ≥ 5`: the class `(E, l)` is empty (`6E ≤ 19 gcd(l, E)`), or one window closes the box `Q ≥ 1`, `QU ≤ 24/19`. -/
def bigOK (E l : ℕ) : Bool := decide (6 * E ≤ 19 * Nat.gcd l E) || regionOK E l 1 (24 / 19)

theorem bigAll : ((List.range 20).all fun E => (List.range E).all fun l => bigOK E l) = true := by decide +kernel

/-- Sum lemma at `M = 1/3` (only when `δ = a`, i.e. `v₄ = v₃ + v₁`). -/
def sumOK (E δ a : ℕ) (Q : ℚ) : Bool :=
  decide (δ = a) && (List.range E).any fun j =>
    decide (1 / 3 ≤ ((j : ℚ) / E - 1 / 3) * Q) && decide ((j : ℚ) / E ≤ 5 / 6 * (2 - Q))

structure FoldW where
  E : ℕ
  c : ℕ
  δ : ℕ
  a : ℕ
  j : ℕ
  sa : ℚ
  sb : ℚ

/-- The ten sub-window folds (`s6_small_fold_v1.py`); `sa, sb` in units of `1/g`. -/
def foldWs : List FoldW := [
  ⟨4, 1, 1, 1, 1, -1/12, -5/108⟩,
  ⟨5, 1, 1, 1, 2, -1/12, -17/330⟩,
  ⟨5, 1, 2, 2, 2, -1/12, -17/360⟩,
  ⟨5, 1, 3, 3, 2, -7/90, -17/390⟩,
  ⟨7, 1, 3, 2, 1, 19/714, 5/84⟩,
  ⟨7, 1, 3, 3, 3, -5/84, -25/714⟩,
  ⟨7, 3, 1, 8, 1, 1/126, 1/42⟩,
  ⟨7, 3, 2, 9, 1, 1/126, 29/1260⟩,
  ⟨7, 4, 2, 9, 1, 1/168, 29/1554⟩,
  ⟨8, 2, 3, 3, 1, 1/72, 17/648⟩]

/-- A reading `r(s) = p + w s` stays in the band of lap `⌊p + w sa − 1/6⌋` across `[sa, sb]`. -/
def bandQ (p w sa sb : ℚ) : Bool := decide (p + w * sb ≤ (⌊p + w * sa - 1 / 6⌋ : ℚ) + 5 / 6)

def foldOK (E c δ a l : ℕ) (f : FoldW) : Bool :=
  decide (f.E = E) && decide (f.c = c) && decide (f.δ = δ) && decide (f.a = a) && decide (f.j < E) &&
    decide (f.sa ≤ f.sb) &&
    bandQ ((f.j : ℚ) / E) a f.sa f.sb && bandQ 0 ((c : ℚ) * E) f.sa f.sb &&
    bandQ 0 (((c : ℚ) + 1) * E) f.sa f.sb &&
    bandQ ((l : ℚ) * f.j / E) (((c : ℚ) + 1) * E + δ) f.sa f.sb &&
    decide (1 / 3 ≤ (((c : ℚ) + 1) * E + δ) * (f.sb - f.sa))

def invE (a E : ℕ) : ℕ := ((List.range E).find? fun u => a * u % E == 1).getD 0

/-- `c ≤ 4`: the point `(E, c, δ, a)` (`a = v₁/g`, `δ = (v₄ − v₃)/g`). -/
def smallOK (E c δ a : ℕ) : Bool :=
  let u := invE a E
  let l := δ * u % E
  let Q : ℚ := 1 + (δ : ℚ) / ((c + 1) * E)
  decide (a * u % E = 1) &&
    (regionOK E l Q (Q * (c + 1) / c) || sumOK E δ a Q || foldWs.any (foldOK E c δ a l))

def smallHyp (E c δ a : ℕ) : Bool :=
  decide (2 ≤ E) && decide (1 ≤ c) && decide (1 ≤ δ) && decide (4 * c * δ < (c + 1) * E + δ) && decide (1 ≤ a) &&
    decide (3 * a < (c + 1) * E) && decide (Nat.Coprime a E)

theorem smallAll : ((List.range 20).all fun E => (List.range 5).all fun c => (List.range 32).all fun δ =>
    (List.range 32).all fun a => !smallHyp E c δ a || smallOK E c δ a) = true := by decide +kernel

/-! ### Soundness -/

/-- Readings at the meeting times for every runner-1 phase `j/E`. -/
def Readings (V1 V2 V3 V4 : ℝ) (E l : ℕ) : Prop :=
  ∀ j < E, ∃ T : ℝ, ∃ N1 N2 N3 N4 : ℤ, V1 * T = N1 + (j : ℝ) / E ∧ V2 * T = N2 ∧ V3 * T = N3 ∧
    V4 * T = N4 + ((l : ℤ) : ℝ) * j / E

def Lonely5 (V1 V2 V3 V4 V5 : ℝ) : Prop :=
  ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (V1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (V2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (V3 * t) ∧
    (6 : ℝ)⁻¹ ≤ circDist (V4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (V5 * t)

theorem region_sound {V1 V2 V3 V4 V5 : ℝ} {E l : ℕ} {Qlo QUhi : ℚ} (hE : 0 < E) (h1 : 0 < V1) (h2 : 0 < V2)
    (h23 : V2 ≤ V3) (h2h : V3 ≤ 2 * V2) (h13 : 3 * V1 < V3) (h34 : V3 ≤ V4) (h45 : V4 ≤ V5)
    (hQ : (Qlo : ℝ) ≤ V4 / V3) (hQU : V4 / V3 * (V3 / V2) ≤ (QUhi : ℝ)) (hr : Readings V1 V2 V3 V4 E l)
    (hc : regionOK E l Qlo QUhi = true) : Lonely5 V1 V2 V3 V4 V5 := by
  have h3 : 0 < V3 := lt_of_lt_of_le h2 h23
  have h4 : 0 < V4 := lt_of_lt_of_le h3 h34
  have hM : V4 / (3 * V5) ≤ 1 / 3 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hER : (0 : ℝ) < E := by exact_mod_cast hE
  simp only [regionOK, List.any_eq_true, List.mem_range, Bool.or_eq_true] at hc
  obtain ⟨j, hj, hjc⟩ := hc
  obtain ⟨T, N1, N2, N3, N4, hT1, hT2, hT3, hT4⟩ := hr j hj
  rcases hjc with hA | hB
  · simp only [okA, Bool.and_eq_true, decide_eq_true_eq] at hA
    obtain ⟨⟨hj1, hj2⟩, hup⟩ := hA
    have hfl := Int.floor_le ((l : ℚ) * j / E + 5 / 6 * Qlo - 1 / 2)
    have hfl' : ((mA ((l : ℚ) * j / E) Qlo : ℤ) : ℝ) ≤ (l : ℝ) * j / E + 5 / 6 * (Qlo : ℝ) - 1 / 2 := by
      have := (Rat.cast_le (K := ℝ)).mpr hfl; push_cast at this; exact this
    have hup' : (l : ℝ) * j / E + (QUhi : ℝ) / 6 + 1 / 3 ≤ ((mA ((l : ℚ) * j / E) Qlo : ℤ) : ℝ) + 5 / 6 := by
      have := (Rat.cast_le (K := ℝ)).mpr hup; push_cast at this; exact this
    refine closeA h1 h2 h23 h2h h13 h34 h45 hT1 hT2 hT3 hT4 ?_ ?_ (mA ((l : ℚ) * j / E) Qlo) ?_ ?_
    · rw [le_div_iff₀ hER]; have : (E : ℝ) ≤ 6 * j := by exact_mod_cast hj1
      linarith
    · rw [div_le_iff₀ hER]; have : 9 * (j : ℝ) ≤ 5 * E := by exact_mod_cast hj2
      linarith
    · push_cast; linarith
    · push_cast; linarith
  · simp only [okB, Bool.and_eq_true, decide_eq_true_eq] at hB
    obtain ⟨⟨hj1, hj2⟩, hup⟩ := hB
    have hfl := Int.floor_le ((1 - (l : ℚ) * j / E) + 5 / 6 * Qlo - 1 / 2)
    have hfl' : ((mA (1 - (l : ℚ) * j / E) Qlo : ℤ) : ℝ) ≤ (1 - (l : ℝ) * j / E) + 5 / 6 * (Qlo : ℝ) - 1 / 2 := by
      have := (Rat.cast_le (K := ℝ)).mpr hfl; push_cast at this; exact this
    have hup' : (1 - (l : ℝ) * j / E) + (QUhi : ℝ) / 6 + 1 / 3 ≤
        ((mA (1 - (l : ℚ) * j / E) Qlo : ℤ) : ℝ) + 5 / 6 := by
      have := (Rat.cast_le (K := ℝ)).mpr hup; push_cast at this; exact this
    refine closeB h1 h2 h23 h2h h13 h34 h45 hT1 hT2 hT3 hT4 ?_ ?_ (mA (1 - (l : ℚ) * j / E) Qlo) ?_ ?_
    · rw [le_div_iff₀ hER]; have : 4 * (E : ℝ) ≤ 9 * j := by exact_mod_cast hj1
      linarith
    · rw [div_le_iff₀ hER]; have : 6 * (j : ℝ) ≤ 5 * E := by exact_mod_cast hj2
      linarith
    · push_cast; linarith
    · push_cast; linarith

theorem sum_sound {V1 V2 V3 V4 V5 : ℝ} {E l δ a : ℕ} {Q : ℚ} (hE : 0 < E) (h1 : 0 < V1) (h2 : 0 < V2)
    (h23 : V2 ≤ V3) (h2h : V3 ≤ 2 * V2) (h34 : V3 ≤ V4) (h45 : V4 ≤ V5)
    (hQ : V4 / V3 = (Q : ℝ)) (hsum : δ = a → V4 = V3 + V1 ∧ V1 / V3 = (Q : ℝ) - 1)
    (hr : Readings V1 V2 V3 V4 E l) (hc : sumOK E δ a Q = true) : Lonely5 V1 V2 V3 V4 V5 := by
  have h3 : 0 < V3 := lt_of_lt_of_le h2 h23
  have h4 : 0 < V4 := lt_of_lt_of_le h3 h34
  have h5 : 0 < V5 := lt_of_lt_of_le h4 h45
  simp only [sumOK, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range] at hc
  obtain ⟨hδ, j, hj, hp1, hp2⟩ := hc
  obtain ⟨hV4, hV1⟩ := hsum hδ
  obtain ⟨T, N1, N2, N3, N4, hT1, hT2, hT3, -⟩ := hr j hj
  have hp1' : 1 / 3 ≤ ((j : ℝ) / E - 1 / 3) * (Q : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr hp1; push_cast at this; exact this
  have hp2' : (j : ℝ) / E ≤ 5 / 6 * (2 - (Q : ℝ)) := by
    have := (Rat.cast_le (K := ℝ)).mpr hp2; push_cast at this; exact this
  have hQp : (0 : ℝ) < Q := by rw [← hQ]; positivity
  have hlo : 1 / 3 + V3 / (3 * V5) ≤ (j : ℝ) / E := by
    have e : V3 / (3 * V5) ≤ 1 / (3 * (Q : ℝ)) := by
      rw [← hQ, div_le_div_iff₀ (by positivity) (by positivity)]
      have : V3 * (3 * (V4 / V3)) = 3 * V4 := by field_simp
      rw [this]; linarith
    have e2 : 1 / (3 * (Q : ℝ)) ≤ (j : ℝ) / E - 1 / 3 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have hhi : (j : ℝ) / E ≤ 5 / 6 * (1 - V1 / V3) := by rw [hV1]; linarith
  obtain ⟨t, a1, a2, a3, a4, a5⟩ := s6_sum_window h1 h2 h23 h2h h5 hT1 hT2 hT3 hlo hhi
  exact ⟨t, a1, a2, a3, by rw [hV4]; exact a4, a5⟩

theorem fold_sound {V1 V2 V3 V4 V5 g : ℝ} {E c δ a l : ℕ} (hg : 0 < g) (hE : 0 < E) (ha : 0 < a) (hc : 1 ≤ c)
    (hV1 : V1 = g * a) (hV2 : V2 = g * (c * E)) (hV3 : V3 = g * ((c + 1) * E)) (hV4 : V4 = g * ((c + 1) * E + δ))
    (h45 : V4 ≤ V5) (hr : Readings V1 V2 V3 V4 E l) (hf : foldWs.any (foldOK E c δ a l) = true) :
    Lonely5 V1 V2 V3 V4 V5 := by
  have hER : (0 : ℝ) < E := by exact_mod_cast hE
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have h1 : 0 < V1 := by rw [hV1]; positivity
  have h2 : 0 < V2 := by rw [hV2]; have : (0 : ℝ) < c := by linarith
                         positivity
  have h3 : 0 < V3 := by rw [hV3]; positivity
  have h4 : 0 < V4 := by rw [hV4]; positivity
  have h5 : 0 < V5 := lt_of_lt_of_le h4 h45
  simp only [List.any_eq_true] at hf
  obtain ⟨f, -, hf⟩ := hf
  simp only [foldOK, bandQ, Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hj⟩, hab⟩, b1⟩, b2⟩, b3⟩, b4⟩, b5⟩ := hf
  obtain ⟨T, N1, N2, N3, N4, hT1, hT2, hT3, hT4⟩ := hr f.j hj
  have cast : ∀ {x y : ℚ}, x ≤ y → (x : ℝ) ≤ (y : ℝ) := fun h => (Rat.cast_le (K := ℝ)).mpr h
  have b1' := cast b1; have b2' := cast b2; have b3' := cast b3; have b4' := cast b4; have b5' := cast b5
  have f1 := cast (Int.floor_le ((f.j : ℚ) / E + a * f.sa - 1 / 6))
  have f2 := cast (Int.floor_le ((0 : ℚ) + (c : ℚ) * E * f.sa - 1 / 6))
  have f3 := cast (Int.floor_le ((0 : ℚ) + ((c : ℚ) + 1) * E * f.sa - 1 / 6))
  have f4 := cast (Int.floor_le ((l : ℚ) * f.j / E + (((c : ℚ) + 1) * E + δ) * f.sa - 1 / 6))
  push_cast at b1' b2' b3' b4' b5' f1 f2 f3 f4
  have hab' : (f.sa : ℝ) ≤ f.sb := cast hab
  have e1 : ∀ x : ℝ, V1 * (x / g) = a * x := fun x => by rw [hV1]; field_simp
  have e2 : ∀ x : ℝ, V2 * (x / g) = c * E * x := fun x => by rw [hV2]; field_simp
  have e3 : ∀ x : ℝ, V3 * (x / g) = (c + 1) * E * x := fun x => by rw [hV3]; field_simp
  have e4 : ∀ x : ℝ, V4 * (x / g) = ((c + 1) * E + δ) * x := fun x => by rw [hV4]; field_simp
  refine closeF h1 h2 h3 h4 h5 (sa := (f.sa : ℝ) / g) (sb := (f.sb : ℝ) / g)
    (m1 := ⌊(f.j : ℚ) / E + a * f.sa - 1 / 6⌋) (m2 := ⌊(0 : ℚ) + (c : ℚ) * E * f.sa - 1 / 6⌋)
    (m3 := ⌊(0 : ℚ) + ((c : ℚ) + 1) * E * f.sa - 1 / 6⌋)
    (m4 := ⌊(l : ℚ) * f.j / E + (((c : ℚ) + 1) * E + δ) * f.sa - 1 / 6⌋)
    hT1 hT2 hT3 hT4 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [e1]; linarith
  · rw [e1]; linarith
  · rw [e2]; linarith
  · rw [e2]; linarith
  · rw [e3]; linarith
  · rw [e3]; linarith
  · rw [e4]; push_cast; linarith
  · rw [e4]; push_cast; linarith
  · rw [show (f.sb : ℝ) / g - f.sa / g = (f.sb - f.sa) / g by ring,
      div_le_div_iff₀ (by positivity) hg]
    have : g * ((c + 1) * E + δ) ≤ V5 := by rw [← hV4]; exact h45
    nlinarith

set_option maxHeartbeats 4000000 in
/-- **§6 with orbit modulus `E = D/g < 20` and `g ∣ v₄`** (`g = gcd(v₁, D)`; `g = 1` is coprime `D < 20`). -/
theorem s6_small {v1 v2 v3 v4 v5 c D : ℕ} (h0 : 0 < v1) (h34 : v3 < v4) (h45 : v4 < v5) (hc : 1 ≤ c)
    (hv2 : v2 = c * D) (hv3 : v3 = (c + 1) * D) (hsmall : 3 * v1 < v3) (hD0 : 0 < D) (hnd : ¬ D ∣ v1)
    (hg4 : Nat.gcd v1 D ∣ v4) (hE15 : D / Nat.gcd v1 D < 20) :
    Lonely5 v1 v2 v3 v4 v5 := by
  by_cases hw : 4 * (v2 : ℝ) * v3 ≤ v4 * (5 * v2 - v3)
  · exact s6_meeting_uniform (v5 := (v5 : ℝ)) h0 (by exact_mod_cast h45.le) hD0 hc hv2 hv3 hsmall hnd hw
  push Not at hw
  obtain ⟨g, hgdef⟩ : ∃ g, g = Nat.gcd v1 D := ⟨_, rfl⟩
  rw [← hgdef] at hg4 hE15
  have hg0 : 0 < g := hgdef ▸ Nat.gcd_pos_of_pos_right _ hD0
  obtain ⟨E, hDE⟩ : g ∣ D := hgdef ▸ Nat.gcd_dvd_right v1 D
  obtain ⟨a, ha⟩ : g ∣ v1 := hgdef ▸ Nat.gcd_dvd_left v1 D
  obtain ⟨w4, hw4⟩ := hg4
  have hcop : Nat.Coprime a E := by
    have : g * Nat.gcd a E = g * 1 := by rw [← Nat.gcd_mul_left, ← ha, ← hDE, ← hgdef, mul_one]
    exact Nat.eq_of_mul_eq_mul_left hg0 this
  have hE15' : E < 20 := by rw [hDE, Nat.mul_div_cancel_left _ hg0] at hE15; exact hE15
  have hE0 : 0 < E := by
    rcases Nat.eq_zero_or_pos E with h | h
    · rw [h, mul_zero] at hDE; omega
    · exact h
  have hE2 : 2 ≤ E := by
    by_contra h
    have h1 : E = 1 := by omega
    exact hnd ⟨a, by rw [hDE, ha, h1, mul_one]⟩
  subst ha hDE hw4 hv2 hv3
  have ha0 : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at h0)
  have hw43 : (c + 1) * E < w4 := by
    have : g * ((c + 1) * E) < g * w4 := by rw [show g * ((c + 1) * E) = (c + 1) * (g * E) by ring]; exact h34
    exact Nat.lt_of_mul_lt_mul_left this
  obtain ⟨δ, hδ⟩ : ∃ δ, w4 = (c + 1) * E + δ := ⟨w4 - (c + 1) * E, by omega⟩
  have hδ1 : 1 ≤ δ := by omega
  subst hδ
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg0
  have hER : (0 : ℝ) < E := by exact_mod_cast hE0
  have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have haR : (0 : ℝ) < a := by exact_mod_cast ha0
  have hNRr : (4 * c * δ : ℝ) < (c + 1) * E + δ := by
    have hp : (0 : ℝ) < g * g * E := by positivity
    have : ((g : ℝ) * g * E) * (4 * c * δ - ((c + 1) * E + δ)) < 0 := by push_cast at hw; linarith
    nlinarith
  have hNR : 4 * c * δ < (c + 1) * E + δ := by exact_mod_cast hNRr
  have hsm3 : 3 * a < (c + 1) * E := by
    have : g * (3 * a) < g * ((c + 1) * E) := by
      rw [show g * (3 * a) = 3 * (g * a) by ring, show g * ((c + 1) * E) = (c + 1) * (g * E) by ring]; exact hsmall
    exact Nat.lt_of_mul_lt_mul_left this
  -- the direction and the readings
  have hmodl : ∀ u, a * u % E = 1 → δ * u % E * a ≡ δ [MOD E] := by
    intro u hu
    show δ * u % E * a % E = δ % E
    rw [Nat.mod_mul_mod, show δ * u * a = δ * (a * u) by ring, Nat.mul_mod, hu, mul_one, Nat.mod_mod]
  have hread : ∀ u, a * u % E = 1 → Readings ((g * a : ℕ) : ℝ) ((c * (g * E) : ℕ) : ℝ) (((c + 1) * (g * E) : ℕ) : ℝ)
      ((g * ((c + 1) * E + δ) : ℕ) : ℝ) E (δ * u % E) := by
    intro u hu j hj
    have hl : (((c + 1) * E + δ : ℕ) : ℤ) ≡ ((δ * u % E : ℕ) : ℤ) * a [ZMOD E] := by
      rw [← Nat.cast_mul]
      apply Int.natCast_modEq_iff.mpr
      have hA : (c + 1) * E + δ ≡ δ [MOD E] := by
        show ((c + 1) * E + δ) % E = δ % E
        rw [add_comm, Nat.add_mul_mod_self_right]
      exact hA.trans (hmodl u hu).symm
    exact readings_E hg0 hcop (by omega) hj _ hl
  -- real facts
  have h1 : (0 : ℝ) < ((g * a : ℕ) : ℝ) := by push_cast; positivity
  have h2 : (0 : ℝ) < ((c * (g * E) : ℕ) : ℝ) := by push_cast; have : (0 : ℝ) < c := by linarith
                                                    positivity
  have h23 : ((c * (g * E) : ℕ) : ℝ) ≤ (((c + 1) * (g * E) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_right _ (by omega)
  have h2h : (((c + 1) * (g * E) : ℕ) : ℝ) ≤ 2 * ((c * (g * E) : ℕ) : ℝ) := by
    have : (c + 1) * (g * E) ≤ 2 * (c * (g * E)) := by nlinarith
    exact_mod_cast this
  have h13 : 3 * ((g * a : ℕ) : ℝ) < (((c + 1) * (g * E) : ℕ) : ℝ) := by exact_mod_cast hsmall
  have h34R : (((c + 1) * (g * E) : ℕ) : ℝ) ≤ ((g * ((c + 1) * E + δ) : ℕ) : ℝ) := by exact_mod_cast h34.le
  have h45R : ((g * ((c + 1) * E + δ) : ℕ) : ℝ) ≤ (v5 : ℝ) := by exact_mod_cast h45.le
  have hQe : ((g * ((c + 1) * E + δ) : ℕ) : ℝ) / (((c + 1) * (g * E) : ℕ) : ℝ) = 1 + (δ : ℝ) / ((c + 1) * E) := by
    push_cast; field_simp
  have hQUe : ((g * ((c + 1) * E + δ) : ℕ) : ℝ) / (((c + 1) * (g * E) : ℕ) : ℝ) *
      ((((c + 1) * (g * E) : ℕ) : ℝ) / ((c * (g * E) : ℕ) : ℝ)) = (1 + (δ : ℝ) / ((c + 1) * E)) * (c + 1) / c := by
    have : (0 : ℝ) < c := by linarith
    push_cast; field_simp
  rcases lt_or_ge c 5 with hc5 | hc5
  · -- c ≤ 4: the points
    have hδ24 : δ < 32 := by nlinarith
    have ha24 : a < 32 := by nlinarith
    have hs := smallAll
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at hs
    have hh : smallHyp E c δ a = true := by
      simp only [smallHyp, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨⟨⟨⟨hE2, hc⟩, hδ1⟩, hNR⟩, ha0⟩, hsm3⟩, hcop⟩
    rcases hs E hE15' c hc5 δ hδ24 a ha24 with hf | hok
    · rw [hh] at hf; exact absurd hf (by decide)
    simp only [smallOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hu, (hreg | hsum) | hfold⟩ := hok
    · refine region_sound hE0 h1 h2 h23 h2h h13 h34R h45R ?_ ?_ (hread _ hu) hreg
      · rw [hQe]; push_cast; exact le_refl _
      · rw [hQUe]; push_cast; exact le_refl _
    · refine sum_sound hE0 h1 h2 h23 h2h h34R h45R ?_ ?_ (hread _ hu) hsum
      · rw [hQe]; push_cast; ring
      · intro hda; subst hda
        constructor
        · push_cast; ring
        · push_cast; field_simp; ring
    · refine fold_sound (g := (g : ℝ)) hgR hE0 ha0 hc ?_ ?_ ?_ ?_ h45R (hread _ hu) hfold
      · push_cast; ring
      · push_cast; ring
      · push_cast; ring
      · push_cast; ring
  · -- c ≥ 5: one window per class
    obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega : 1 < E)
    have hb := bigAll
    simp only [List.all_eq_true, List.mem_range] at hb
    have hbl := hb E hE15' (δ * u % E) (Nat.mod_lt _ hE0)
    simp only [bigOK, Bool.or_eq_true, decide_eq_true_eq] at hbl
    rcases hbl with hemp | hreg
    · exfalso
      have hd : Nat.gcd (δ * u % E) E ∣ δ := by
        have h1 : Nat.gcd (δ * u % E) E ∣ Nat.gcd (δ * u % E * a) E :=
          Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_left _ _) (dvd_mul_right _ _)) (Nat.gcd_dvd_right _ _)
        rw [(hmodl u hu).gcd_eq] at h1
        exact dvd_trans h1 (Nat.gcd_dvd_left _ _)
      have := Nat.le_of_dvd (by omega) hd
      have h6 : 6 * (c + 1) * E ≤ 19 * (c + 1) * δ := by nlinarith
      nlinarith
    · refine region_sound (Qlo := 1) (QUhi := 24 / 19) hE0 h1 h2 h23 h2h h13 h34R h45R ?_ ?_ (hread _ hu) hreg
      · rw [hQe]; push_cast; have : (0 : ℝ) ≤ δ / ((c + 1) * E) := by positivity
        linarith
      · rw [hQUe]; push_cast
        have hc5R : (5 : ℝ) ≤ c := by exact_mod_cast hc5
        have hcp : (0 : ℝ) < c := by linarith
        have hδb : (δ : ℝ) * (4 * c - 1) < (c + 1) * E := by linarith
        rw [show (1 + (δ : ℝ) / ((c + 1) * E)) * (c + 1) / c = ((c + 1) * E + δ) / (c * E) by field_simp,
          div_le_iff₀ (by positivity)]
        by_contra hn
        push Not at hn
        have hm := mul_lt_mul_of_pos_left hn (show (0 : ℝ) < 4 * c - 1 by linarith)
        have hH : (0 : ℝ) ≤ (c - 5) * c * E := by
          have : (0 : ℝ) ≤ c - 5 := by linarith
          positivity
        nlinarith

/-! ### `g ∣ v₄` with `E = D/g ≥ 20`: the branch on the reduced speeds -/

/-- **§6 with `g ∣ v₄` and `E = D/g ≥ 20`.** At speeds `(v₁, …, v₄)/g` (whole numbers, `gcd(v₁/g, E) = 1`) and `v₅/g`
(real), `s6_branch` applies with `E ≥ 20`; the instant scales by `1/g`. -/
theorem s6_scaled {v1 v2 v3 v4 v5 c D : ℕ} (h0 : 0 < v1) (h34 : v3 < v4) (h45 : v4 < v5) (hc : 1 ≤ c)
    (hv2 : v2 = c * D) (hv3 : v3 = (c + 1) * D) (hsmall : 3 * v1 < v3) (hD0 : 0 < D)
    (hg4 : Nat.gcd v1 D ∣ v4) (hE20 : 20 ≤ D / Nat.gcd v1 D) :
    Lonely5 v1 v2 v3 v4 v5 := by
  obtain ⟨g, hgdef⟩ : ∃ g, g = Nat.gcd v1 D := ⟨_, rfl⟩
  rw [← hgdef] at hg4 hE20
  have hg0 : 0 < g := hgdef ▸ Nat.gcd_pos_of_pos_right _ hD0
  obtain ⟨E, hDE⟩ : g ∣ D := hgdef ▸ Nat.gcd_dvd_right v1 D
  obtain ⟨a, ha⟩ : g ∣ v1 := hgdef ▸ Nat.gcd_dvd_left v1 D
  obtain ⟨w4, hw4⟩ := hg4
  have hcop : Nat.Coprime a E := by
    have : g * Nat.gcd a E = g * 1 := by rw [← Nat.gcd_mul_left, ← ha, ← hDE, ← hgdef, mul_one]
    exact Nat.eq_of_mul_eq_mul_left hg0 this
  have hE20' : 20 ≤ E := by rw [hDE, Nat.mul_div_cancel_left _ hg0] at hE20; exact hE20
  subst ha hDE hw4 hv2 hv3
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg0
  have ha0 : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at h0)
  have h34' : (c + 1) * E < w4 := by
    have : g * ((c + 1) * E) < g * w4 := by rw [show g * ((c + 1) * E) = (c + 1) * (g * E) by ring]; exact h34
    exact Nat.lt_of_mul_lt_mul_left this
  have hsm' : 3 * a < (c + 1) * E := by
    have : g * (3 * a) < g * ((c + 1) * E) := by
      rw [show g * (3 * a) = 3 * (g * a) by ring, show g * ((c + 1) * E) = (c + 1) * (g * E) by ring]; exact hsmall
    exact Nat.lt_of_mul_lt_mul_left this
  have h45' : (w4 : ℝ) < (v5 : ℝ) / g := by
    rw [lt_div_iff₀ hgR]; have : ((g * w4 : ℕ) : ℝ) < v5 := by exact_mod_cast h45
    push_cast at this; linarith
  obtain ⟨t, a1, a2, a3, a4, a5⟩ := s6_branch (v1 := a) (v2 := c * E) (v3 := (c + 1) * E) (v4 := w4)
    (v5 := (v5 : ℝ) / g) ha0 h34' h45' hc rfl rfl hsm' hcop (by omega) (Or.inl hE20')
  have e : ∀ (k : ℕ) (x : ℝ), ((g * k : ℕ) : ℝ) * (t / g) = (k : ℝ) * t := fun k x => by push_cast; field_simp
  refine ⟨t / g, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e a 0]; exact a1
  · rw [show c * (g * E) = g * (c * E) by ring, e _ 0]; exact a2
  · rw [show (c + 1) * (g * E) = g * ((c + 1) * E) by ring, e _ 0]; exact a3
  · rw [e w4 0]; exact a4
  · rw [show (v5 : ℝ) * (t / g) = (v5 : ℝ) / g * t by ring]; exact a5

/-! ### All of §6 -/

/-- **§6 natively, every case** (`v₂ = cD`, `v₃ = (c+1)D`, `D ∤ v₁`, `3v₁ < v₃`): `g = gcd(v₁, D)`; `g ∤ v₄` by
`s6_coset`; `g ∣ v₄` with `D/g < 20` by `s6_small`; `g ∣ v₄` with `D/g ≥ 20` by `s6_scaled`. -/
theorem s6_all {v1 v2 v3 v4 v5 c D : ℕ} (h0 : 0 < v1) (h34 : v3 < v4) (h45 : v4 < v5) (hc : 1 ≤ c)
    (hv2 : v2 = c * D) (hv3 : v3 = (c + 1) * D) (hsmall : 3 * v1 < v3) (hD0 : 0 < D) (hnd : ¬ D ∣ v1) :
    Lonely5 v1 v2 v3 v4 v5 := by
  by_cases hg : Nat.gcd v1 D ∣ v4
  · rcases lt_or_ge (D / Nat.gcd v1 D) 20 with hE | hE
    · exact s6_small h0 h34 h45 hc hv2 hv3 hsmall hD0 hnd hg hE
    · exact s6_scaled h0 h34 h45 hc hv2 hv3 hsmall hD0 hg hE
  · exact s6_coset h0 h34 h45.le hc hv2 hv3 hsmall hD0 hnd hg

/-- **BHK §6 natively, in the dispatch's form** (`D = v₃ − v₂`, `D ∣ v₃`, `D ∤ v₁`, `3v₁ < v₃`). -/
theorem lonely_6_native {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3)
    (h34 : v3 < v4) (h45 : v4 < v5) (hsmall : 3 * v1 < v3) (hD3 : (v3 - v2) ∣ v3) (hD1 : ¬ (v3 - v2) ∣ v1) :
    ∃ t : ℝ, 0 < t ∧ LRC.OrderSixN.Lonely6 v1 v2 v3 v4 v5 t := by
  set D := v3 - v2 with hDdef
  obtain ⟨e, he⟩ := hD3
  have he2 : 2 ≤ e := by
    rcases Nat.lt_or_ge e 2 with h | h
    · interval_cases e <;> omega
    · exact h
  have hv3 : v3 = ((e - 1) + 1) * D := by rw [Nat.sub_add_cancel (by omega)]; rw [he]; ring
  have hv2 : v2 = (e - 1) * D := by
    have : v2 = v3 - D := by omega
    rw [this, hv3]; rw [Nat.add_mul, one_mul]; omega
  obtain ⟨s, a1, a2, a3, a4, a5⟩ :=
    s6_all h0 h34 h45 (show 1 ≤ e - 1 by omega) hv2 hv3 hsmall (by omega) hD1
  obtain ⟨m, hm⟩ := exists_nat_gt (-s)
  have key : ∀ v : ℕ, circDist ((v : ℝ) * (s + ((m + 1 : ℕ) : ℝ))) = circDist ((v : ℝ) * s) := by
    intro v
    have e' : (v : ℝ) * (s + ((m + 1 : ℕ) : ℝ)) = (v : ℝ) * s + ((v * (m + 1) : ℕ) : ℤ) := by push_cast; ring
    rw [e', s8_circDist_add_int]
  refine ⟨s + ((m + 1 : ℕ) : ℝ), by push_cast; linarith, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [key, one_div] <;> assumption

end LRC.S6Native
