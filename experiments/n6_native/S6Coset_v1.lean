import LonelyRunner.LRC.Spec.OrderSixSixNativeN

/-!
# §6, runner 1's orbit coarse and runner 4 off it: g = gcd(v₁, D) ∤ v₄ (n6_native, E101–E102)

At the meeting times `k = k₀ + (D/g)·i` runner 1's phase does not move (`v₁·(D/g) = (v₁/g)·D`), while runner 4's moves by
`v₄/g` per step. With `i` from Bézout (`v₄ i ≡ d = gcd(v₄, g) mod g`, `d < g`, so `d ≤ g/2`) the step is `d/g ≤ 1/2`
mod 1, and a progression with step at most `1/2` meets every closed half arc (`step_meets_half_arc`). Runner 4's usable
arc after the meeting time is at least a half arc (as in `s6_generic`), so `s6_window_fold` closes it. No bound on `D`.
-/

namespace LRC.S6Native
open LRC.S7Native LRC.S8Native

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

end LRC.S6Native

#print axioms LRC.S6Native.step_meets_half_arc
#print axioms LRC.S6Native.s6_coset
