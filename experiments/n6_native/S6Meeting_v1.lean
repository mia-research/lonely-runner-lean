import LonelyRunner.LRC.Spec.OrderSixEightNativeN

/-!
# BHK §6 by meeting windows (n6_native, E92)

§6: `v₃ = c D`, `v₂ = (c − 1) D` (`D = v₃ − v₂`), `D ∤ v₁`, `3 v₁ < v₃`. At the meeting time `k/D` runners 2 and 3 are both
on the subject; just after it they are clear together on `[k/D + 1/(6v₂), k/D + 5/(6v₃)]` (`meeting_pair_clear`).
Runner 1 reads `(k v₁ mod D)/D` at `k/D`; the orbit `k v₁ mod D` contains every multiple of `g = gcd(v₁, D) < D`, so some
`k` puts that residue in `[D/6, 5D/9]` (`orbit_residue`), and then runner 1 is clear across the whole window
(`3 v₁ < v₃`). Runners 4, 5 by `window_two_uniform` when the window is at least `2/(3 v₄)` (`s6_meeting_uniform`).
-/

namespace N6Native
open LRC.S7Native

/-- **The orbit of `v₁` mod `D` reaches `[D/6, 5D/9]`** when `D ∤ v₁`. -/
theorem orbit_residue (v1 D : ℕ) (hD : 0 < D) (hnd : ¬ D ∣ v1) :
    ∃ k : ℕ, D ≤ 6 * (v1 * k % D) ∧ 9 * (v1 * k % D) ≤ 5 * D := by
  set g := Nat.gcd v1 D with hg
  have hgD : g ∣ D := Nat.gcd_dvd_right v1 D
  have hgv : g ∣ v1 := Nat.gcd_dvd_left v1 D
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ hD
  have hglt : g < D := by
    rcases lt_or_eq_of_le (Nat.le_of_dvd hD hgD) with h | h
    · exact h
    · exact absurd (h ▸ hgv) hnd
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_gcd (k := D) (n := v1) hglt
  obtain ⟨e, he⟩ := hgD
  by_cases hsmall : 18 * g ≤ 7 * D
  · set q := D / (6 * g) + 1 with hq
    have hq1 : D < 6 * g * q := by rw [hq]; exact Nat.lt_mul_div_succ D (by omega)
    have hq2 : 6 * g * q ≤ D + 6 * g := by
      have := Nat.mul_div_le D (6 * g); rw [hq]; nlinarith
    have hqg : q * g < D := by nlinarith
    have e1 : v1 * (q * m) % D = q * g := by
      have : v1 * (q * m) % D = (q * g) % D := by
        rw [show v1 * (q * m) = q * (v1 * m) by ring, Nat.mul_mod, hm, ← hg]
        conv_rhs => rw [Nat.mul_mod, Nat.mod_eq_of_lt hglt]
      rw [this, Nat.mod_eq_of_lt hqg]
    refine ⟨q * m, ?_, ?_⟩ <;> rw [e1] <;> nlinarith
  · push Not at hsmall
    have he2 : e = 2 := by
      have : 2 ≤ e := by
        rcases Nat.lt_or_ge e 2 with h | h
        · interval_cases e <;> (simp at he; omega)
        · exact h
      by_contra hne
      have : 3 ≤ e := by omega
      nlinarith
    subst he2
    refine ⟨m, ?_, ?_⟩ <;> rw [hm] <;> omega

set_option maxHeartbeats 1000000 in
/-- **§6 by the meeting window, uniform case.** With `v₂ = c D`, `v₃ = (c+1) D` (`c ≥ 1`), `D ∤ v₁`, `3 v₁ < v₃` and
`4 v₂ v₃ ≤ v₄ (5 v₂ − v₃)` (the window `[k/D + 1/(6v₂), k/D + 5/(6v₃)]` is at least `2/(3v₄)`), some instant is lonely. -/
theorem s6_meeting_uniform {v1 v2 v3 v4 v5 c D : ℕ} (h0 : 0 < v1) (h45 : v4 ≤ v5) (hD : 0 < D) (hc : 1 ≤ c)
    (hv2 : v2 = c * D) (hv3 : v3 = (c + 1) * D) (hsmall : 3 * v1 < v3) (hnd : ¬ D ∣ v1)
    (hw : 4 * (v2 : ℝ) * v3 ≤ v4 * (5 * v2 - v3)) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  obtain ⟨k, hk1, hk2⟩ := orbit_residue v1 D hD hnd
  set r := v1 * k % D with hr
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hv2R : (v2 : ℝ) = c * D := by rw [hv2]; push_cast; ring
  have hv3R : (v3 : ℝ) = (c + 1) * D := by rw [hv3]; push_cast; ring
  have h2p : (0 : ℝ) < v2 := by rw [hv2R]; positivity
  have h3p : (0 : ℝ) < v3 := by rw [hv3R]; positivity
  have h23 : (v2 : ℝ) < v3 := by rw [hv2R, hv3R]; nlinarith
  have h1p : (0 : ℝ) < v1 := by exact_mod_cast h0
  have h13 : 3 * (v1 : ℝ) < v3 := by exact_mod_cast hsmall
  have h4p : (0 : ℝ) < v4 := by
    have : (0 : ℝ) < 5 * v2 - v3 := by rw [hv2R, hv3R]; nlinarith
    by_contra hc4; push Not at hc4; nlinarith [mul_pos h2p h3p]
  have h45R : (v4 : ℝ) ≤ v5 := by exact_mod_cast h45
  set J₀ : ℝ := (k : ℝ) / D + 1 / (6 * v2) with hJ
  set ℓ : ℝ := 5 / (6 * v3) - 1 / (6 * v2) with hℓ
  have hlen : 2 / (3 * (v4 : ℝ)) ≤ ℓ := by
    rw [hℓ, div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  obtain ⟨t, ht1, ht2, c4, c5⟩ := window_two_uniform (J₀ := J₀) h4p h45R hlen
  set s := t - (k : ℝ) / D with hs
  have hs1 : 1 / (6 * (v2 : ℝ)) ≤ s := by rw [hs]; linarith
  have hs2 : s ≤ 5 / (6 * (v3 : ℝ)) := by rw [hs]; linarith
  have hs0 : 0 ≤ s := le_trans (by positivity) hs1
  have a2 : (1 : ℝ) / 6 ≤ v2 * s := by rw [div_le_iff₀ (by positivity)] at hs1; linarith
  have b3 : (v3 : ℝ) * s ≤ 5 / 6 := by rw [le_div_iff₀ (by positivity)] at hs2; linarith
  have b2 : (v2 : ℝ) * s ≤ 5 / 6 := by nlinarith
  have a3 : (1 : ℝ) / 6 ≤ v3 * s := by nlinarith
  have b1 : (v1 : ℝ) * s ≤ 5 / 18 := by nlinarith
  have ht : t = (k : ℝ) / D + s := by rw [hs]; ring
  -- runner 1: v1 t = ⌊v1 k / D⌋ + r/D + v1 s
  have hdm : ((v1 * k : ℕ) : ℝ) = D * ((v1 * k / D : ℕ) : ℝ) + (r : ℝ) := by
    exact_mod_cast (Nat.div_add_mod (v1 * k) D).symm
  have hk1R : (D : ℝ) ≤ 6 * r := by exact_mod_cast hk1
  have hk2R : 9 * (r : ℝ) ≤ 5 * D := by exact_mod_cast hk2
  have e0 : ((v1 : ℝ) * k) / D = ((v1 * k / D : ℕ) : ℝ) + (r : ℝ) / D := by
    rw [show ((v1 : ℝ) * k) = ((v1 * k : ℕ) : ℝ) by push_cast; ring, hdm]; field_simp
  have e1 : (v1 : ℝ) * t = (((v1 * k / D : ℕ) : ℤ) : ℝ) + ((r : ℝ) / D + v1 * s) := by
    rw [ht, mul_add, show (v1 : ℝ) * ((k : ℝ) / D) = ((v1 : ℝ) * k) / D by ring, e0, Int.cast_natCast]; ring
  have rD1 : (1 : ℝ) / 6 ≤ (r : ℝ) / D := by rw [le_div_iff₀ hDR]; linarith
  have rD2 : (r : ℝ) / D ≤ 5 / 9 := by rw [div_le_iff₀ hDR]; linarith
  have e2 : (v2 : ℝ) * t = (((c * k : ℕ) : ℤ) : ℝ) + v2 * s := by
    rw [ht, mul_add, hv2R]; push_cast; field_simp
  have e3 : (v3 : ℝ) * t = ((((c + 1) * k : ℕ) : ℤ) : ℝ) + v3 * s := by
    rw [ht, mul_add, hv3R]; push_cast; field_simp
  refine ⟨t, ?_, ?_, ?_, c4, c5⟩
  · have v1s0 : (0 : ℝ) ≤ v1 * s := by positivity
    rw [e1]; apply clear_of_band (p := ((v1 * k / D : ℕ) : ℤ)) <;> linarith
  · rw [e2]; apply clear_of_band (p := ((c * k : ℕ) : ℤ)) <;> linarith
  · rw [e3]; apply clear_of_band (p := (((c + 1) * k : ℕ) : ℤ)) <;> linarith

/-- **§5's pair window (M5).** Runners 2 and 3 on one lap `j ≥ 0` are clear together on `[(j+1/6)/v₂, (j+5/6)/v₃]`; if
runner 1 on lap `m` is clear on a sub-window `[a, b]` of it of length at least `2/(3 v₄)`, runners 4 and 5 are folded by
`window_two_uniform`. -/
theorem s5_pair_window {v1 v2 v3 v4 v5 a b : ℝ} {j m : ℤ} (hj : 0 ≤ j) (h1 : 0 < v1) (h2 : 0 < v2) (h23 : v2 ≤ v3)
    (h4 : 0 < v4) (h45 : v4 ≤ v5)
    (ha2 : ((j : ℝ) + 1 / 6) / v2 ≤ a) (hb3 : b ≤ ((j : ℝ) + 5 / 6) / v3)
    (ha1 : ((m : ℝ) + 1 / 6) / v1 ≤ a) (hb1 : b ≤ ((m : ℝ) + 5 / 6) / v1)
    (hlen : 2 / (3 * v4) ≤ b - a) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have h3 : 0 < v3 := lt_of_lt_of_le h2 h23
  have hjR : (0 : ℝ) ≤ j := by exact_mod_cast hj
  obtain ⟨t, ht1, ht2, c4, c5⟩ := window_two_uniform (J₀ := a) (ℓ := b - a) h4 h45 hlen
  have htb : t ≤ b := by linarith
  rw [div_le_iff₀ h2] at ha2; rw [le_div_iff₀ h3] at hb3
  rw [div_le_iff₀ h1] at ha1; rw [le_div_iff₀ h1] at hb1
  have ht0 : 0 ≤ t := by nlinarith
  refine ⟨t, ?_, ?_, ?_, c4, c5⟩
  · apply clear_of_band (p := m) <;> nlinarith
  · apply clear_of_band (p := j) <;> nlinarith
  · apply clear_of_band (p := j) <;> nlinarith

end N6Native

#print axioms N6Native.orbit_residue
#print axioms N6Native.s6_meeting_uniform
#print axioms N6Native.s5_pair_window
