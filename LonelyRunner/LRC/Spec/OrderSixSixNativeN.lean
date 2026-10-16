import LonelyRunner.LRC.Spec.OrderSixEightNativeN

/-!
# BHK §6 natively, the branch D ≥ 15 with runner 1's orbit coprime (gcd(v₁, D) = 1)

Moved into the tree 2026-10-16 from `experiments/n6_native/S6Branch_v1.lean` (log E92–E100). `lonely_6_native_branch`
is used by `lonely6_of_lt` when `D = v₃ − v₂ ≥ 15` and `gcd(v₁, D) = 1`; otherwise BHK's `lonely_6`.

Collects `S6Meeting_v1`, `S6Generic_v1`, `S6Sum_v1` and adds the mirror window, the sum lemma on whole numbers, and
the branch theorem for directions other than ±1.
-/

namespace LRC.S6Native
open LRC.S7Native LRC.S8Native

/-! ### from `S6Meeting_v1.lean` -/

/-!
# BHK §6 by meeting windows (n6_native, E92)

§6: `v₃ = c D`, `v₂ = (c − 1) D` (`D = v₃ − v₂`), `D ∤ v₁`, `3 v₁ < v₃`. At the meeting time `k/D` runners 2 and 3 are both
on the subject; just after it they are clear together on `[k/D + 1/(6v₂), k/D + 5/(6v₃)]` (`meeting_pair_clear`).
Runner 1 reads `(k v₁ mod D)/D` at `k/D`; the orbit `k v₁ mod D` contains every multiple of `g = gcd(v₁, D) < D`, so some
`k` puts that residue in `[D/6, 5D/9]` (`orbit_residue`), and then runner 1 is clear across the whole window
(`3 v₁ < v₃`). Runners 4, 5 by `window_two_uniform` when the window is at least `2/(3 v₄)` (`s6_meeting_uniform`).
-/


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


/-! ### from `S6Generic_v1.lean` -/

/-!
# §6 near-runner, generic orbits (n6_native, E95)

At the meeting times `k/D` the phases of runners 1 and 4 are `(k v₁ mod D)/D` and `(k δ mod D)/D`, `δ = v₄ − v₃`. With
`gcd(v₁, D) = 1` put `j = k v₁ mod D`; then runner 4's phase is `λ j / D` mod 1, `λ ≡ δ v₁⁻¹`. For `j` over the integers of
`[D/6, 5D/9]` (runner 1 clear across the window) the points `λ j / D` form a progression with step `|λ|/D ≤ 1/2`; when
`|λ| ≥ 2` and `D ≥ 15` its span exceeds `1/2`, so it meets every closed half arc (`ap_meets_half_arc`).
-/


/-- Two reals in upper halves of unit intervals, at most `1/2` apart, lie in the same unit interval. -/
theorem floor_eq_of_upper {y z : ℝ} (hy : (⌊y⌋ : ℝ) + 1 / 2 < y) (hz : (⌊z⌋ : ℝ) + 1 / 2 < z)
    (h : |z - y| ≤ 1 / 2) : ⌊z⌋ = ⌊y⌋ := by
  have hy1 := Int.lt_floor_add_one y
  have hz1 := Int.lt_floor_add_one z
  rw [abs_le] at h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have : (⌊z⌋ : ℝ) + 1 ≤ ⌊y⌋ := by exact_mod_cast hlt
    linarith
  · have : (⌊y⌋ : ℝ) + 1 ≤ ⌊z⌋ := by exact_mod_cast hgt
    linarith

/-- **The progression meets every half arc.** For `D ≥ 15`, `2 ≤ |λ|`, `2|λ| ≤ D` and any `x₀`, some integer
`j ∈ [D/6, 5D/9]` has `λ j / D − x₀` within `[m, m + 1/2]` for an integer `m`. -/
theorem ap_meets_half_arc (D : ℕ) (l : ℤ) (hD : 15 ≤ D) (hl : 2 ≤ |l|) (hl2 : 2 * |l| ≤ D) (x₀ : ℝ) :
    ∃ j : ℕ, D ≤ 6 * j ∧ 9 * j ≤ 5 * D ∧ ∃ m : ℤ, (m : ℝ) ≤ l * j / D - x₀ ∧ l * j / D - x₀ ≤ m + 1 / 2 := by
  by_contra hcon
  push Not at hcon
  have hDR : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  set z : ℕ → ℝ := fun j => l * j / D - x₀ with hz
  set j₀ := (D + 5) / 6 with hj0
  set j₁ := 5 * D / 9 with hj1
  have hj0a : D ≤ 6 * j₀ := by omega
  have hj1a : 9 * j₁ ≤ 5 * D := by omega
  have hj01 : j₀ ≤ j₁ := by omega
  -- every z_j in range is in an upper half
  have upper : ∀ j, D ≤ 6 * j → 9 * j ≤ 5 * D → (⌊z j⌋ : ℝ) + 1 / 2 < z j := by
    intro j h1 h2
    have := hcon j h1 h2 ⌊z j⌋ (Int.floor_le _)
    exact this
  have step : ∀ j, |z (j + 1) - z j| ≤ 1 / 2 := by
    intro j
    have e : z (j + 1) - z j = l / D := by simp only [hz]; push_cast; ring
    rw [e, abs_div, abs_of_pos hDR, div_le_iff₀ hDR]
    have : (2 * |l| : ℝ) ≤ D := by exact_mod_cast hl2
    have h' : ((|l| : ℤ) : ℝ) = |(l : ℝ)| := by push_cast; rfl
    rw [← h']; linarith
  have const : ∀ j, j₀ ≤ j → j ≤ j₁ → ⌊z j⌋ = ⌊z j₀⌋ := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; rfl
    | succ j hj ih =>
      intro hj1'
      rw [← ih (by omega)]
      exact floor_eq_of_upper (upper j (by omega) (by omega)) (upper (j + 1) (by omega) (by omega)) (step j)
  have u0 := upper j₀ hj0a (by omega)
  have u1 := upper j₁ (by omega) hj1a
  have f1 := const j₁ hj01 le_rfl
  have hy1 := Int.lt_floor_add_one (z j₀)
  have hz1 := Int.lt_floor_add_one (z j₁)
  rw [f1] at u1 hz1
  -- |z j₁ - z j₀| < 1/2, but the span is at least 1/2
  have span : (1 : ℝ) / 2 ≤ |z j₁ - z j₀| := by
    have e : z j₁ - z j₀ = l * ((j₁ : ℝ) - j₀) / D := by simp only [hz]; ring
    rw [e, abs_div, abs_mul, abs_of_pos hDR, abs_of_nonneg (show (0 : ℝ) ≤ (j₁ : ℝ) - j₀ by have h' : (j₀ : ℝ) ≤ j₁ := (by exact_mod_cast hj01); linarith)]
    rw [le_div_iff₀ hDR]
    have hlR : (2 : ℝ) ≤ |(l : ℝ)| := by
      have : ((2 : ℤ) : ℝ) ≤ ((|l| : ℤ) : ℝ) := by exact_mod_cast hl
      push_cast at this; exact this
    have hd : (7 : ℝ) * D ≤ 18 * ((j₁ : ℝ) - j₀) + 33 := by
      have a : (D : ℝ) ≤ 6 * j₀ := by exact_mod_cast hj0a
      have b : 6 * (j₀ : ℝ) ≤ D + 5 := by exact_mod_cast (show 6 * j₀ ≤ D + 5 by omega)
      have c : 5 * (D : ℝ) ≤ 9 * j₁ + 8 := by exact_mod_cast (show 5 * D ≤ 9 * j₁ + 8 by omega)
      linarith
    have hD15 : (15 : ℝ) ≤ D := by exact_mod_cast hD
    have hjj : (0 : ℝ) ≤ (j₁ : ℝ) - j₀ := by have h' : (j₀ : ℝ) ≤ j₁ := (by exact_mod_cast hj01); linarith
    have := mul_le_mul_of_nonneg_right hlR hjj
    nlinarith
  have close : |z j₁ - z j₀| < 1 / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
  linarith


set_option maxHeartbeats 1000000 in
/-- **The fold at a meeting window, from the phases.** `v₂ = cD`, `v₃ = (c+1)D`, `3v₁ < v₃`, `v₃ ≤ v₄ ≤ v₅`. At the
meeting time `T = k/D` runners 2, 3 are on the subject, runner 1 reads `p₁ ∈ [1/6, 5/9]` past a whole lap, runner 4 reads
`p₄` past one; on the window `s ∈ [s₀, s₁] = [1/(6v₂), 5/(6v₃)]` runner 4 sweeps `[x, x + v₄ℓ]`, `x = p₄ + v₄ s₀`. If that
sweep meets the band `[m + 1/6, m + 5/6]` in a stretch of length at least `v₄/(3v₅)`, the arrangement is lonely. -/
theorem s6_window_fold {v1 v2 v3 v4 v5 D T p1 p4 : ℝ} {N2 N3 N1 N4 m : ℤ} (h1 : 0 < v1) (hD : 0 < D)
    (h2 : 0 < v2) (h23 : v2 ≤ v3) (h13 : 3 * v1 < v3) (h34 : v3 ≤ v4) (h45 : v4 ≤ v5)
    (hT2 : v2 * T = N2) (hT3 : v3 * T = N3) (hT1 : v1 * T = N1 + p1) (hT4 : v4 * T = N4 + p4)
    (hp1a : 1 / 6 ≤ p1) (hp1b : p1 ≤ 5 / 9)
    (hlo : (m : ℝ) + 1 / 6 - v4 * (5 / (6 * v3) - 1 / (6 * v2)) + v4 / (3 * v5) ≤ p4 + v4 / (6 * v2))
    (hhi : p4 + v4 / (6 * v2) ≤ (m : ℝ) + 5 / 6 - v4 / (3 * v5))
    (hlam : v4 / (3 * v5) ≤ v4 * (5 / (6 * v3) - 1 / (6 * v2))) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have h3 : 0 < v3 := lt_of_lt_of_le h2 h23
  have h4 : 0 < v4 := lt_of_lt_of_le h3 h34
  have h5 : 0 < v5 := lt_of_lt_of_le h4 h45
  set s0 := 1 / (6 * v2) with hs0
  set s1 := 5 / (6 * v3) with hs1
  set x := p4 + v4 * s0 with hx
  set μ := v4 / (3 * v5) with hμ
  have e0 : v4 / (6 * v2) = v4 * s0 := by rw [hs0]; ring
  rw [e0] at hlo hhi
  have hμ0 : 0 < μ := by positivity
  have hμ3 : μ ≤ 1 / 3 := by rw [hμ, div_le_iff₀ (by positivity)]; linarith
  -- the stretch of runner 4's sweep inside its band, in reading units
  set ya := max x ((m : ℝ) + 1 / 6) with hya
  set yb := min (x + v4 * (s1 - s0)) ((m : ℝ) + 5 / 6) with hyb
  have hyab : μ ≤ yb - ya := by
    rw [hya, hyb]
    rcases le_total x ((m : ℝ) + 1 / 6) with hx1 | hx1 <;>
    rcases le_total (x + v4 * (s1 - s0)) ((m : ℝ) + 5 / 6) with hx2 | hx2 <;>
    simp only [max_eq_left, max_eq_right, min_eq_left, min_eq_right, hx1, hx2] <;> linarith
  -- the time window [T + sa, T + sb]
  set sa := s0 + (ya - x) / v4 with hsa
  set sb := s0 + (yb - x) / v4 with hsb
  have hxa : x ≤ ya := le_max_left _ _
  have hyb2 : yb ≤ x + v4 * (s1 - s0) := min_le_left _ _
  have hsa0 : s0 ≤ sa := by rw [hsa]; have : 0 ≤ (ya - x) / v4 := div_nonneg (by linarith) h4.le; linarith
  have hsb1 : sb ≤ s1 := by
    rw [hsb]; have : (yb - x) / v4 ≤ s1 - s0 := by rw [div_le_iff₀ h4]; linarith
    linarith
  have hlen : 1 / (3 * v5) ≤ sb - sa := by
    rw [hsa, hsb, show s0 + (yb - x) / v4 - (s0 + (ya - x) / v4) = (yb - ya) / v4 by ring,
      le_div_iff₀ h4]
    have : 1 / (3 * v5) * v4 = μ := by rw [hμ]; ring
    linarith
  obtain ⟨t', ht1, ht2, c5⟩ := fold_one (J₀ := T + sa) (ℓ := sb - sa) h5 hlen
  set s := t' - T with hs
  have hss : sa ≤ s ∧ s ≤ sb := ⟨by rw [hs]; linarith, by rw [hs]; linarith⟩
  have hs0s : s0 ≤ s := le_trans hsa0 hss.1
  have hss1 : s ≤ s1 := le_trans hss.2 hsb1
  have ht : t' = T + s := by rw [hs]; ring
  have hs0p : 0 < s0 := by positivity
  refine ⟨t', ?_, ?_, ?_, ?_, c5⟩
  · -- runner 1: p1 + v1 s ∈ [1/6, 5/6]
    have : v1 * s ≤ 5 / 18 := by
      have : v1 * s ≤ v1 * s1 := mul_le_mul_of_nonneg_left hss1 h1.le
      have : v1 * s1 < 5 / 18 := by rw [hs1]; rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
      linarith
    have : 0 ≤ v1 * s := mul_nonneg h1.le (by linarith)
    rw [ht, mul_add, hT1]; apply clear_of_band (p := N1) <;> linarith
  · have a : 1 / 6 ≤ v2 * s := by rw [hs0] at hs0s; rw [div_le_iff₀ (by positivity)] at hs0s; linarith
    have b : v2 * s ≤ 5 / 6 := by
      have : v2 * s ≤ v3 * s := mul_le_mul_of_nonneg_right h23 (by linarith)
      rw [hs1] at hss1; rw [le_div_iff₀ (by positivity)] at hss1; linarith
    rw [ht, mul_add, hT2]; apply clear_of_band (p := N2) <;> linarith
  · have a : 1 / 6 ≤ v3 * s := by
      have : v2 * s ≤ v3 * s := mul_le_mul_of_nonneg_right h23 (by linarith)
      rw [hs0] at hs0s; rw [div_le_iff₀ (by positivity)] at hs0s; linarith
    have b : v3 * s ≤ 5 / 6 := by rw [hs1] at hss1; rw [le_div_iff₀ (by positivity)] at hss1; linarith
    rw [ht, mul_add, hT3]; apply clear_of_band (p := N3) <;> linarith
  · -- runner 4: reading N4 + p4 + v4 s = N4 + x + v4 (s - s0) ∈ [ya, yb] ⊆ [m + 1/6, m + 5/6]
    have r1 : ya ≤ x + v4 * (s - s0) := by
      have : (ya - x) / v4 ≤ s - s0 := by rw [hsa] at hss; linarith [hss.1]
      rw [div_le_iff₀ h4] at this; linarith
    have r2 : x + v4 * (s - s0) ≤ yb := by
      have : s - s0 ≤ (yb - x) / v4 := by rw [hsb] at hss; linarith [hss.2]
      rw [le_div_iff₀ h4] at this; linarith
    have r3 : (m : ℝ) + 1 / 6 ≤ ya := le_max_right _ _
    have r4 : yb ≤ (m : ℝ) + 5 / 6 := min_le_right _ _
    rw [ht, mul_add, hT4]; apply clear_of_band (p := N4 + m)
    · push_cast; rw [hx] at r1; linarith
    · push_cast; rw [hx] at r2; linarith

set_option maxHeartbeats 1000000 in
/-- **§6, generic orbits.** `v₂ = cD`, `v₃ = (c+1)D` (`c ≥ 1`), `3v₁ < v₃`, `v₃ < v₄ ≤ v₅`, `gcd(v₁, D) = 1`, `D ≥ 15`, and
the orbit direction `λ` (`v₄ ≡ λ v₁ mod D`, equivalently `δ = v₄ − v₃ ≡ λ v₁`) with `2 ≤ |λ|`, `2|λ| ≤ D`: some instant is
lonely. The meeting time `k/D` is chosen with `k v₁ ≡ j` for the `j ∈ [D/6, 5D/9]` given by `ap_meets_half_arc`. -/
theorem s6_generic {v1 v2 v3 v4 v5 c D : ℕ} (h0 : 0 < v1) (h34 : v3 < v4) (h45 : v4 ≤ v5) (hc : 1 ≤ c)
    (hv2 : v2 = c * D) (hv3 : v3 = (c + 1) * D) (hsmall : 3 * v1 < v3) (hcop : Nat.Coprime v1 D) (hD : 15 ≤ D)
    (l : ℤ) (hl : (v4 : ℤ) ≡ l * v1 [ZMOD D]) (hl1 : 2 ≤ |l|) (hl2 : 2 * |l| ≤ D) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have hD0 : 0 < D := by omega
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD0
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
  -- the half arc and j
  obtain ⟨j, hj1, hj2, m, hm1, hm2⟩ :=
    ap_meets_half_arc D l hD hl1 hl2 (1 / 6 - lam + μ - v4 * s0)
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (show 1 < D by omega)
  set k := j * u with hk
  -- readings at T = k/D
  have hjD : j < D := by omega
  have hv1k : v1 * k % D = j := by
    rw [hk, show v1 * (j * u) = j * (v1 * u) by ring, Nat.mul_mod, hu, mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hjD]
  set q1 := v1 * k / D with hq1
  have hdiv1 : v1 * k = D * q1 + j := by rw [hq1, ← hv1k]; exact (Nat.div_add_mod _ _).symm
  have hmod4 : (v4 * k : ℤ) ≡ l * j [ZMOD D] := by
    have a : (v4 * k : ℤ) ≡ l * v1 * k [ZMOD D] := Int.ModEq.mul_right _ hl
    have b : (l * v1 * k : ℤ) = l * (D * q1) + l * j := by
      have : ((v1 * k : ℕ) : ℤ) = ((D * q1 + j : ℕ) : ℤ) := by rw [hdiv1]
      push_cast at this; rw [mul_assoc, this]; ring
    rw [b] at a
    refine a.trans ?_
    have : (l * (D * q1) + l * j : ℤ) ≡ 0 + l * j [ZMOD D] :=
      Int.ModEq.add_right _ (Int.modEq_zero_iff_dvd.mpr ⟨l * q1, by ring⟩)
    simpa using this
  obtain ⟨q4, hq4⟩ := hmod4.symm.dvd
  set T : ℝ := (k : ℝ) / D with hT
  have hT2 : (v2 : ℝ) * T = ((c * k : ℕ) : ℤ) := by rw [hT, hv2R]; push_cast; field_simp
  have hT3 : (v3 : ℝ) * T = (((c + 1) * k : ℕ) : ℤ) := by rw [hT, hv3R]; push_cast; field_simp
  have hT1 : (v1 : ℝ) * T = ((q1 : ℕ) : ℤ) + (j : ℝ) / D := by
    have : ((v1 * k : ℕ) : ℝ) = D * q1 + j := by exact_mod_cast hdiv1
    rw [hT]; push_cast at this ⊢; field_simp; linarith
  have hT4 : (v4 : ℝ) * T = (q4 : ℤ) + (l : ℝ) * j / D := by
    have h' : (v4 * k : ℤ) = l * j + D * q4 := by linarith [hq4]
    have : ((v4 * k : ℤ) : ℝ) = ((l * j + D * q4 : ℤ) : ℝ) := by rw [h']
    push_cast at this
    rw [hT]; field_simp; linarith
  have hp1a : (1 : ℝ) / 6 ≤ (j : ℝ) / D := by
    rw [le_div_iff₀ hDR]; have : (D : ℝ) ≤ 6 * j := by exact_mod_cast hj1
    linarith
  have hp1b : (j : ℝ) / D ≤ 5 / 9 := by
    rw [div_le_iff₀ hDR]; have : 9 * (j : ℝ) ≤ 5 * D := by exact_mod_cast hj2
    linarith
  have hx : (v4 : ℝ) / (6 * v2) = v4 * s0 := by rw [hs0]; ring
  refine s6_window_fold (m := m) h1p hDR h2p h23 h13 h34R h45R hT2 hT3 hT1 hT4 hp1a hp1b ?_ ?_ ?_
  · rw [hx]; linarith
  · rw [hx]; linarith
  · linarith


/-! ### from `S6Sum_v1.lean` -/

/-!
# §6 with the sum relation `v₄ = v₃ + v₁` (n6_native, E97)

At a meeting time `T = k/D` runners 2, 3 are on the subject and runner 4 reads what runner 1 reads, `p` (because
`v₄ T = v₃ T + v₁ T`). After `T`, on the instants where runner 3 reads `x₃ ∈ [7/6 − p, 5/6]`: runner 4 reads `x₃ + p + v₁s`,
one lap on and in the band; runner 1 reads `p + v₁ s ≤ 5/6` when `p ≤ (5/6)(1 − v₁/v₃)`; runner 2 reads `x₃ · v₂/v₃ ≥ x₃/2`;
and runner 5 is folded when the stretch `(p − 1/3)/v₃` is at least `1/(3v₅)`.
-/


set_option maxHeartbeats 1000000 in
theorem s6_sum_window {v1 v2 v3 v5 T p : ℝ} {N1 N2 N3 : ℤ} (h1 : 0 < v1) (h2 : 0 < v2) (h23 : v2 ≤ v3)
    (h2half : v3 ≤ 2 * v2) (h5 : 0 < v5)
    (hT1 : v1 * T = N1 + p) (hT2 : v2 * T = N2) (hT3 : v3 * T = N3)
    (hplo : 1 / 3 + v3 / (3 * v5) ≤ p) (hphi : p ≤ 5 / 6 * (1 - v1 / v3)) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist ((v3 + v1) * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have h3 : 0 < v3 := lt_of_lt_of_le h2 h23
  have hr : v1 / v3 * v3 = v1 := by field_simp
  -- the stretch: s ∈ [(7/6 - p)/v3, 5/(6 v3)]
  have hlen : 1 / (3 * v5) ≤ 5 / (6 * v3) - (7 / 6 - p) / v3 := by
    have e : 5 / (6 * v3) - (7 / 6 - p) / v3 = (p - 1 / 3) / v3 := by field_simp; ring
    rw [e, div_le_div_iff₀ (by positivity) h3]
    have : v3 / (3 * v5) * (3 * v5) = v3 := by field_simp
    nlinarith
  obtain ⟨t', ht1, ht2, c5⟩ := LRC.S8Native.fold_one (J₀ := T + (7 / 6 - p) / v3)
    (ℓ := 5 / (6 * v3) - (7 / 6 - p) / v3) h5 hlen
  set s := t' - T with hs
  have hsa : (7 / 6 - p) / v3 ≤ s := by rw [hs]; linarith
  have hsb : s ≤ 5 / (6 * v3) := by rw [hs]; linarith
  have x3a : 7 / 6 - p ≤ v3 * s := by rw [div_le_iff₀ h3] at hsa; linarith
  have x3b : v3 * s ≤ 5 / 6 := by rw [le_div_iff₀ (by positivity)] at hsb; linarith
  have hp56 : p ≤ 5 / 6 := by
    have : 0 ≤ v1 / v3 := by positivity
    nlinarith
  have hs0 : 0 ≤ s := by
    have : 0 ≤ (7 / 6 - p) / v3 := div_nonneg (by linarith) h3.le
    linarith
  have x1b : v1 * s ≤ 5 / 6 * (v1 / v3) := by
    have : v1 * s = v1 / v3 * (v3 * s) := by field_simp
    rw [this]; have : 0 ≤ v1 / v3 := by positivity
    nlinarith
  have x1a : 0 ≤ v1 * s := mul_nonneg h1.le hs0
  have ht : t' = T + s := by rw [hs]; ring
  refine ⟨t', ?_, ?_, ?_, ?_, c5⟩
  · rw [ht, mul_add, hT1]; apply clear_of_band (p := N1) <;> nlinarith
  · have x2a : 1 / 6 ≤ v2 * s := by
      have : v3 * s ≤ 2 * (v2 * s) := by nlinarith
      linarith
    have x2b : v2 * s ≤ 5 / 6 := by nlinarith
    rw [ht, mul_add, hT2]; apply clear_of_band (p := N2) <;> linarith
  · rw [ht, mul_add, hT3]; apply clear_of_band (p := N3) <;> linarith
  · rw [ht, show (v3 + v1) * (T + s) = v3 * T + v1 * T + (v3 * s + v1 * s) by ring, hT1, hT3]
    apply clear_of_band (p := N3 + N1 + 1)
    · push_cast; linarith
    · push_cast; nlinarith

/-- **λ = 0 is the uniform case.** If `D ∣ v₄` and `v₃ < v₄` (`v₂ = cD`, `v₃ = (c+1)D`, `c ≥ 1`), then `v₄ ≥ (c+2)D` and
the condition of `s6_meeting_uniform` holds. -/
theorem lam_zero_uniform {v2 v3 v4 c D : ℕ} (hc : 1 ≤ c) (hv2 : v2 = c * D) (hv3 : v3 = (c + 1) * D)
    (hd : D ∣ v4) (h34 : v3 < v4) : 4 * (v2 : ℝ) * v3 ≤ v4 * (5 * v2 - v3) := by
  obtain ⟨e, rfl⟩ := hd
  have hD : 0 < D := by rcases Nat.eq_zero_or_pos D with h | h <;> [simp_all; exact h]
  have he : c + 2 ≤ e := by
    have : (c + 1) * D < D * e := by rw [← hv3]; exact h34
    have : c + 1 < e := by nlinarith
    omega
  rw [hv2, hv3]; push_cast
  have heR : (c : ℝ) + 2 ≤ e := by exact_mod_cast he
  have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have h5 : (0 : ℝ) ≤ 5 * (c * D) - (c + 1) * D := by nlinarith
  have : 4 * ((c : ℝ) * D) * ((c + 1) * D) ≤ ((c + 2) * D) * (5 * (c * D) - (c + 1) * D) := by
    have e : ((c : ℝ) + 2) * D * (5 * (c * D) - (c + 1) * D) - 4 * (c * D) * ((c + 1) * D) = (3 * c - 2) * D ^ 2 := by ring
    have : (0 : ℝ) ≤ (3 * c - 2) * D ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  calc 4 * ((c : ℝ) * D) * ((c + 1) * D) ≤ ((c + 2) * D) * (5 * (c * D) - (c + 1) * D) := this
    _ ≤ (D * e) * (5 * (c * D) - (c + 1) * D) := by
        apply mul_le_mul_of_nonneg_right _ h5; nlinarith

/-- **A grid point in an interval.** With `gcd(v₁, D) = 1` and an interval `[lo, hi] ⊆ [0, 1)` of length at least `1/D`,
some `k` puts `(k v₁ mod D)/D` in it. -/
theorem exists_grid_point (v1 D : ℕ) (hD : 1 < D) (hcop : Nat.Coprime v1 D) {lo hi : ℝ} (hlo : 0 ≤ lo)
    (hhi : hi < 1) (hlen : 1 ≤ D * (hi - lo)) :
    ∃ k : ℕ, lo ≤ ((v1 * k % D : ℕ) : ℝ) / D ∧ ((v1 * k % D : ℕ) : ℝ) / D ≤ hi := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  set j := ⌈lo * D⌉₊ with hj
  have hj1 : lo * D ≤ j := Nat.le_ceil _
  have hj2 : (j : ℝ) < lo * D + 1 := Nat.ceil_lt_add_one (by positivity)
  have hjD : j < D := by
    have : (j : ℝ) < D := by nlinarith
    exact_mod_cast this
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hD
  refine ⟨j * u, ?_, ?_⟩ <;>
  · have e : v1 * (j * u) % D = j := by
      rw [show v1 * (j * u) = j * (v1 * u) by ring, Nat.mul_mod, hu, mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hjD]
    rw [e]
    first
    | (rw [le_div_iff₀ hDR]; linarith)
    | (rw [div_le_iff₀ hDR]; nlinarith)


/-! ### New in E98 -/

/-- **The window before the meeting time**, by reflection `t ↦ −t`: runner 1 at phase `p₁ ∈ [4/9, 5/6]`, runner 4's
reflected phase `1 − p₄` meeting the arc condition of `s6_window_fold`. -/
theorem s6_window_fold_before {v1 v2 v3 v4 v5 D T p1 p4 : ℝ} {N2 N3 N1 N4 m : ℤ} (h1 : 0 < v1) (hD : 0 < D)
    (h2 : 0 < v2) (h23 : v2 ≤ v3) (h13 : 3 * v1 < v3) (h34 : v3 ≤ v4) (h45 : v4 ≤ v5)
    (hT2 : v2 * T = N2) (hT3 : v3 * T = N3) (hT1 : v1 * T = N1 + p1) (hT4 : v4 * T = N4 + p4)
    (hp1a : 4 / 9 ≤ p1) (hp1b : p1 ≤ 5 / 6)
    (hlo : (m : ℝ) + 1 / 6 - v4 * (5 / (6 * v3) - 1 / (6 * v2)) + v4 / (3 * v5) ≤ (1 - p4) + v4 / (6 * v2))
    (hhi : (1 - p4) + v4 / (6 * v2) ≤ (m : ℝ) + 5 / 6 - v4 / (3 * v5))
    (hlam : v4 / (3 * v5) ≤ v4 * (5 / (6 * v3) - 1 / (6 * v2))) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  obtain ⟨t, a1, a2, a3, a4, a5⟩ := s6_window_fold (T := -T) (p1 := 1 - p1) (p4 := 1 - p4)
    (N2 := -N2) (N3 := -N3) (N1 := -N1 - 1) (N4 := -N4 - 1) (m := m) h1 hD h2 h23 h13 h34 h45
    (by rw [mul_neg, hT2]; push_cast; ring) (by rw [mul_neg, hT3]; push_cast; ring)
    (by rw [mul_neg, hT1]; push_cast; ring) (by rw [mul_neg, hT4]; push_cast; ring)
    (by linarith) (by linarith) hlo hhi hlam
  have neg : ∀ v : ℝ, circDist (v * -t) = circDist (v * t) := fun v => by rw [mul_neg, circDist.symm_neg]
  exact ⟨-t, by rw [neg]; exact a1, by rw [neg]; exact a2, by rw [neg]; exact a3, by rw [neg]; exact a4,
    by rw [neg]; exact a5⟩

/-- **§6, D ≥ 15, gcd(v₁, D) = 1, direction λ ≠ ±1.** (`v₄ ≡ λ v₁ mod D`, representative with `2|λ| ≤ D`.) -/
theorem s6_off_unit {v1 v2 v3 v4 v5 c D : ℕ} (h0 : 0 < v1) (h34 : v3 < v4) (h45 : v4 ≤ v5) (hc : 1 ≤ c)
    (hv2 : v2 = c * D) (hv3 : v3 = (c + 1) * D) (hsmall : 3 * v1 < v3) (hcop : Nat.Coprime v1 D) (hD : 15 ≤ D)
    (l : ℤ) (hl : (v4 : ℤ) ≡ l * v1 [ZMOD D]) (hl2 : 2 * |l| ≤ D) (hl1 : |l| ≠ 1) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have hnd : ¬ D ∣ v1 := fun h => by
    have : D ∣ Nat.gcd v1 D := Nat.dvd_gcd h dvd_rfl
    rw [hcop] at this; have := Nat.le_of_dvd one_pos this; omega
  by_cases hl0 : l = 0
  · subst hl0
    have hd : D ∣ v4 := by
      have : (v4 : ℤ) ≡ 0 [ZMOD D] := by simpa using hl
      exact Int.natCast_dvd_natCast.mp (Int.modEq_zero_iff_dvd.mp this)
    exact s6_meeting_uniform h0 h45 (by omega) hc hv2 hv3 hsmall hnd (lam_zero_uniform hc hv2 hv3 hd h34)
  · have hl2' : 2 ≤ |l| := by
      have : 0 < |l| := abs_pos.mpr hl0
      omega
    exact s6_generic h0 h34 h45 hc hv2 hv3 hsmall hcop hD l hl hl2' hl2

/-- **The sum lemma on whole numbers.** `v₄ = v₃ + v₁`, `gcd(v₁, D) = 1`, and the interval
`I = [1/3 + v₃/(3v₅), (5/6)(1 − v₁/v₃)]` at least `1/D` long. -/
theorem s6_sum {v1 v2 v3 v5 c D : ℕ} (h0 : 0 < v1) (hc : 1 ≤ c) (hv2 : v2 = c * D) (hv3 : v3 = (c + 1) * D)
    (hcop : Nat.Coprime v1 D) (hD : 2 ≤ D) (h5 : 0 < v5)
    (hlen : 1 ≤ (D : ℝ) * (5 / 6 * (1 - (v1 : ℝ) / v3) - (1 / 3 + (v3 : ℝ) / (3 * v5)))) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (((v3 + v1 : ℕ) : ℝ) * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hv2R : (v2 : ℝ) = c * D := by rw [hv2]; push_cast; ring
  have hv3R : (v3 : ℝ) = (c + 1) * D := by rw [hv3]; push_cast; ring
  have h2p : (0 : ℝ) < v2 := by rw [hv2R]; positivity
  have h3p : (0 : ℝ) < v3 := by rw [hv3R]; positivity
  have h1p : (0 : ℝ) < v1 := by exact_mod_cast h0
  have h5p : (0 : ℝ) < v5 := by exact_mod_cast h5
  have hlo0 : (0 : ℝ) ≤ 1 / 3 + (v3 : ℝ) / (3 * v5) := by positivity
  have hhi1 : 5 / 6 * (1 - (v1 : ℝ) / v3) < 1 := by
    have : 0 < (v1 : ℝ) / v3 := by positivity
    linarith
  obtain ⟨k, hk1, hk2⟩ := exists_grid_point v1 D (by omega) hcop hlo0 hhi1 hlen
  set j := v1 * k % D with hj
  have hdm : ((v1 * k : ℕ) : ℝ) = D * ((v1 * k / D : ℕ) : ℝ) + (j : ℝ) := by
    exact_mod_cast (Nat.div_add_mod (v1 * k) D).symm
  set T : ℝ := (k : ℝ) / D with hT
  have hT1 : (v1 : ℝ) * T = ((v1 * k / D : ℕ) : ℤ) + (j : ℝ) / D := by
    rw [hT, Int.cast_natCast]; push_cast at hdm; field_simp; linarith
  have hT2 : (v2 : ℝ) * T = ((c * k : ℕ) : ℤ) := by rw [hT, hv2R]; push_cast; field_simp
  have hT3 : (v3 : ℝ) * T = (((c + 1) * k : ℕ) : ℤ) := by rw [hT, hv3R]; push_cast; field_simp
  have h23 : (v2 : ℝ) ≤ v3 := by rw [hv2R, hv3R]; nlinarith
  have h2half : (v3 : ℝ) ≤ 2 * v2 := by rw [hv2R, hv3R]; nlinarith
  obtain ⟨t, a1, a2, a3, a4, a5⟩ := s6_sum_window h1p h2p h23 h2half h5p hT1 hT2 hT3 hk1 hk2
  refine ⟨t, a1, a2, a3, ?_, a5⟩
  push_cast; exact a4

/-! ### E99: the directions λ = ±1 -/

/-- At the meeting time `k/D` for a `k` with `k v₁ ≡ j`, the readings: runners 2, 3 whole, runner 1 `q₁ + j/D`,
runner 4 `q₄ + l j/D` (when `v₄ ≡ l v₁`). -/
theorem readings_at {v1 v2 v3 v4 c D j : ℕ} (hv2 : v2 = c * D) (hv3 : v3 = (c + 1) * D) (hcop : Nat.Coprime v1 D)
    (hD : 1 < D) (hjD : j < D) (l : ℤ) (hl : (v4 : ℤ) ≡ l * v1 [ZMOD D]) :
    ∃ T : ℝ, ∃ N1 N2 N3 N4 : ℤ, (v1 : ℝ) * T = N1 + (j : ℝ) / D ∧ (v2 : ℝ) * T = N2 ∧ (v3 : ℝ) * T = N3 ∧
      (v4 : ℝ) * T = N4 + (l : ℝ) * j / D := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hD
  set k := j * u with hk
  have hv1k : v1 * k % D = j := by
    rw [hk, show v1 * (j * u) = j * (v1 * u) by ring, Nat.mul_mod, hu, mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hjD]
  set q1 := v1 * k / D with hq1
  have hdiv1 : v1 * k = D * q1 + j := by rw [hq1, ← hv1k]; exact (Nat.div_add_mod _ _).symm
  have hmod4 : (v4 * k : ℤ) ≡ l * j [ZMOD D] := by
    have a : (v4 * k : ℤ) ≡ l * v1 * k [ZMOD D] := Int.ModEq.mul_right _ hl
    have b : (l * v1 * k : ℤ) = l * (D * q1) + l * j := by
      have : ((v1 * k : ℕ) : ℤ) = ((D * q1 + j : ℕ) : ℤ) := by rw [hdiv1]
      push_cast at this; rw [mul_assoc, this]; ring
    rw [b] at a
    refine a.trans ?_
    have : (l * (D * q1) + l * j : ℤ) ≡ 0 + l * j [ZMOD D] :=
      Int.ModEq.add_right _ (Int.modEq_zero_iff_dvd.mpr ⟨l * q1, by ring⟩)
    simpa using this
  obtain ⟨q4, hq4⟩ := hmod4.symm.dvd
  refine ⟨(k : ℝ) / D, q1, c * k, (c + 1) * k, q4, ?_, ?_, ?_, ?_⟩
  · have : ((v1 * k : ℕ) : ℝ) = D * q1 + j := by exact_mod_cast hdiv1
    push_cast at this ⊢; field_simp; linarith
  · rw [hv2]; push_cast; field_simp
  · rw [hv3]; push_cast; field_simp
  · have h' : (v4 * k : ℤ) = l * j + D * q4 := by linarith [hq4]
    have : ((v4 * k : ℤ) : ℝ) = ((l * j + D * q4 : ℤ) : ℝ) := by rw [h']
    push_cast at this; field_simp; linarith

/-- A grid point `j/D` in an interval of length at least `1/D` inside `[0, 1)`. -/
theorem exists_j (D : ℕ) (hD : 0 < D) {a L : ℝ} (ha : 0 ≤ a) (haL : a + L < 1) (hL : 1 ≤ D * L) :
    ∃ j : ℕ, j < D ∧ a ≤ (j : ℝ) / D ∧ (j : ℝ) / D ≤ a + L := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  refine ⟨⌈a * D⌉₊, ?_, ?_, ?_⟩
  · have h1 : (⌈a * D⌉₊ : ℝ) < a * D + 1 := Nat.ceil_lt_add_one (by positivity)
    have : (⌈a * D⌉₊ : ℝ) < D := by nlinarith
    exact_mod_cast this
  · rw [le_div_iff₀ hDR]; exact Nat.le_ceil _
  · have h1 : (⌈a * D⌉₊ : ℝ) < a * D + 1 := Nat.ceil_lt_add_one (by positivity)
    rw [div_le_iff₀ hDR]; nlinarith

section closers
variable {v1 v2 v3 v4 v5 c D : ℕ}

/-- **Closing at a grid point, window after the meeting time.** `q₄ = v₄/v₃`, `u = v₃/v₂`, `μ = v₄/(3v₅)`. -/
theorem close_after (h0 : 0 < v1) (hc : 1 ≤ c) (hv2 : v2 = c * D) (hv3 : v3 = (c + 1) * D) (hsmall : 3 * v1 < v3)
    (h34 : v3 < v4) (h45 : v4 ≤ v5) (hcop : Nat.Coprime v1 D) (hD : 1 < D) (l : ℤ) (hl : (v4 : ℤ) ≡ l * v1 [ZMOD D])
    (j : ℕ) (hjD : j < D) (m : ℤ) (hp1 : 1 / 6 ≤ (j : ℝ) / D) (hp2 : (j : ℝ) / D ≤ 5 / 9)
    (hlow : (m : ℝ) + 1 / 6 ≤ l * ((j : ℝ) / D) + 5 / 6 * ((v4 : ℝ) / v3) - (v4 : ℝ) / (3 * v5))
    (hup : l * ((j : ℝ) / D) + ((v4 : ℝ) / v3) * ((v3 : ℝ) / v2) / 6 + (v4 : ℝ) / (3 * v5) ≤ m + 5 / 6) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  obtain ⟨T, N1, N2, N3, N4, hT1, hT2, hT3, hT4⟩ := readings_at hv2 hv3 hcop hD hjD l hl
  have hDR : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
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
  have e1 : (v4 : ℝ) * (5 / (6 * v3)) = 5 / 6 * ((v4 : ℝ) / v3) := by field_simp
  have e2 : (v4 : ℝ) / (6 * v2) = ((v4 : ℝ) / v3) * ((v3 : ℝ) / v2) / 6 := by field_simp
  have e3 : (v4 : ℝ) * (1 / (6 * v2)) = (v4 : ℝ) / (6 * v2) := by ring
  have hT4' : (v4 : ℝ) * T = N4 + (l * ((j : ℝ) / D)) := by rw [hT4]; ring
  refine s6_window_fold (m := m) h1p hDR h2p h23 h13 h34R h45R hT2 hT3 hT1 hT4' hp1 hp2 ?_ ?_ ?_
  · rw [mul_sub, e1, e3, e2]; linarith
  · rw [e2]; linarith
  · -- μ ≤ 1/3 ≤ 1/2 ≤ v₄ ℓ
    have hμ : (v4 : ℝ) / (3 * v5) ≤ 1 / 3 := by rw [div_le_iff₀ (by positivity)]; linarith
    have hd : (0 : ℝ) ≤ 5 / (6 * v3) - 1 / (6 * v2) := by
      rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by positivity)]; rw [hv2R, hv3R]; nlinarith
    have : (v3 : ℝ) * (5 / (6 * v3) - 1 / (6 * v2)) ≤ v4 * (5 / (6 * v3) - 1 / (6 * v2)) :=
      mul_le_mul_of_nonneg_right h34R hd
    have e : (v3 : ℝ) * (5 / (6 * v3) - 1 / (6 * v2)) = 5 / 6 - v3 / (6 * v2) := by field_simp
    have : (v3 : ℝ) / (6 * v2) ≤ 1 / 3 := by rw [div_le_iff₀ (by positivity), hv2R, hv3R]; nlinarith
    linarith

/-- **Closing at a grid point, window before the meeting time.** -/
theorem close_before (h0 : 0 < v1) (hc : 1 ≤ c) (hv2 : v2 = c * D) (hv3 : v3 = (c + 1) * D) (hsmall : 3 * v1 < v3)
    (h34 : v3 < v4) (h45 : v4 ≤ v5) (hcop : Nat.Coprime v1 D) (hD : 1 < D) (l : ℤ) (hl : (v4 : ℤ) ≡ l * v1 [ZMOD D])
    (j : ℕ) (hjD : j < D) (m : ℤ) (hp1 : 4 / 9 ≤ (j : ℝ) / D) (hp2 : (j : ℝ) / D ≤ 5 / 6)
    (hlow : (m : ℝ) + 1 / 6 ≤ 1 - l * ((j : ℝ) / D) + 5 / 6 * ((v4 : ℝ) / v3) - (v4 : ℝ) / (3 * v5))
    (hup : 1 - l * ((j : ℝ) / D) + ((v4 : ℝ) / v3) * ((v3 : ℝ) / v2) / 6 + (v4 : ℝ) / (3 * v5) ≤ m + 5 / 6) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  obtain ⟨T, N1, N2, N3, N4, hT1, hT2, hT3, hT4⟩ := readings_at hv2 hv3 hcop hD hjD l hl
  have hDR : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
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
  have e1 : (v4 : ℝ) * (5 / (6 * v3)) = 5 / 6 * ((v4 : ℝ) / v3) := by field_simp
  have e2 : (v4 : ℝ) / (6 * v2) = ((v4 : ℝ) / v3) * ((v3 : ℝ) / v2) / 6 := by field_simp
  have e3 : (v4 : ℝ) * (1 / (6 * v2)) = (v4 : ℝ) / (6 * v2) := by ring
  have hT4' : (v4 : ℝ) * T = N4 + (l * ((j : ℝ) / D)) := by rw [hT4]; ring
  refine s6_window_fold_before (m := m) h1p hDR h2p h23 h13 h34R h45R hT2 hT3 hT1 hT4' hp1 hp2 ?_ ?_ ?_
  · rw [mul_sub, e1, e3, e2]; linarith
  · rw [e2]; linarith
  · have hμ : (v4 : ℝ) / (3 * v5) ≤ 1 / 3 := by rw [div_le_iff₀ (by positivity)]; linarith
    have hd : (0 : ℝ) ≤ 5 / (6 * v3) - 1 / (6 * v2) := by
      rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by positivity)]; rw [hv2R, hv3R]; nlinarith
    have : (v3 : ℝ) * (5 / (6 * v3) - 1 / (6 * v2)) ≤ v4 * (5 / (6 * v3) - 1 / (6 * v2)) :=
      mul_le_mul_of_nonneg_right h34R hd
    have e : (v3 : ℝ) * (5 / (6 * v3) - 1 / (6 * v2)) = 5 / 6 - v3 / (6 * v2) := by field_simp
    have : (v3 : ℝ) / (6 * v2) ≤ 1 / 3 := by rw [div_le_iff₀ (by positivity), hv2R, hv3R]; nlinarith
    linarith

/-- **Closing at a grid point by the sum lemma** (`v₄ = v₃ + v₁`). -/
theorem close_sum (h0 : 0 < v1) (hc : 1 ≤ c) (hv2 : v2 = c * D) (hv3 : v3 = (c + 1) * D) (h5 : 0 < v5)
    (h4 : v4 = v3 + v1) (hcop : Nat.Coprime v1 D) (hD : 1 < D) (j : ℕ) (hjD : j < D)
    (hp1 : 1 / 3 + (v3 : ℝ) / (3 * v5) ≤ (j : ℝ) / D) (hp2 : (j : ℝ) / D ≤ 5 / 6 * (1 - (v1 : ℝ) / v3)) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have hl : (v4 : ℤ) ≡ 1 * v1 [ZMOD D] := by
    rw [h4, hv3, one_mul]; push_cast
    exact (Int.modEq_iff_dvd.mpr ⟨-(c + 1), by ring⟩)
  obtain ⟨T, N1, N2, N3, N4, hT1, hT2, hT3, -⟩ := readings_at hv2 hv3 hcop hD hjD 1 hl
  have hDR : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hv2R : (v2 : ℝ) = c * D := by rw [hv2]; push_cast; ring
  have hv3R : (v3 : ℝ) = (c + 1) * D := by rw [hv3]; push_cast; ring
  have h2p : (0 : ℝ) < v2 := by rw [hv2R]; positivity
  have h23 : (v2 : ℝ) ≤ v3 := by rw [hv2R, hv3R]; nlinarith
  have h2half : (v3 : ℝ) ≤ 2 * v2 := by rw [hv2R, hv3R]; nlinarith
  have h1p : (0 : ℝ) < v1 := by exact_mod_cast h0
  have h5p : (0 : ℝ) < v5 := by exact_mod_cast h5
  obtain ⟨t, a1, a2, a3, a4, a5⟩ := s6_sum_window h1p h2p h23 h2half h5p hT1 hT2 hT3 hp1 hp2
  refine ⟨t, a1, a2, a3, ?_, a5⟩
  rw [h4]; push_cast; exact a4

end closers

set_option maxHeartbeats 4000000 in
/-- **§6, D ≥ 15, gcd(v₁, D) = 1, directions λ = ±1** (near-runner case). Case tree from `s6_lam_cert_v1.py`
(over `U = v₃/v₂`, `Q = v₄/v₃`, `M = v₄/(3v₅)`) and, for `c = 1`, `D = 15..19`, the explicit cases of
`s6_lam_small_v1.py`. Leaves close by the window after or before the meeting time, or by the sum lemma. -/
theorem s6_unit_dir {v1 v2 v3 v4 v5 c D : ℕ} (h0 : 0 < v1) (h34 : v3 < v4) (h45 : v4 < v5) (hc : 1 ≤ c)
    (hv2 : v2 = c * D) (hv3 : v3 = (c + 1) * D) (hsmall : 3 * v1 < v3) (hcop : Nat.Coprime v1 D) (hD : 15 ≤ D)
    (hnr : (v4 : ℝ) * (5 * v2 - v3) < 4 * v2 * v3) (l : ℤ) (hl : (v4 : ℤ) ≡ l * v1 [ZMOD D]) (hl1 : l = 1 ∨ l = -1) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have hD1 : 1 < D := by omega
  have hDR : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hv2R : (v2 : ℝ) = c * D := by rw [hv2]; push_cast; ring
  have hv3R : (v3 : ℝ) = (c + 1) * D := by rw [hv3]; push_cast; ring
  have h2p : (0 : ℝ) < v2 := by rw [hv2R]; positivity
  have h3p : (0 : ℝ) < v3 := by rw [hv3R]; positivity
  have h34R : (v3 : ℝ) < v4 := by exact_mod_cast h34
  have h45R : (v4 : ℝ) < v5 := by exact_mod_cast h45
  have h4p : (0 : ℝ) < v4 := by linarith
  have h5p : (0 : ℝ) < v5 := by linarith
  set Q : ℝ := (v4 : ℝ) / v3 with hQv
  set U : ℝ := (v3 : ℝ) / v2 with hUv
  set M : ℝ := (v4 : ℝ) / (3 * v5) with hMv
  have hUdef : U = ((c : ℝ) + 1) / c := by rw [hUv, hv2R, hv3R]; field_simp
  have hU1 : 1 ≤ U := by rw [hUdef, le_div_iff₀ (by linarith)]; linarith
  have hU2 : U ≤ 2 := by rw [hUdef, div_le_iff₀ (by linarith)]; linarith
  have hU3 : 2 < c → U ≤ 4 / 3 := fun h => by
    have : (3 : ℝ) ≤ c := by exact_mod_cast h
    rw [hUdef, div_le_iff₀ (by linarith)]; linarith
  have hQ1 : 1 ≤ Q := by rw [hQv, le_div_iff₀ h3p]; linarith
  have hQU : Q * (5 - U) ≤ 4 := by
    have e : Q * (5 - U) = (v4 : ℝ) * (5 * v2 - v3) / (v2 * v3) := by rw [hQv, hUv]; field_simp
    rw [e, div_le_iff₀ (by positivity)]; linarith
  have hQle : Q ≤ 4 / (5 - U) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hQUb : Q * U ≤ 4 * U / (5 - U) := by
    have := mul_le_mul_of_nonneg_right hQle (show (0 : ℝ) ≤ U by linarith)
    calc Q * U ≤ 4 / (5 - U) * U := this
      _ = 4 * U / (5 - U) := by ring
  have hM0 : 0 ≤ M := by positivity
  have hM3 : M ≤ 1 / 3 := by rw [hMv, div_le_iff₀ (by positivity)]; linarith
  have hMmax : M ≤ (v4 : ℝ) / (3 * (v4 + 1)) := by
    have : (v4 : ℝ) + 1 ≤ v5 := by exact_mod_cast h45
    rw [hMv]; exact div_le_div_of_nonneg_left h4p.le (by positivity) (by linarith)
  have hDL15 : 1 ≤ (D : ℝ) * (1 / 15) := by
    have : (15 : ℝ) ≤ D := by exact_mod_cast hD
    linarith
  -- closers at a grid point
  have closeAP : ∀ (j : ℕ) (m : ℤ), j < D → 1 / 6 ≤ (j : ℝ) / D → (j : ℝ) / D ≤ 5 / 9 →
      (m : ℝ) + 1 / 6 ≤ l * ((j : ℝ) / D) + 5 / 6 * Q - M → l * ((j : ℝ) / D) + Q * U / 6 + M ≤ m + 5 / 6 →
      ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
        (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) :=
    fun j m hjD hp1 hp2 hlo hup => close_after h0 hc hv2 hv3 hsmall h34 h45.le hcop hD1 l hl j hjD m hp1 hp2 hlo hup
  have closeBP : ∀ (j : ℕ) (m : ℤ), j < D → 4 / 9 ≤ (j : ℝ) / D → (j : ℝ) / D ≤ 5 / 6 →
      (m : ℝ) + 1 / 6 ≤ 1 - l * ((j : ℝ) / D) + 5 / 6 * Q - M → 1 - l * ((j : ℝ) / D) + Q * U / 6 + M ≤ m + 5 / 6 →
      ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
        (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) :=
    fun j m hjD hp1 hp2 hlo hup => close_before h0 hc hv2 hv3 hsmall h34 h45.le hcop hD1 l hl j hjD m hp1 hp2 hlo hup
  have closeSP : v4 = v3 + v1 → ∀ (j : ℕ), j < D → M ≤ ((j : ℝ) / D - 1 / 3) * Q → (j : ℝ) / D ≤ 5 / 6 * (2 - Q) →
      ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
        (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
    intro hδ j hjD h1 h2
    have hQe : Q = 1 + (v1 : ℝ) / v3 := by
      rw [hQv, hδ]; push_cast; field_simp
    refine close_sum h0 hc hv2 hv3 (by omega) hδ hcop hD1 j hjD ?_ ?_
    · have e : (v3 : ℝ) / (3 * v5) = M / Q := by rw [hMv, hQv]; field_simp
      rw [e, ← le_sub_iff_add_le', div_le_iff₀ (by linarith)]; linarith
    · rw [hQe] at h2; linarith
  -- closers on an interval of length L ≥ 1/D
  have closeA : ∀ (m : ℤ) (a L : ℝ), 1 / 6 ≤ a → a + L ≤ 5 / 9 → 1 ≤ (D : ℝ) * L →
      (∀ p : ℝ, a ≤ p → p ≤ a + L → (m : ℝ) + 1 / 6 ≤ l * p + 5 / 6 * Q - M) →
      (∀ p : ℝ, a ≤ p → p ≤ a + L → l * p + Q * U / 6 + M ≤ m + 5 / 6) →
      ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
        (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
    intro m a L ha haL hDL hlo hup
    obtain ⟨j, hjD, hj1, hj2⟩ := exists_j D (by omega) (a := a) (L := L) (by linarith) (by linarith) hDL
    exact closeAP j m hjD (by linarith) (by linarith) (hlo _ hj1 hj2) (hup _ hj1 hj2)
  have closeB : ∀ (m : ℤ) (a L : ℝ), 4 / 9 ≤ a → a + L ≤ 5 / 6 → 1 ≤ (D : ℝ) * L →
      (∀ p : ℝ, a ≤ p → p ≤ a + L → (m : ℝ) + 1 / 6 ≤ 1 - l * p + 5 / 6 * Q - M) →
      (∀ p : ℝ, a ≤ p → p ≤ a + L → 1 - l * p + Q * U / 6 + M ≤ m + 5 / 6) →
      ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
        (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
    intro m a L ha haL hDL hlo hup
    obtain ⟨j, hjD, hj1, hj2⟩ := exists_j D (by omega) (a := a) (L := L) (by linarith) (by linarith) hDL
    exact closeBP j m hjD (by linarith) (by linarith) (hlo _ hj1 hj2) (hup _ hj1 hj2)
  have closeS : v4 = v3 + v1 → ∀ (a L : ℝ), 0 ≤ a → a + L < 1 → 1 ≤ (D : ℝ) * L →
      (∀ p : ℝ, a ≤ p → p ≤ a + L → M ≤ (p - 1 / 3) * Q) → (∀ p : ℝ, a ≤ p → p ≤ a + L → p ≤ 5 / 6 * (2 - Q)) →
      ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
        (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
    intro hδ a L ha haL hDL h1 h2
    obtain ⟨j, hjD, hj1, hj2⟩ := exists_j D (by omega) ha haL hDL
    exact closeSP hδ j hjD (h1 _ hj1 hj2) (h2 _ hj1 hj2)
  -- λ = 1 and c ≤ 2 force the sum relation δ = v₁
  have hδ2 : c ≤ 2 → l = 1 → v4 = v3 + v1 := by
    intro hc2 hl1'
    subst hl1'
    have hv1D : v1 < D := by
      have : 3 * v1 < 3 * D := by rw [hv3] at hsmall; nlinarith
      omega
    have hδD : v4 - v3 < D := by
      have h' : (v4 : ℝ) * (4 * c - 1) < 4 * c * (c + 1) * D := by
        rw [hv2R, hv3R] at hnr; nlinarith
      have hc2R : (c : ℝ) ≤ 2 := by exact_mod_cast hc2
      have : (v4 : ℝ) < v3 + D := by
        rw [hv3R]; nlinarith
      have : v4 < v3 + D := by exact_mod_cast this
      omega
    have hm : ((v4 - v3 : ℕ) : ℤ) ≡ v1 [ZMOD D] := by
      have h3 : (v3 : ℤ) ≡ 0 [ZMOD D] := Int.modEq_zero_iff_dvd.mpr ⟨c + 1, by rw [hv3]; push_cast; ring⟩
      have := hl.sub h3
      rw [Nat.cast_sub h34.le]; simpa using this
    obtain ⟨t, ht⟩ := hm.symm.dvd
    have hdist : ((v4 - v3 : ℕ) : ℤ) - v1 = D * t := by linarith
    have hb1 : ((v4 - v3 : ℕ) : ℤ) < D := by exact_mod_cast hδD
    have hb2 : (v1 : ℤ) < D := by exact_mod_cast hv1D
    have hb3 : (0 : ℤ) ≤ ((v4 - v3 : ℕ) : ℤ) := by positivity
    have hb4 : (0 : ℤ) < v1 := by exact_mod_cast h0
    have ht0 : t = 0 := by
      rcases lt_trichotomy t 0 with h | h | h
      · nlinarith
      · exact h
      · nlinarith
    rw [ht0, mul_zero, sub_eq_zero] at hdist
    have : v4 - v3 = v1 := by exact_mod_cast hdist
    omega
  rcases hl1 with rfl | rfl
  · rcases lt_or_ge 2 c with hc3 | hc2
    · have hU43 : U ≤ 4 / 3 := hU3 hc3
      have hQUb2 : Q * U ≤ 16 / 11 := le_trans hQUb (by rw [div_le_iff₀ (by linarith)]; linarith)
      exact closeA 0 (1/6 : ℝ) (1/15 : ℝ) (by norm_num) (by norm_num) hDL15 (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)
    · have hδ : v4 = v3 + v1 := hδ2 hc2 (by rfl)
      rcases (show c = 1 ∨ c = 2 by omega) with rfl | rfl
      · have hUe : U = 2 := by rw [hUdef]; norm_num
        have hQU' : Q * U = 2 * Q := by rw [hUe]; ring
        have hQ43 : Q ≤ 4 / 3 := by have := hQle; rw [hUe] at this; linarith
        rcases le_or_gt 20 D with hD20 | hD20
        · have hDL20 : 1 ≤ (D : ℝ) * (1 / 20) := by
            have : (20 : ℝ) ≤ D := by exact_mod_cast hD20
            linarith
          rcases le_total Q (7/6 : ℝ) with hQ1 | hQ1
          · rcases le_total M (1/6 : ℝ) with hM2 | hM2
            · exact closeA 0 (1/6 : ℝ) (1/20 : ℝ) (by norm_num) (by norm_num) hDL20 (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)
            · rcases le_total Q (13/12 : ℝ) with hQ3 | hQ3
              · exact closeS hδ (2/3 : ℝ) (1/20 : ℝ) (by norm_num) (by norm_num) hDL20 (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)
              · exact closeS hδ (25/39 : ℝ) (1/20 : ℝ) (by norm_num) (by norm_num) hDL20 (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)
          · rcases le_total M (1/6 : ℝ) with hM4 | hM4
            · exact closeA 0 (1/6 : ℝ) (1/20 : ℝ) (by norm_num) (by norm_num) hDL20 (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)
            · rcases le_total Q (5/4 : ℝ) with hQ5 | hQ5
              · rcases le_total M (1/4 : ℝ) with hM6 | hM6
                · exact closeA 1 (4/9 : ℝ) (1/20 : ℝ) (by norm_num) (by norm_num) hDL20 (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)
                · rcases le_total Q (29/24 : ℝ) with hQ7 | hQ7
                  · rcases le_total M (7/24 : ℝ) with hM8 | hM8
                    · exact closeA 1 (35/72 : ℝ) (1/20 : ℝ) (by norm_num) (by norm_num) hDL20 (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)
                    · rcases le_total Q (19/16 : ℝ) with hQ9 | hQ9
                      · exact closeS hδ (13/21 : ℝ) (1/20 : ℝ) (by norm_num) (by norm_num) hDL20 (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)
                      · rcases le_total M (5/16 : ℝ) with hM10 | hM10
                        · exact closeA 1 (47/96 : ℝ) (1/20 : ℝ) (by norm_num) (by norm_num) hDL20 (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)
                        · rcases le_total Q (115/96 : ℝ) with hQ11 | hQ11
                          · exact closeS hδ (35/57 : ℝ) (1/20 : ℝ) (by norm_num) (by norm_num) hDL20 (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)
                          · exact closeA 1 (289/576 : ℝ) (1/20 : ℝ) (by norm_num) (by norm_num) hDL20 (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)
                  · exact closeA 1 (71/144 : ℝ) (1/20 : ℝ) (by norm_num) (by norm_num) hDL20 (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)
              · exact closeA 1 (11/24 : ℝ) (1/20 : ℝ) (by norm_num) (by norm_num) hDL20 (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)
        · subst hv2 hv3 hδ
          interval_cases D
          · have hv1b : v1 < 10 := by omega
            interval_cases v1
            · exact closeSP rfl 10 (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact closeSP rfl 10 (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact absurd hcop (by norm_num)
            · exact closeSP rfl 10 (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact absurd hcop (by norm_num)
            · exact absurd hcop (by norm_num)
            · exact closeAP 7 1 (by norm_num) (by norm_num) (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact closeAP 7 1 (by norm_num) (by norm_num) (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact absurd hcop (by norm_num)
          · have hv1b : v1 < 11 := by omega
            interval_cases v1
            · exact closeSP rfl 11 (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact absurd hcop (by norm_num)
            · exact closeSP rfl 11 (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact absurd hcop (by norm_num)
            · exact closeSP rfl 10 (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact absurd hcop (by norm_num)
            · exact closeAP 8 1 (by norm_num) (by norm_num) (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact absurd hcop (by norm_num)
            · exact closeAP 7 1 (by norm_num) (by norm_num) (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact absurd hcop (by norm_num)
          · have hv1b : v1 < 12 := by omega
            interval_cases v1
            · exact closeSP rfl 12 (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact closeSP rfl 11 (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact closeSP rfl 11 (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact closeSP rfl 11 (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact closeSP rfl 11 (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact closeBP 8 1 (by norm_num) (by norm_num) (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact closeBP 8 1 (by norm_num) (by norm_num) (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact closeAP 8 1 (by norm_num) (by norm_num) (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact closeAP 8 1 (by norm_num) (by norm_num) (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact closeAP 8 1 (by norm_num) (by norm_num) (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact closeAP 7 1 (by norm_num) (by norm_num) (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
          · have hv1b : v1 < 12 := by omega
            interval_cases v1
            · exact closeSP rfl 12 (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact absurd hcop (by norm_num)
            · exact absurd hcop (by norm_num)
            · exact absurd hcop (by norm_num)
            · exact closeBP 8 1 (by norm_num) (by norm_num) (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact absurd hcop (by norm_num)
            · exact closeBP 8 1 (by norm_num) (by norm_num) (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact absurd hcop (by norm_num)
            · exact absurd hcop (by norm_num)
            · exact absurd hcop (by norm_num)
            · exact closeAP 8 1 (by norm_num) (by norm_num) (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
          · have hv1b : v1 < 13 := by omega
            interval_cases v1
            · exact closeSP rfl 13 (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact closeSP rfl 13 (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact closeSP rfl 13 (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact closeSP rfl 12 (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact closeSP rfl 12 (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact closeSP rfl 12 (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact closeBP 9 1 (by norm_num) (by norm_num) (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact closeBP 9 1 (by norm_num) (by norm_num) (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact closeAP 9 1 (by norm_num) (by norm_num) (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact closeAP 9 1 (by norm_num) (by norm_num) (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact closeAP 8 1 (by norm_num) (by norm_num) (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
            · exact closeAP 8 1 (by norm_num) (by norm_num) (by norm_num) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0]) (by (try simp only [hQv, hUv]); norm_num <;> nlinarith [hMmax, hM0])
      · have hUe : U = 3 / 2 := by rw [hUdef]; norm_num
        have hQU' : Q * U = 3 / 2 * Q := by rw [hUe]; ring
        have hQ87 : Q ≤ 8 / 7 := by have := hQle; rw [hUe] at this; linarith
        rcases le_total M (1/6 : ℝ) with hM12 | hM12
        · exact closeA 0 (1/6 : ℝ) (1/15 : ℝ) (by norm_num) (by norm_num) hDL15 (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)
        · rcases le_total M (1/4 : ℝ) with hM13 | hM13
          · exact closeA 0 (1/6 : ℝ) (1/15 : ℝ) (by norm_num) (by norm_num) hDL15 (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)
          · rcases le_total Q (15/14 : ℝ) with hQ14 | hQ14
            · exact closeS hδ (2/3 : ℝ) (1/15 : ℝ) (by norm_num) (by norm_num) hDL15 (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)
            · exact closeS hδ (29/45 : ℝ) (1/15 : ℝ) (by norm_num) (by norm_num) hDL15 (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)
  · have hQUb3 : Q * U ≤ 8 / 3 := le_trans hQUb (by rw [div_le_iff₀ (by linarith)]; linarith)
    exact closeA 0 (1/6 : ℝ) (1/15 : ℝ) (by norm_num) (by norm_num) hDL15 (fun p h1 h2 => by nlinarith) (fun p h1 h2 => by nlinarith)

/-- **§6, the branch D ≥ 15 with gcd(v₁, D) = 1, every direction.** -/
theorem s6_branch {v1 v2 v3 v4 v5 c D : ℕ} (h0 : 0 < v1) (h34 : v3 < v4) (h45 : v4 < v5) (hc : 1 ≤ c)
    (hv2 : v2 = c * D) (hv3 : v3 = (c + 1) * D) (hsmall : 3 * v1 < v3) (hcop : Nat.Coprime v1 D) (hD : 15 ≤ D) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have hnd : ¬ D ∣ v1 := fun h => by
    have : D ∣ Nat.gcd v1 D := Nat.dvd_gcd h dvd_rfl
    rw [hcop] at this; have := Nat.le_of_dvd one_pos this; omega
  by_cases hw : 4 * (v2 : ℝ) * v3 ≤ v4 * (5 * v2 - v3)
  · exact s6_meeting_uniform h0 h45.le (by omega) hc hv2 hv3 hsmall hnd hw
  push Not at hw
  -- the direction λ: v₄ ≡ λ v₁ (mod D), representative in (−D/2, D/2]
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (show 1 < D by omega)
  set l0 := v4 * u % D with hl0
  have hl0D : l0 < D := Nat.mod_lt _ (by omega)
  have hcong0 : (v4 : ℤ) ≡ (l0 : ℤ) * v1 [ZMOD D] := by
    have a : ((v1 * u : ℕ) : ℤ) ≡ 1 [ZMOD D] := by
      unfold Int.ModEq; rw [← Int.natCast_mod, hu]
      exact (Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast (show 1 < D by omega))).symm
    have b : ((l0 : ℕ) : ℤ) ≡ ((v4 * u : ℕ) : ℤ) [ZMOD D] := by
      unfold Int.ModEq; rw [hl0, Int.natCast_mod]; exact Int.emod_emod_of_dvd _ dvd_rfl
    push_cast at a b
    calc (v4 : ℤ) = v4 * 1 := by ring
      _ ≡ v4 * (v1 * u) [ZMOD D] := Int.ModEq.mul_left _ a.symm
      _ = (v4 * u) * v1 := by ring
      _ ≡ (l0 : ℤ) * v1 [ZMOD D] := Int.ModEq.mul_right _ b.symm
  by_cases hhalf : 2 * l0 ≤ D
  · by_cases h1 : l0 = 1
    · rw [h1] at hcong0
      exact s6_unit_dir h0 h34 h45 hc hv2 hv3 hsmall hcop hD hw 1 (by simpa using hcong0) (Or.inl rfl)
    · exact s6_off_unit h0 h34 h45.le hc hv2 hv3 hsmall hcop hD (l0 : ℤ) hcong0
        (by rw [abs_of_nonneg (Int.natCast_nonneg _)]; exact_mod_cast hhalf)
        (by rw [abs_of_nonneg (Int.natCast_nonneg _)]; intro h; exact h1 (by exact_mod_cast h))
  · push Not at hhalf
    have hcong1 : (v4 : ℤ) ≡ ((l0 : ℤ) - D) * v1 [ZMOD D] :=
      hcong0.trans (Int.modEq_iff_dvd.mpr ⟨-(v1 : ℤ), by ring⟩)
    have hl0D' : (l0 : ℤ) < D := by exact_mod_cast hl0D
    have habs : |((l0 : ℤ) - D)| = D - l0 := by rw [abs_of_neg (by linarith)]; ring
    by_cases h1 : l0 + 1 = D
    · have hm1 : (l0 : ℤ) - D = -1 := by have h' : (l0 : ℤ) + 1 = D := (by exact_mod_cast h1); linarith
      exact s6_unit_dir h0 h34 h45 hc hv2 hv3 hsmall hcop hD hw ((l0 : ℤ) - D) hcong1 (Or.inr hm1)
    · have hh : (D : ℤ) < 2 * l0 := by exact_mod_cast hhalf
      exact s6_off_unit h0 h34 h45.le hc hv2 hv3 hsmall hcop hD ((l0 : ℤ) - D) hcong1
        (by rw [habs]; linarith)
        (by rw [habs]; intro h; apply h1; omega)

end LRC.S6Native
namespace LRC.S6Native
open LRC.S7Native LRC.S8Native

/-- **BHK §6 natively, the branch `D ≥ 15`, `gcd(v₁, D) = 1`, in the dispatch's form** (`D = v₃ − v₂`, `D ∣ v₃`). -/
theorem lonely_6_native_branch {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3)
    (h34 : v3 < v4) (h45 : v4 < v5) (hsmall : 3 * v1 < v3) (hD3 : (v3 - v2) ∣ v3)
    (hD : 15 ≤ v3 - v2) (hcop : Nat.Coprime v1 (v3 - v2)) :
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
    s6_branch h0 h34 h45 (show 1 ≤ e - 1 by omega) hv2 hv3 hsmall hcop hD
  obtain ⟨m, hm⟩ := exists_nat_gt (-s)
  have key : ∀ v : ℕ, circDist ((v : ℝ) * (s + ((m + 1 : ℕ) : ℝ))) = circDist ((v : ℝ) * s) := by
    intro v
    have e' : (v : ℝ) * (s + ((m + 1 : ℕ) : ℝ)) = (v : ℝ) * s + ((v * (m + 1) : ℕ) : ℤ) := by push_cast; ring
    rw [e', s8_circDist_add_int]
  refine ⟨s + ((m + 1 : ℕ) : ℝ), by push_cast; linarith, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [key, one_div] <;> assumption

end LRC.S6Native
