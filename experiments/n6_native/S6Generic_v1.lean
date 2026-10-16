import LonelyRunner.LRC.Spec.OrderSixEightNativeN

/-!
# §6 near-runner, generic orbits (n6_native, E95)

At the meeting times `k/D` the phases of runners 1 and 4 are `(k v₁ mod D)/D` and `(k δ mod D)/D`, `δ = v₄ − v₃`. With
`gcd(v₁, D) = 1` put `j = k v₁ mod D`; then runner 4's phase is `λ j / D` mod 1, `λ ≡ δ v₁⁻¹`. For `j` over the integers of
`[D/6, 5D/9]` (runner 1 clear across the window) the points `λ j / D` form a progression with step `|λ|/D ≤ 1/2`; when
`|λ| ≥ 2` and `D ≥ 15` its span exceeds `1/2`, so it meets every closed half arc (`ap_meets_half_arc`).
-/

namespace N6Native

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

open LRC.S7Native LRC.S8Native

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

end N6Native


#print axioms N6Native.ap_meets_half_arc
#print axioms N6Native.s6_window_fold
#print axioms N6Native.s6_generic
