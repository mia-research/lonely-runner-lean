import LonelyRunner.LRC.Spec.OrderFiveN

/-!
# Order five: the last sub-case, in the framework's own mechanisms

2026-09-24.  `lonely_five_or_residual` leaves one sub-case at order five: exactly one disparity
`e` divisible by `5`, and it is not the largest.  Write `F` for the largest.  The classical proof
(Bienia et al. 1998, §4) settles it; here each of its steps is a mechanism the framework already
has.

1. **Units of `ℤ/F`.**  On the fastest runner's lap points `K/F`, another runner sits at
   `(d·K mod F)/F`.  Taking `K ≡ v₃⁻¹ (mod F)` puts `v₃` one step out and `e` at least two
   (`exists_time_coprime`).
2. **A change of scale.**  Multiplying the lap index by `m` scales every position by `m` while it
   stays within half a lap; the least `m` with `m·δₑ ≥ 1/5` makes `e` clear and leaves `v₃`
   inside `1/5`.
3. **The shift budget.**  Shifting by `k/5`: the fastest runner, on a lap point, blocks only
   `k = 0`; `e`, a multiple of `5`, does not move; `v₃`, inside `1/5`, blocks one further shift at
   most; the fourth runner at most two.  Four shifts, at most three blocked
   (`exists_fifth_shift`).
4. **A common divisor `g = gcd(F, v₃) > 1`** is the same shift argument with divisor `g`: the
   steps `K/g` move only the runners `g` does not divide, by at most half a lap each time
   (`exists_step_clear`).

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.OrderFiveN

open MomentIterationN LRC.SpecN LRC.Descent ConstructionN

/-- A point in the band `[K + 1/5, K + 4/5]` is clear at `1/5`. -/
theorem fifth_le_circDist_of_band {z : ℝ} (K : ℤ) (h1 : (K : ℝ) + 1 / 5 ≤ z)
    (h2 : z ≤ (K : ℝ) + 4 / 5) : (1 / 5 : ℝ) ≤ circDist z := by
  obtain ⟨K', hK'⟩ := circDist_eq_abs_sub_some_int z
  rw [hK']
  rcases le_or_gt K' K with h | h
  · have : (K' : ℝ) ≤ K := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]; linarith
  · have : (K : ℝ) + 1 ≤ K' := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]; linarith

/-- Within half a lap of an integer, that integer is the nearest. -/
theorem circDist_eq_of_abs_le_half {z : ℝ} {L : ℤ} (h : |z - L| ≤ 1 / 2) :
    circDist z = |z - L| := by
  apply le_antisymm (circDist_le_abs_sub_int z L)
  obtain ⟨K, hK⟩ := circDist_eq_abs_sub_some_int z
  rw [hK]
  by_cases hKL : K = L
  · rw [hKL]
  · have h1 : (1 : ℝ) ≤ |(K : ℝ) - L| := by
      have : (1 : ℤ) ≤ |K - L| := Int.one_le_abs (sub_ne_zero.mpr hKL)
      exact_mod_cast this
    have htri : |(K : ℝ) - L| ≤ |z - K| + |z - L| := by
      calc |(K : ℝ) - L| = |(z - L) - (z - K)| := by ring_nf
        _ ≤ |z - L| + |z - K| := abs_sub _ _
        _ = |z - K| + |z - L| := add_comm _ _
    linarith

/-- **Steps of at most half a lap reach the band.**  From any reading, repeated steps of size
`s ∈ (0, 1/2]` land in `[K + 1/5, K + 4/5]` for some `K`. -/
theorem exists_step_clear (y s : ℝ) (hs0 : 0 < s) (hs : s ≤ 1 / 2) :
    ∃ i : ℕ, (1 / 5 : ℝ) ≤ circDist (y + i * s) := by
  obtain ⟨K, hK⟩ := circDist_eq_abs_sub_some_int y
  by_cases h0 : (1 / 5 : ℝ) ≤ circDist y
  · exact ⟨0, by simpa using h0⟩
  · push Not at h0
    rw [hK] at h0
    have hy := abs_lt.mp h0
    have hx0 : 0 ≤ ((K : ℝ) + 1 / 5 - y) / s := div_nonneg (by linarith) hs0.le
    refine ⟨⌈((K : ℝ) + 1 / 5 - y) / s⌉₊, fifth_le_circDist_of_band K ?_ ?_⟩
    · have := Nat.le_ceil (((K : ℝ) + 1 / 5 - y) / s)
      rw [div_le_iff₀ hs0] at this; linarith
    · have hc := Nat.ceil_lt_add_one hx0
      have h' : (⌈((K : ℝ) + 1 / 5 - y) / s⌉₊ : ℝ) * s < ((K : ℝ) + 1 / 5 - y) + s := by
        have := mul_lt_mul_of_pos_right hc hs0
        rwa [add_mul, div_mul_cancel₀ _ hs0.ne', one_mul] at this
      linarith

/-- A shift `k ∈ {1,2,3,4}` moves a non-multiple of `5` off the lap line. -/
theorem not_dvd_five_mul {F k : ℕ} (hF : ¬ 5 ∣ F) (hk0 : k ≠ 0) (hk5 : k < 5) :
    ¬ ((5 : ℕ) : ℤ) ∣ ((F * k : ℕ) : ℤ) := by
  intro h
  have h' : 5 ∣ F * k := by exact_mod_cast h
  have hF' : F % 5 ≠ 0 := fun h0 => hF (Nat.dvd_of_mod_eq_zero h0)
  have hm : (F * k) % 5 = 0 := Nat.mod_eq_zero_of_dvd h'
  rw [Nat.mul_mod] at hm
  have hFlt : F % 5 < 5 := Nat.mod_lt _ (by norm_num)
  rw [Nat.mod_eq_of_lt hk5] at hm
  interval_cases hr : F % 5 <;> interval_cases k <;> simp_all

/-- **The shift by fifths.**  At `t`, let the fastest runner `F` sit on a lap point, let `e`
(a multiple of `5`) be clear, and let `v₃` be inside `1/5`.  Then some shift `t + k/5`, `k < 5`,
is lonely for `F, e, v₃, v₄`. -/
theorem exists_fifth_shift {F e v3 v4 : ℕ} {t : ℝ} (hFt : ∃ z : ℤ, (F : ℝ) * t = z)
    (hF5 : ¬ 5 ∣ F) (he5 : 5 ∣ e) (het : (1 / 5 : ℝ) ≤ circDist ((e : ℝ) * t))
    (h3 : ¬ 5 ∣ v3) (h3t : circDist ((v3 : ℝ) * t) < 1 / 5) (h4 : ¬ 5 ∣ v4) :
    ∃ k : ℕ, k < 5 ∧ ∀ d ∈ ({F, e, v3, v4} : Finset ℕ),
      (1 / 5 : ℝ) ≤ circDist ((d : ℝ) * (t + k / 5)) := by
  classical
  have h55 : ((5 : ℕ) : ℝ) = 5 := by norm_num
  set B3 := (Finset.range 5).filter
    (fun k : ℕ => circDist ((v3 : ℝ) * t + (v3 : ℝ) * (k : ℝ) / ((5 : ℕ) : ℝ)) < ((5 : ℕ) : ℝ)⁻¹)
    with hB3
  set B4 := (Finset.range 5).filter
    (fun k : ℕ => circDist ((v4 : ℝ) * t + (v4 : ℝ) * (k : ℝ) / ((5 : ℕ) : ℝ)) < ((5 : ℕ) : ℝ)⁻¹)
    with hB4
  have hc3 : B3.card ≤ 2 := by
    have := card_bad_le (n := 5) (by norm_num) ((v3 : ℝ) * t) v3
    rwa [gcd_five_of_not_dvd h3] at this
  have hc4 : B4.card ≤ 2 := by
    have := card_bad_le (n := 5) (by norm_num) ((v4 : ℝ) * t) v4
    rwa [gcd_five_of_not_dvd h4] at this
  have h03 : 0 ∈ B3 := by
    rw [hB3, Finset.mem_filter, Finset.mem_range]
    refine ⟨by norm_num, ?_⟩
    simpa [h55] using h3t
  have hU : (B3 ∪ B4).card < (Finset.range 5).card := by
    rw [Finset.card_range]
    have := Finset.card_union_le B3 B4
    omega
  obtain ⟨k, hk, hkU⟩ := Finset.exists_mem_notMem_of_card_lt_card hU
  have hk5 : k < 5 := Finset.mem_range.mp hk
  have hk0 : k ≠ 0 := fun h => hkU (Finset.mem_union_left _ (h ▸ h03))
  have hk3 : k ∉ B3 := fun h => hkU (Finset.mem_union_left _ h)
  have hk4 : k ∉ B4 := fun h => hkU (Finset.mem_union_right _ h)
  refine ⟨k, hk5, fun d hd => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · -- the fastest runner, off its lap point by `F·k/5`
    obtain ⟨z, hz⟩ := hFt
    have heq : (d : ℝ) * (t + k / 5) = (((d * k : ℕ) : ℤ) : ℝ) / ((5 : ℕ) : ℝ) + z := by
      rw [mul_add, hz]; push_cast; ring
    rw [heq, circDist_add_int]
    have := circDist_int_div (n := 5) (by norm_num) (not_dvd_five_mul hF5 hk0 hk5)
    simpa using this
  · -- the multiple of five does not move
    obtain ⟨q, rfl⟩ := he5
    have heq : ((5 * q : ℕ) : ℝ) * (t + k / 5) = ((5 * q : ℕ) : ℝ) * t + (((q * k : ℕ) : ℤ) : ℝ) := by
      push_cast; ring
    rw [heq, circDist_add_int]
    exact het
  · have hnot : ¬ circDist ((d : ℝ) * t + (d : ℝ) * (k : ℝ) / ((5 : ℕ) : ℝ)) < ((5 : ℕ) : ℝ)⁻¹ :=
      fun h => hk3 (Finset.mem_filter.mpr ⟨hk, h⟩)
    have heq : (d : ℝ) * (t + k / 5) = (d : ℝ) * t + (d : ℝ) * (k : ℝ) / ((5 : ℕ) : ℝ) := by
      rw [h55]; ring
    rw [heq]
    push Not at hnot
    simpa using hnot
  · have hnot : ¬ circDist ((d : ℝ) * t + (d : ℝ) * (k : ℝ) / ((5 : ℕ) : ℝ)) < ((5 : ℕ) : ℝ)⁻¹ :=
      fun h => hk4 (Finset.mem_filter.mpr ⟨hk, h⟩)
    have heq : (d : ℝ) * (t + k / 5) = (d : ℝ) * t + (d : ℝ) * (k : ℝ) / ((5 : ℕ) : ℝ) := by
      rw [h55]; ring
    rw [heq]
    push Not at hnot
    simpa using hnot

/-- **Units of `ℤ/F`, then a change of scale.**  With `v₃` coprime to `F`, name the lap point
`α/F`, `α ≡ v₃⁻¹ (mod F)`: `v₃` sits one step out, `e` at least two.  Scaling the lap index by
the least `m` with `m·δₑ ≥ 1/5` makes `e` clear while `v₃` stays inside `1/5`. -/
theorem exists_time_coprime {F e v3 : ℕ} (hF6 : 6 ≤ F) (he : 0 < e) (heF : e < F)
    (hv3F : v3 < F) (hev3 : e ≠ v3) (hsum : e + v3 ≠ F) (hcop : Nat.Coprime v3 F) :
    ∃ t : ℝ, 0 < t ∧ (∃ z : ℤ, (F : ℝ) * t = z) ∧ (1 / 5 : ℝ) ≤ circDist ((e : ℝ) * t) ∧
      circDist ((v3 : ℝ) * t) < 1 / 5 := by
  obtain ⟨α, -, hα⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (show 1 < F by omega)
  have hF0 : (0 : ℝ) < F := by exact_mod_cast (show 0 < F by omega)
  have hFz : (0 : ℤ) < F := by exact_mod_cast (show 0 < F by omega)
  have hα0 : 0 < α := by
    rcases Nat.eq_zero_or_pos α with h | h
    · rw [h, mul_zero, Nat.zero_mod] at hα; exact absurd hα (by norm_num)
    · exact h
  set q := v3 * α / F with hq
  have hvq : v3 * α = F * q + 1 := by
    have := Nat.div_add_mod (v3 * α) F; rw [hα, ← hq] at this; linarith
  have hvqz : ((v3 : ℤ) * α) = F * q + 1 := by exact_mod_cast hvq
  have hαcop : IsCoprime (F : ℤ) (α : ℤ) := ⟨-(q : ℤ), (v3 : ℤ), by linarith⟩
  -- the position of `e` at the lap point `α/F`
  set y : ℝ := (e : ℝ) * ((α : ℝ) / F) with hy
  obtain ⟨K, hK⟩ := circDist_eq_abs_sub_some_int y
  set c : ℤ := (e : ℤ) * α - F * K with hc
  have hyc : y - K = (c : ℝ) / F := by rw [hy, hc]; push_cast; field_simp
  have heFz : (e : ℤ) < F := by exact_mod_cast heF
  have hez : (0 : ℤ) < e := by exact_mod_cast he
  have hv3z : (v3 : ℤ) < F := by exact_mod_cast hv3F
  have hv3z0 : (0 : ℤ) ≤ v3 := by positivity
  -- at least two steps from the lap line: `c ≠ 0, ±1`
  have hc2 : (2 : ℤ) ≤ |c| := by
    by_contra hlt
    push Not at hlt
    have hcases : c = 0 ∨ c = 1 ∨ c = -1 := by have := abs_lt.mp hlt; omega
    rcases hcases with h0 | h1 | hm1
    · have hdvd : (F : ℤ) ∣ (e : ℤ) * α := ⟨K, by rw [hc] at h0; linarith⟩
      have := Int.le_of_dvd hez (hαcop.dvd_of_dvd_mul_right hdvd)
      linarith
    · have hdvd : (F : ℤ) ∣ ((e : ℤ) - v3) * α := ⟨K - q, by rw [hc] at h1; linarith⟩
      obtain ⟨w, hw⟩ := hαcop.dvd_of_dvd_mul_right hdvd
      have hw0 : w = 0 := by
        rcases lt_trichotomy w 0 with h | h | h
        · have : (F : ℤ) * w ≤ -F := by nlinarith
          linarith
        · exact h
        · have : (F : ℤ) ≤ F * w := by nlinarith
          linarith
      rw [hw0, mul_zero] at hw
      exact hev3 (by omega)
    · have hdvd : (F : ℤ) ∣ ((e : ℤ) + v3) * α := ⟨K + q, by rw [hc] at hm1; linarith⟩
      obtain ⟨w, hw⟩ := hαcop.dvd_of_dvd_mul_right hdvd
      have hw1 : w = 1 := by
        rcases lt_trichotomy w 1 with h | h | h
        · have : w ≤ 0 := by omega
          have : (F : ℤ) * w ≤ 0 := by nlinarith
          linarith
        · exact h
        · have : w ≥ 2 := by omega
          have : 2 * (F : ℤ) ≤ F * w := by nlinarith
          linarith
      rw [hw1, mul_one] at hw
      exact hsum (by omega)
  set δ := circDist y with hδdef
  have hδ : δ = |y - K| := hK
  have hδ2 : 2 / (F : ℝ) ≤ δ := by
    rw [hδ, hyc, abs_div, abs_of_pos hF0]
    have : (2 : ℝ) ≤ |(c : ℝ)| := by exact_mod_cast hc2
    exact div_le_div_of_nonneg_right this hF0.le
  have hδ0 : 0 < δ := lt_of_lt_of_le (by positivity) hδ2
  have hδhalf : δ ≤ 1 / 2 := circDist.le_half y
  -- the scaled lap point `m·α/F`
  have finish : ∀ m : ℕ, (1 / 5 : ℝ) ≤ m * δ → (m : ℝ) * δ ≤ 1 / 2 → (m : ℝ) / F < 1 / 5 →
      ∃ t : ℝ, 0 < t ∧ (∃ z : ℤ, (F : ℝ) * t = z) ∧ (1 / 5 : ℝ) ≤ circDist ((e : ℝ) * t) ∧
        circDist ((v3 : ℝ) * t) < 1 / 5 := by
    intro m hlo hhi hv
    have hm0 : (0 : ℝ) < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h] at hlo; simp at hlo; linarith
      · exact_mod_cast h
    refine ⟨m * ((α : ℝ) / F), by positivity, ⟨((m * α : ℕ) : ℤ), by push_cast; field_simp⟩, ?_, ?_⟩
    · have heq : (e : ℝ) * (m * ((α : ℝ) / F)) = m * y := by rw [hy]; ring
      have habs : |(m : ℝ) * y - (((m : ℤ) * K : ℤ) : ℝ)| = m * δ := by
        rw [hδ]; push_cast; rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
      rw [heq, circDist_eq_of_abs_le_half (L := (m : ℤ) * K) (by rw [habs]; exact hhi), habs]
      exact hlo
    · have heq : (v3 : ℝ) * (m * ((α : ℝ) / F)) = (m : ℝ) / F + (((m * q : ℕ) : ℤ) : ℝ) := by
        have hv : (v3 : ℝ) * α = F * q + 1 := by exact_mod_cast hvq
        rw [show (v3 : ℝ) * (m * ((α : ℝ) / F)) = (m : ℝ) * ((v3 : ℝ) * α) / F by ring, hv]
        push_cast
        field_simp
        ring
      rw [heq, circDist_add_int]
      calc circDist ((m : ℝ) / F) ≤ |(m : ℝ) / F - ((0 : ℤ) : ℝ)| := circDist_le_abs_sub_int _ 0
        _ = (m : ℝ) / F := by rw [Int.cast_zero, sub_zero, abs_of_nonneg (by positivity)]
        _ < 1 / 5 := hv
  by_cases hbig : (1 / 5 : ℝ) ≤ δ
  · apply finish 1 (by simpa using hbig) (by simpa using hδhalf)
    rw [Nat.cast_one, div_lt_div_iff₀ hF0 (by norm_num)]
    have : (6 : ℝ) ≤ F := by exact_mod_cast hF6
    linarith
  · push Not at hbig
    set m := ⌈(1 / 5 : ℝ) / δ⌉₊ with hm
    have hx0 : 0 ≤ (1 / 5 : ℝ) / δ := by positivity
    have hlo : (1 / 5 : ℝ) ≤ m * δ := by
      have := Nat.le_ceil ((1 / 5 : ℝ) / δ)
      rwa [div_le_iff₀ hδ0] at this
    have hup : (m : ℝ) * δ < 1 / 5 + δ := by
      have hc := Nat.ceil_lt_add_one hx0
      have := mul_lt_mul_of_pos_right hc hδ0
      rwa [add_mul, div_mul_cancel₀ _ hδ0.ne', one_mul] at this
    apply finish m hlo (by linarith)
    have h1F : 1 / (F : ℝ) ≤ δ / 2 := by
      rw [div_le_iff₀ hF0]; have := hδ2; rw [div_le_iff₀ hF0] at this; linarith
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    calc (m : ℝ) / F = m * (1 / F) := by ring
      _ ≤ m * (δ / 2) := mul_le_mul_of_nonneg_left h1F hm0
      _ < 1 / 5 := by nlinarith

/-- **A common divisor `g` of `F` and `v₃` that misses `e`.**  At the points `K/g`, `F` and `v₃`
are on lap lines, and the steps move `e` by `gcd(e, g)/g ≤ 1/2`, so one lands `e` in the band. -/
theorem exists_time_common {F e v3 : ℕ} (g : ℕ) (hg : 2 ≤ g) (hgF : g ∣ F) (hgv : g ∣ v3)
    (hge : ¬ g ∣ e) :
    ∃ t : ℝ, 0 < t ∧ (∃ z : ℤ, (F : ℝ) * t = z) ∧ (1 / 5 : ℝ) ≤ circDist ((e : ℝ) * t) ∧
      circDist ((v3 : ℝ) * t) < 1 / 5 := by
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  set h := Nat.gcd e g with hh
  have hhg : h < g := by
    have hle : h ≤ g := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right e g)
    rcases Nat.lt_or_ge h g with hl | hl
    · exact hl
    · exfalso; apply hge; have : h = g := le_antisymm hle hl
      rw [← this]; exact Nat.gcd_dvd_left e g
  have hh0 : 0 < h := Nat.gcd_pos_of_pos_right e (by omega)
  have h2h : 2 * h ≤ g := by
    obtain ⟨r, hr⟩ := Nat.gcd_dvd_right e g
    have : 2 ≤ r := by
      rcases Nat.lt_or_ge r 2 with h' | h'
      · interval_cases r <;> omega
      · exact h'
    rw [← hh] at hr; nlinarith
  obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_gcd (k := g) (n := e) hhg
  -- `e·a = g·w + h`
  set w := e * a / g with hw
  have hea : e * a = g * w + h := by
    have := Nat.div_add_mod (e * a) g; rw [ha, ← hw] at this; linarith
  set s : ℝ := (h : ℝ) / g with hs
  have hs0 : 0 < s := by positivity
  have hs2 : s ≤ 1 / 2 := by
    rw [hs, div_le_iff₀ hg0]; have : (2 * h : ℝ) ≤ g := by exact_mod_cast h2h
    linarith
  obtain ⟨i, hi⟩ := exists_step_clear 0 s hs0 hs2
  obtain ⟨F', rfl⟩ := hgF
  obtain ⟨v', rfl⟩ := hgv
  set t : ℝ := ((i * a : ℕ) : ℝ) / g + 1 with ht
  refine ⟨t, by positivity, ⟨((F' * (i * a) + g * F' : ℕ) : ℤ), ?_⟩, ?_, ?_⟩
  · rw [ht]; push_cast; field_simp
  · have heq : (e : ℝ) * t = 0 + i * s + (((i * w + e : ℕ) : ℤ) : ℝ) := by
      have hv : (e : ℝ) * a = g * w + h := by exact_mod_cast hea
      rw [ht, hs]; push_cast
      rw [show (e : ℝ) * ((i : ℝ) * a / g + 1) = (i : ℝ) * ((e : ℝ) * a) / g + e by ring, hv]
      field_simp
      ring
    rw [heq, circDist_add_int]; exact hi
  · have heq : ((g * v' : ℕ) : ℝ) * t = (((v' * (i * a) + g * v' : ℕ) : ℤ) : ℝ) := by
      rw [ht]; push_cast; field_simp
    rw [heq, circDist_intCast']; norm_num

/-- **A common divisor `g` of `F, e, v₃` that misses `v₄`.**  The three are settled together
first; then the steps `K/g` leave them on their readings and move `v₄` alone, by
`gcd(v₄, g)/g ≤ 1/2`, into the band. -/
theorem lonely_of_common_divisor {F e v3 v4 : ℕ} (g : ℕ) (hg : 2 ≤ g) (hgF : g ∣ F)
    (hge : g ∣ e) (hgv : g ∣ v3) (hg4 : ¬ g ∣ v4) (hF : 0 < F) (he : 0 < e) (hv3 : 0 < v3) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ ({F, e, v3, v4} : Finset ℕ), (1 / 5 : ℝ) ≤ circDist ((d : ℝ) * t) := by
  classical
  obtain ⟨τ, hτ, hl⟩ := lonely_five_of_card_le_three (S := {F, e, v3})
    (by intro d hd; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl <;> assumption)
    Finset.card_le_three
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  set h := Nat.gcd v4 g with hh
  have hhg : h < g := by
    have hle : h ≤ g := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right v4 g)
    rcases Nat.lt_or_ge h g with hl' | hl'
    · exact hl'
    · exfalso; apply hg4; have : h = g := le_antisymm hle hl'
      rw [← this]; exact Nat.gcd_dvd_left v4 g
  have hh0 : 0 < h := Nat.gcd_pos_of_pos_right v4 (by omega)
  have h2h : 2 * h ≤ g := by
    obtain ⟨r, hr⟩ := Nat.gcd_dvd_right v4 g
    have : 2 ≤ r := by
      rcases Nat.lt_or_ge r 2 with h' | h'
      · interval_cases r <;> omega
      · exact h'
    rw [← hh] at hr; nlinarith
  obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_gcd (k := g) (n := v4) hhg
  set w := v4 * a / g with hw
  have hva : v4 * a = g * w + h := by
    have := Nat.div_add_mod (v4 * a) g; rw [ha, ← hw] at this; linarith
  set s : ℝ := (h : ℝ) / g with hs
  have hs0 : 0 < s := by positivity
  have hs2 : s ≤ 1 / 2 := by
    rw [hs, div_le_iff₀ hg0]; have : (2 * h : ℝ) ≤ g := by exact_mod_cast h2h
    linarith
  obtain ⟨i, hi⟩ := exists_step_clear ((v4 : ℝ) * τ) s hs0 hs2
  refine ⟨τ + ((i * a : ℕ) : ℝ) / g, by positivity, fun d hd => ?_⟩
  -- the three multiples of `g` keep their readings
  have hkeep : ∀ d ∈ ({F, e, v3} : Finset ℕ), g ∣ d →
      (1 / 5 : ℝ) ≤ circDist ((d : ℝ) * (τ + ((i * a : ℕ) : ℝ) / g)) := by
    intro d hd hgd
    obtain ⟨d', rfl⟩ := hgd
    have heq : ((g * d' : ℕ) : ℝ) * (τ + ((i * a : ℕ) : ℝ) / g)
        = ((g * d' : ℕ) : ℝ) * τ + (((d' * (i * a) : ℕ) : ℤ) : ℝ) := by
      push_cast; field_simp
    rw [heq, circDist_add_int]
    have := hl _ hd
    simpa using this
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · exact hkeep _ (by simp) hgF
  · exact hkeep _ (by simp) hge
  · exact hkeep _ (by simp) hgv
  · have heq : (d : ℝ) * (τ + ((i * a : ℕ) : ℝ) / g) = (d : ℝ) * τ + i * s + (((i * w : ℕ) : ℤ) : ℝ) := by
      have hv : (d : ℝ) * a = g * w + h := by exact_mod_cast hva
      rw [hs]; push_cast
      rw [show (d : ℝ) * (τ + (i : ℝ) * a / g) = (d : ℝ) * τ + (i : ℝ) * ((d : ℝ) * a) / g by ring, hv]
      field_simp
      ring
    rw [heq, circDist_add_int]; exact hi

/-- **The last sub-case at order five.**  At most four positive disparities with no common
divisor above one, exactly one of them `e` divisible by `5`, and `e` not the largest: lonely at
`1/5`. -/
theorem lonely_five_residual {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) (hcard : S.card ≤ 4)
    (hprim : ∀ g, 2 ≤ g → ∃ d ∈ S, ¬ g ∣ d) {e : ℕ} (heS : e ∈ S) (he5 : 5 ∣ e)
    (hothers : ∀ d ∈ S, d ≠ e → ¬ 5 ∣ d) (hbig : ∃ d ∈ S, e < d) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (5 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  have h15 : (5 : ℝ)⁻¹ = 1 / 5 := by norm_num
  rcases Nat.lt_or_ge S.card 4 with hc3 | hc4
  · exact lonely_five_of_card_le_three hpos (by omega)
  have hc4' : S.card = 4 := by omega
  have hne : S.Nonempty := ⟨e, heS⟩
  set F := S.max' hne with hFdef
  have hFS : F ∈ S := S.max'_mem hne
  have hFmax : ∀ d ∈ S, d ≤ F := fun d hd => S.le_max' d hd
  have heF : e < F := by obtain ⟨d, hd, hed⟩ := hbig; exact lt_of_lt_of_le hed (hFmax d hd)
  have hFe : F ≠ e := by omega
  have hF5 : ¬ 5 ∣ F := hothers F hFS hFe
  have he0 : 0 < e := hpos e heS
  have he5' : 5 ≤ e := Nat.le_of_dvd he0 he5
  -- the other two
  set T := (S.erase F).erase e with hT
  have hTcard : T.card = 2 := by
    rw [hT, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hFe.symm, heS⟩),
      Finset.card_erase_of_mem hFS]; omega
  obtain ⟨a, b, hab, hTab⟩ := Finset.card_eq_two.mp hTcard
  have hmemT : ∀ x ∈ T, x ∈ S ∧ x ≠ F ∧ x ≠ e := by
    intro x hx
    obtain ⟨hxe, hx'⟩ := Finset.mem_erase.mp hx
    obtain ⟨hxF, hxS⟩ := Finset.mem_erase.mp hx'
    exact ⟨hxS, hxF, hxe⟩
  have haT : a ∈ T := by rw [hTab]; simp
  have hbT : b ∈ T := by rw [hTab]; simp
  obtain ⟨haS, haF, hae⟩ := hmemT a haT
  obtain ⟨hbS, hbF, hbe⟩ := hmemT b hbT
  -- every member of `S` is `F`, `e`, `a` or `b`
  have hcover : ∀ d ∈ S, d = F ∨ d = e ∨ d = a ∨ d = b := by
    intro d hd
    by_cases h1 : d = F
    · exact Or.inl h1
    by_cases h2 : d = e
    · exact Or.inr (Or.inl h2)
    have : d ∈ T := Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, hd⟩⟩
    rw [hTab] at this; simp at this
    rcases this with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  -- choose `v₃` with `e + v₃ ≠ F`
  obtain ⟨v3, v4, hv34, hsum⟩ : ∃ v3 v4 : ℕ, ((v3 = a ∧ v4 = b) ∨ (v3 = b ∧ v4 = a)) ∧ e + v3 ≠ F := by
    by_cases h : e + a = F
    · exact ⟨b, a, Or.inr ⟨rfl, rfl⟩, by omega⟩
    · exact ⟨a, b, Or.inl ⟨rfl, rfl⟩, h⟩
  have hv3S : v3 ∈ S ∧ v3 ≠ F ∧ v3 ≠ e := by rcases hv34 with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> tauto
  have hv4S : v4 ∈ S ∧ v4 ≠ F ∧ v4 ≠ e := by rcases hv34 with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> tauto
  have h35 : ¬ 5 ∣ v3 := hothers v3 hv3S.1 hv3S.2.2
  have h45 : ¬ 5 ∣ v4 := hothers v4 hv4S.1 hv4S.2.2
  have hv3F : v3 < F := lt_of_le_of_ne (hFmax v3 hv3S.1) hv3S.2.1
  have hv30 : 0 < v3 := hpos v3 hv3S.1
  have hF0 : 0 < F := hpos F hFS
  have hev3 : e ≠ v3 := fun h => h35 (h ▸ he5)
  -- the lonely instant for `F, e, v₃, v₄`
  have key : ∃ t : ℝ, 0 < t ∧ ∀ d ∈ ({F, e, v3, v4} : Finset ℕ), (1 / 5 : ℝ) ≤ circDist ((d : ℝ) * t) := by
    have shift : ∀ t : ℝ, 0 < t → (∃ z : ℤ, (F : ℝ) * t = z) → (1 / 5 : ℝ) ≤ circDist ((e : ℝ) * t) →
        circDist ((v3 : ℝ) * t) < 1 / 5 →
        ∃ t : ℝ, 0 < t ∧ ∀ d ∈ ({F, e, v3, v4} : Finset ℕ), (1 / 5 : ℝ) ≤ circDist ((d : ℝ) * t) := by
      intro t ht hFt het h3t
      obtain ⟨k, -, hk⟩ := exists_fifth_shift hFt hF5 he5 het h35 h3t h45
      exact ⟨t + k / 5, by positivity, hk⟩
    set g := Nat.gcd v3 F with hg
    have hg0 : 0 < g := Nat.gcd_pos_of_pos_right v3 hF0
    rcases Nat.lt_or_ge g 2 with hg1 | hg2
    · have hcop : Nat.Coprime v3 F := by unfold Nat.Coprime; omega
      obtain ⟨t, ht, hFt, het, h3t⟩ := exists_time_coprime (by omega) he0 heF hv3F hev3 hsum hcop
      exact shift t ht hFt het h3t
    · by_cases hge : g ∣ e
      · by_cases hg4 : g ∣ v4
        · exfalso
          obtain ⟨d, hd, hnd⟩ := hprim g hg2
          apply hnd
          rcases hcover d hd with h | h | h | h <;> rw [h]
          · exact Nat.gcd_dvd_right v3 F
          · exact hge
          · rcases hv34 with ⟨h3, h4⟩ | ⟨h3, h4⟩
            · rw [← h3]; exact Nat.gcd_dvd_left v3 F
            · rw [← h4]; exact hg4
          · rcases hv34 with ⟨h3, h4⟩ | ⟨h3, h4⟩
            · rw [← h4]; exact hg4
            · rw [← h3]; exact Nat.gcd_dvd_left v3 F
        · exact lonely_of_common_divisor g hg2 (Nat.gcd_dvd_right v3 F) hge (Nat.gcd_dvd_left v3 F)
            hg4 hF0 he0 hv30
      · obtain ⟨t, ht, hFt, het, h3t⟩ :=
          exists_time_common g hg2 (Nat.gcd_dvd_right v3 F) (Nat.gcd_dvd_left v3 F) hge
        exact shift t ht hFt het h3t
  obtain ⟨t, ht, hl⟩ := key
  refine ⟨t, ht, fun d hd => ?_⟩
  rw [h15]
  apply hl
  rcases hcover d hd with rfl | rfl | rfl | rfl
  · simp
  · simp
  · rcases hv34 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · rcases hv34 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-- **Order five, whole numbers, by descent on the sum.** -/
theorem lonely_five_nat_aux : ∀ N : ℕ, ∀ S : Finset ℕ, (∑ d ∈ S, d) = N → (∀ d ∈ S, 0 < d) →
    S.card ≤ 4 → ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (5 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro S hN hpos hcard
    classical
    by_cases hdiv : ∃ g, 2 ≤ g ∧ ∀ d ∈ S, g ∣ d
    · obtain ⟨g, hg, hgd⟩ := hdiv
      rcases Finset.eq_empty_or_nonempty S with rfl | hne
      · exact ⟨1, by norm_num, by simp⟩
      have hinj : Set.InjOn (fun d => d / g) (S : Set ℕ) := by
        intro x hx y hy hxy
        simp only at hxy
        rw [← Nat.div_mul_cancel (hgd x hx), ← Nat.div_mul_cancel (hgd y hy), hxy]
      have hsum' : ∑ d ∈ S.image (fun d => d / g), d < N := by
        rw [Finset.sum_image hinj, ← hN]
        apply Finset.sum_lt_sum_of_nonempty hne
        intro d hd
        exact Nat.div_lt_self (hpos d hd) (by omega)
      obtain ⟨τ, hτ, hl⟩ := ih _ hsum' (S.image (fun d => d / g)) rfl
        (by
          intro x hx
          obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
          exact Nat.div_pos (Nat.le_of_dvd (hpos d hd) (hgd d hd)) (by omega))
        (le_trans Finset.card_image_le hcard)
      have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
      refine ⟨τ / g, by positivity, fun d hd => ?_⟩
      have := hl (d / g) (Finset.mem_image_of_mem _ hd)
      rw [Nat.cast_div (hgd d hd) hg0, div_mul_eq_mul_div] at this
      rwa [mul_div_assoc] at this
    · push Not at hdiv
      rcases lonely_five_or_residual hpos hcard (hdiv 5 (by norm_num)) with h | ⟨hc1, e, heS, he5, hbig⟩
      · exact h
      · have hothers : ∀ d ∈ S, d ≠ e → ¬ 5 ∣ d := by
          intro d hd hne h5
          obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc1
          have h1 : d ∈ S.filter (fun d => 5 ∣ d) := Finset.mem_filter.mpr ⟨hd, h5⟩
          have h2 : e ∈ S.filter (fun d => 5 ∣ d) := Finset.mem_filter.mpr ⟨heS, he5⟩
          rw [hx, Finset.mem_singleton] at h1 h2
          exact hne (h1.trans h2.symm)
        exact lonely_five_residual hpos hcard hdiv heS he5 hothers hbig

/-- **The conjecture at five runners, for whole-number speeds, inside the framework.**  Every set
of at most four positive whole-number disparities is lonely at `1/5`. -/
theorem lonely_five_nat (S : Finset ℕ) (hpos : ∀ d ∈ S, 0 < d) (hcard : S.card ≤ 4) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (5 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) :=
  lonely_five_nat_aux _ S rfl hpos hcard

/-- **Commensurable real speeds at order five.**  If every disparity is a positive whole multiple
of one unit `u > 0`, the set is lonely at `1/5`: read it in that unit and rescale the instant. -/
theorem lonely_five_commensurable {ds : Finset ℝ} {u : ℝ} (hu : 0 < u) (hcard : ds.card ≤ 4)
    (hcomm : ∀ d ∈ ds, ∃ m : ℕ, 0 < m ∧ d = u * m) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ ds, (5 : ℝ)⁻¹ ≤ circDist (d * t) := by
  classical
  set S : Finset ℕ := ds.image (fun d => ⌊d / u⌋₊) with hS
  have hunit : ∀ d ∈ ds, d = u * (⌊d / u⌋₊ : ℝ) ∧ 0 < ⌊d / u⌋₊ := by
    intro d hd
    obtain ⟨m, hm, rfl⟩ := hcomm d hd
    rw [mul_div_cancel_left₀ _ hu.ne', Nat.floor_natCast]
    exact ⟨rfl, hm⟩
  obtain ⟨τ, hτ, hl⟩ := lonely_five_nat S
    (by
      intro m hm
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hm
      exact (hunit d hd).2)
    (le_trans Finset.card_image_le hcard)
  refine ⟨τ / u, by positivity, fun d hd => ?_⟩
  have h := hl _ (Finset.mem_image_of_mem _ hd)
  have heq : d * (τ / u) = (⌊d / u⌋₊ : ℝ) * τ := by
    conv_lhs => rw [(hunit d hd).1]
    field_simp
  rw [heq]; exact h

end LRC.OrderFiveN
