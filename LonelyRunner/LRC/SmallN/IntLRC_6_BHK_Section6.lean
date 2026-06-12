import LonelyRunner.LRC.SmallN.IntLRC_6_BHK_Section7

/-!
# BHK §6 — the case `{v₃ t₀} = 0`, `{v₁ t₀} ≠ 0` (reduction + skeleton)

Here runners 2 and 3 are *both* at the origin whenever runner 3 passes
runner 2: with `D := v₃ - v₂` and `t₀ := 1/D`, the hypothesis
`{v₃ t₀} = 0` means `D ∣ v₃`, hence also `D ∣ v₂`, so

* `v₃ = k·D` and `v₂ = (k−1)·D` for some `k ≥ 2` (BHK (58):
  `v₂ = (k−1)/k` in the `v₃ = 1` normalisation), and
* `D ∤ v₁` (from `{v₁ t₀} ≠ 0`), which forces `D ≥ 2`.

The **reduction** (`bhk_s6_main`, PROVED) extracts this arithmetic
structure; the **analytic core** (`bhk_s6_reduced`, OPEN) is BHK
pp. 40–43:

1. **Lemma 22**: an interval `I` with `I ∩ (B₁∪B₂∪B₃) = ∅`,
   `|I| ≥ 1/3`, containing a time `t` with `{v₄t} = 1/2`, yields a
   lonely time (the covering 1234-gap is too long for one 5-block).
2. The 23-gaps after `j·t₀` give intervals
   `I_j = [jt₀ + 2/6, jt₀ + 5/6]` (normalised) avoiding `B₂ ∪ B₃`
   (uses `x₂ ≤ 2`, i.e. `2 v₂ ≥ v₃`, from `k ≥ 2`). Condition (59)
   `1/6 − 2v₁/6 ≤ {v₁ j t₀} ≤ 5/6 − 5v₁/6` makes `I_j ∩ B₁ = ∅`;
   since `x₁ > 3` the window has length `> 1/2` and the nontrivial
   orbit `{v₁ j t₀}` (order `D / gcd(v₁, D) ≥ 2`) hits it.
   Lemma 4 then closes everything unless `x₄ > 3/4` (`3 v₄ > ... `,
   normalised `v₄ < 4/3`).
3. Condition (60) excludes `{v₄ j t₀}` from an arc of length
   `1 − v₄/2 < 1/2`; when it holds, some `t ∈ I_j` has `{v₄ t} = 1/2`
   and Lemma 22 fires.
4. Otherwise apply **Corollary 6** to the cyclic group
   `G = ⟨({v₁ t₀}, {v₄ t₀})⟩` (order `n` divides `D`) and the rectangle
   `R = [1/6 − v₁/3, 5/6 − 5v₁/6] × [9/6 − 5v₄/6, 9/6 − 2v₄/6]`,
   noting `[1/6, 5/9] × [2/3, 1] ⊆ R` (BHK (61)). `G ∩ R ≠ ∅` gives
   (59) + (60) simultaneously. The residual cases are:
   * **6.1** `n₂ = 1` (`n₁ = 1` is impossible since `{v₁t₀} ≠ 0`):
     circle `L₀²` meets `R` in length `2/3 − v₁/2 > 1/2 ≥` period.
   * **6.2** `(1/n, 1/n) ∈ G`, `n ≥ 2`: ad hoc — `γ = {v₁jt₀} =
     {v₄jt₀} ∈ [1/3, 1/2]`; sub-cases `v₂ = 1/2` (Lemma 23:
     `[7/6, 10/6] ⊄ B₄ ∪ B₅`, then `m = 2`, `v₄ = 1 + v₁`) and
     `v₂ ≥ 2/3` (`I = [jt₀ + 1/4, jt₀ + 5/6]` in a 123-gap, `x₄ > 7/8`,
     flanked 4-block, `n = 2` endgame).
   * **6.3** `(1/n, −1/n) ∈ G`: multiples land in `G ∩ R` unless
     `n = 2`, which is Case 6.2.
   * **6.4** `(1/n, 2/n) ∈ G`, `n ≥ 4`: some `j/n ∈ [1/3, 1/2]` always
     exists, giving `j·(1/n, 2/n) ∈ G ∩ R`.
   * **6.5** `(1/n, −2/n) ∈ G`, `n ≥ 4`: `j/n ∈ [1/2, 5/9]` exists
     unless `n ∈ {5, 7}`; **6.5.1** `n = 5` ((62)–(64), `t = 7/6`
     2-block endgame), **6.5.2** `n = 7` (width of `R` > 1/2 forces
     `(1/7, 5/7) ∈ R` or `(4/7, 6/7) ∈ R`).

## Source

T. Bohman, R. Holzman, D. Kleitman, *Six Lonely Runners*, EJC **8**
(2001) R3, §6 (pp. 40–43).
-/

open MeasureTheory Set

namespace BHK

/-- **BHK §6 orbit lemma (PROVED).** If `D ∤ V₁` then the orbit
    `{V₁·j/D}` (j ∈ ℕ) has step `g/D ≤ 1/2` (`g := gcd(D, V₁) ≤ D/2`),
    so it hits every window `[lo, hi] ⊆ [0, 1)` of length `≥ 1/2`. This
    is the "since `{v₁t₀} ≠ 0`, there exists a `j` satisfying (59)"
    step of BHK §6 (the 1-D version of observation (11)). -/
lemma bhk_s6_find_j (V1 D : ℕ) (hD : 0 < D) (hndvd : ¬ D ∣ V1)
    (lo hi : ℝ) (hlo : 0 ≤ lo) (hhi : hi < 1) (hgap : 1 / 2 ≤ hi - lo) :
    ∃ j : ℕ, lo ≤ Int.fract (((V1 * j : ℕ) : ℝ) / D) ∧
      Int.fract (((V1 * j : ℕ) : ℝ) / D) ≤ hi := by
  set g : ℕ := Nat.gcd D V1 with hg_def
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left _ hD
  have hgD : g ∣ D := Nat.gcd_dvd_left D V1
  have hg_lt : g < D := by
    rcases lt_or_eq_of_le (Nat.le_of_dvd hD hgD) with h | h
    · exact h
    · exact absurd (h ▸ Nat.gcd_dvd_right D V1) hndvd
  -- `D = g·D'` with `D' ≥ 2`, so `2g ≤ D`.
  obtain ⟨D', hD'⟩ := hgD
  have hD'2 : 2 ≤ D' := by
    rcases (by omega : D' = 0 ∨ D' = 1 ∨ 2 ≤ D') with rfl | rfl | h
    · rw [mul_zero] at hD'; omega
    · rw [mul_one] at hD'; omega
    · exact h
  have h2g : 2 * g ≤ D := by
    calc 2 * g = g * 2 := by ring
    _ ≤ g * D' := Nat.mul_le_mul_left g hD'2
    _ = D := hD'.symm
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg_pos
  -- Target residue: the smallest multiple of `g` at or above `lo·D`.
  set m : ℕ := ⌈lo * (D : ℝ) / g⌉₊ with hm_def
  have hm_ge : lo * (D : ℝ) / g ≤ m := Nat.le_ceil _
  have hm_lt : (m : ℝ) < lo * (D : ℝ) / g + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hmg_ge : lo * (D : ℝ) ≤ (m : ℝ) * g := by
    rw [div_le_iff₀ hgR] at hm_ge; linarith
  have hmg_le : (m : ℝ) * g ≤ hi * D := by
    have h1 : (m : ℝ) * g < lo * (D : ℝ) + g := by
      have h := mul_lt_mul_of_pos_right hm_lt hgR
      rwa [add_mul, one_mul, div_mul_cancel₀ _ hgR.ne'] at h
    have h2 : (g : ℝ) ≤ (hi - lo) * D := by
      have h2g' : (2 : ℝ) * g ≤ D := by exact_mod_cast h2g
      have h3 := mul_le_mul_of_nonneg_right hgap hDR.le
      linarith
    nlinarith
  have hmg_lt_D : m * g < D := by
    have hreal : ((m * g : ℕ) : ℝ) < (D : ℝ) := by
      push_cast
      have : hi * (D : ℝ) < D := by nlinarith
      linarith
    exact_mod_cast hreal
  -- Bezout: `V₁·t ≡ g (mod D)`; then `j := t·m` lands on `m·g/D`.
  obtain ⟨t, ht⟩ := bhk_s7_bezout_mod D V1 hD
  rw [show Nat.gcd D V1 % D = g from by rw [← hg_def, Nat.mod_eq_of_lt hg_lt]]
    at ht
  refine ⟨t * m, ?_⟩
  have hmod : V1 * (t * m) % D = m * g := by
    rw [show t * m = m * t from mul_comm t m, bhk_s7_mul_mod V1 t m D, ht,
        show g * m = m * g from mul_comm g m, Nat.mod_eq_of_lt hmg_lt_D]
  rw [bhk_fract_nat_div _ D hD, hmod]
  constructor
  · rw [le_div_iff₀ hDR]; push_cast; linarith
  · rw [div_le_iff₀ hDR]; push_cast; linarith

/-- **BHK §6, Lemma 22 (PROVED).** If `[a, b]` is a 123-gap of length at
    least `1/(3 v₃)` (BHK's `|I| ≥ 1/3` in the `v₃ = 1` normalisation)
    containing a time `t` at which runner 4 sits exactly opposite the
    origin (`{v₄ t} = 1/2`), then a lonely time exists.

    Proof: runner 4 is safe on `W = [t − 1/(3v₄), t + 1/(3v₄)]`. One of
    `[t, t + 1/(3v₄)]`, `[t − 1/(3v₄), t]`, `[a, b]` lies inside both
    `[a, b]` and `W` and is longer than one 5-block (`1/(3 v₅)`), so it
    contains a 5-safe point, which is then safe for all five runners. -/
theorem bhk_s6_lemma_22 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (a b : ℝ) (hab : a ≤ b)
    (h123gap : Set.Icc a b ⊆ (unsafeOf speeds ⟨0, by omega⟩ ∪
                              unsafeOf speeds ⟨1, by omega⟩ ∪
                              unsafeOf speeds ⟨2, by omega⟩)ᶜ)
    (hlen : 1 / (3 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ b - a)
    (t : ℝ) (ht : t ∈ Set.Icc a b)
    (h4 : Int.fract ((speeds ⟨3, by omega⟩ : ℝ) * t) = 1 / 2) :
    ∃ t' : ℝ, ∀ i, circDist ((speeds i : ℝ) * t') ≥ (1 : ℝ) / 6 := by
  have hv3pos : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hpos _
  have hv4pos : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by
    exact_mod_cast hpos _
  have hv5pos : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    exact_mod_cast hpos _
  have hv34 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (by omega))
  have hv45 : (speeds ⟨3, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (by omega))
  set v3 : ℝ := (speeds ⟨2, by omega⟩ : ℝ) with hv3_def
  set v4 : ℝ := (speeds ⟨3, by omega⟩ : ℝ) with hv4_def
  set v5 : ℝ := (speeds ⟨4, by omega⟩ : ℝ) with hv5_def
  have hw_pos : (0 : ℝ) < 1 / (3 * v4) := by positivity
  -- Runner 4 is safe throughout `W = [t − 1/(3v₄), t + 1/(3v₄)]`.
  have h4safe : ∀ s ∈ Set.Icc (t - 1 / (3 * v4)) (t + 1 / (3 * v4)),
      s ∉ unsafeOf speeds ⟨3, by omega⟩ := by
    intro s hs hmem
    have hδlo : -(1 / (3 * v4)) ≤ s - t := by
      have := hs.1; linarith
    have hδhi : s - t ≤ 1 / (3 * v4) := by
      have := hs.2; linarith
    have hself : v4 * (1 / (3 * v4)) = 1 / 3 := by field_simp
    have hmlo : -(1 / 3 : ℝ) ≤ v4 * (s - t) := by
      have h := mul_le_mul_of_nonneg_left hδlo hv4pos.le
      rw [mul_neg, hself] at h
      linarith
    have hmhi : v4 * (s - t) ≤ 1 / 3 := by
      have h := mul_le_mul_of_nonneg_left hδhi hv4pos.le
      rw [hself] at h
      linarith
    have h0 : 0 ≤ Int.fract (v4 * t) + v4 * (s - t) := by
      rw [h4]; linarith
    have h1 : Int.fract (v4 * t) + v4 * (s - t) < 1 := by
      rw [h4]; linarith
    have hfs := bhk_fract_translate v4 t (s - t) h0 h1
    rw [show t + (s - t) = s from by ring] at hfs
    rw [mem_unsafeOf_iff] at hmem
    unfold circDist at hmem
    rw [hfs, h4] at hmem
    rcases min_lt_iff.mp hmem with h | h <;> linarith
  -- A sub-interval of `[a, b] ∩ W` longer than one 5-block.
  have h45len : 1 / (3 * v5) < 1 / (3 * v4) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have h35len : 1 / (3 * v5) < 1 / (3 * v3) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  suffices key : ∃ c d : ℝ, c ≤ d ∧ Set.Icc c d ⊆ Set.Icc a b ∧
      (∀ s ∈ Set.Icc c d, s ∉ unsafeOf speeds ⟨3, by omega⟩) ∧
      1 / (3 * v5) < d - c by
    obtain ⟨c, d, hcd, hsubI, h4safe', hlength⟩ := key
    by_cases h5 : ∀ s ∈ Set.Icc c d, s ∈ unsafeOf speeds ⟨4, by omega⟩
    · have hbnd := block_length_bound speeds ⟨4, by omega⟩ (hpos _) c d hcd
        (fun s hs => h5 s hs)
      rw [← hv5_def] at hbnd
      linarith
    · push_neg at h5
      obtain ⟨s, hsI, hs5⟩ := h5
      refine ⟨s, fun i => ?_⟩
      have hs123 := h123gap (hsubI hsI)
      have hs4 := h4safe' s hsI
      have hnot : s ∉ unsafeOf speeds i →
          circDist ((speeds i : ℝ) * s) ≥ 1 / 6 := fun hn =>
        not_lt.mp (fun hlt => hn ((mem_unsafeOf_iff speeds i s).mpr hlt))
      fin_cases i
      · exact hnot (fun h => hs123 (Or.inl (Or.inl h)))
      · exact hnot (fun h => hs123 (Or.inl (Or.inr h)))
      · exact hnot (fun h => hs123 (Or.inr h))
      · exact hnot hs4
      · exact hnot hs5
  by_cases hb : t + 1 / (3 * v4) ≤ b
  · -- Right half-window fits: `[t, t + 1/(3v₄)]`.
    refine ⟨t, t + 1 / (3 * v4), by linarith,
      Set.Icc_subset_Icc ht.1 hb,
      fun s hs => h4safe s ⟨by have := hs.1; linarith, hs.2⟩,
      by linarith⟩
  by_cases ha : a ≤ t - 1 / (3 * v4)
  · -- Left half-window fits: `[t − 1/(3v₄), t]`.
    refine ⟨t - 1 / (3 * v4), t, by linarith,
      Set.Icc_subset_Icc ha ht.2,
      fun s hs => h4safe s ⟨hs.1, by have := hs.2; linarith⟩,
      by linarith⟩
  · -- `[a, b] ⊆ W` entirely.
    push_neg at hb ha
    refine ⟨a, b, hab, subset_rfl,
      fun s hs => h4safe s ⟨by have := hs.1; linarith,
                             by have := hs.2; linarith⟩,
      by linarith⟩

set_option maxHeartbeats 1000000 in
/-- **The §6 123-gap at a given index (PROVED).** If `{v₁ j/D}` satisfies
    the (59)-window, then `[j/D + 1/(3v₃), j/D + 5/(6v₃)]` is a 123-gap:
    runners 2 and 3 have integer positions at `j/D` (ratio
    `v₂/v₃ = (k−1)/k ∈ [1/2, 1)`) and runner 1 stays in `[1/6, 5/6]` by
    the window condition. -/
lemma bhk_s6_123_gap_at (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (D k : ℕ) (hD2 : 2 ≤ D) (hk2 : 2 ≤ k)
    (hv3 : speeds ⟨2, by omega⟩ = k * D)
    (hv2 : speeds ⟨1, by omega⟩ = (k - 1) * D)
    (j : ℕ)
    (hj_lo : 1 / 6 - (speeds ⟨0, by omega⟩ : ℝ) / (3 * speeds ⟨2, by omega⟩)
      ≤ Int.fract (((speeds ⟨0, by omega⟩ * j : ℕ) : ℝ) / D))
    (hj_hi : Int.fract (((speeds ⟨0, by omega⟩ * j : ℕ) : ℝ) / D)
      ≤ 5 / 6 - 5 * (speeds ⟨0, by omega⟩ : ℝ) / (6 * speeds ⟨2, by omega⟩)) :
    Set.Icc ((j : ℝ) / D + 1 / (3 * (speeds ⟨2, by omega⟩ : ℝ)))
            ((j : ℝ) / D + 5 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
      ⊆ (unsafeOf speeds ⟨0, by omega⟩ ∪
         unsafeOf speeds ⟨1, by omega⟩ ∪
         unsafeOf speeds ⟨2, by omega⟩)ᶜ := by
  -- Replace `k` by `k' + 1` to avoid ℕ-subtraction.
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hk'1 : 1 ≤ k' := by omega
  have hV1pos : 0 < speeds ⟨0, by omega⟩ := hpos _
  have hV12 : speeds ⟨0, by omega⟩ < speeds ⟨1, by omega⟩ :=
    hmono (Fin.mk_lt_mk.mpr (by omega))
  have hV23 : speeds ⟨1, by omega⟩ < speeds ⟨2, by omega⟩ :=
    hmono (Fin.mk_lt_mk.mpr (by omega))
  set V1 : ℕ := speeds ⟨0, by omega⟩ with hV1_def
  set V2 : ℕ := speeds ⟨1, by omega⟩ with hV2_def
  set V3 : ℕ := speeds ⟨2, by omega⟩ with hV3_def
  have hv2' : V2 = k' * D := by simpa using hv2
  have hv3' : V3 = (k' + 1) * D := hv3
  have hDpos : 0 < D := by omega
  have hv1R : (0 : ℝ) < V1 := by exact_mod_cast hV1pos
  have hv2R : (0 : ℝ) < V2 := by exact_mod_cast (by omega : 0 < V2)
  have hv3R : (0 : ℝ) < V3 := by exact_mod_cast (by omega : 0 < V3)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hsmallR : 3 * (V1 : ℝ) < V3 := by exact_mod_cast hsmall
  have h2V2 : (V3 : ℝ) ≤ 2 * V2 := by
    have hN : V3 ≤ 2 * V2 := by
      rw [hv3', hv2']
      have hkk : k' + 1 ≤ 2 * k' := by omega
      calc (k' + 1) * D ≤ 2 * k' * D := Nat.mul_le_mul_right D hkk
      _ = 2 * (k' * D) := by ring
    exact_mod_cast hN
  have hV2R_lt : (V2 : ℝ) < V3 := by exact_mod_cast hV23
  set τ : ℝ := (j : ℝ) / D with hτ_def
  intro s hs
  obtain ⟨hsa, hsb⟩ := Set.mem_Icc.mp hs
  have hδlo : 1 / (3 * (V3 : ℝ)) ≤ s - τ := by linarith
  have hδhi : s - τ ≤ 5 / (6 * (V3 : ℝ)) := by linarith
  -- Runner 1: window condition (59).
  have hfr1 : Int.fract ((V1 : ℝ) * τ) = Int.fract (((V1 * j : ℕ) : ℝ) / D) := by
    rw [hτ_def]
    congr 1
    push_cast
    ring
  have hγ_lo : 1 / 6 - (V1 : ℝ) / (3 * V3) ≤ Int.fract ((V1 : ℝ) * τ) := by
    rw [hfr1]; exact hj_lo
  have hγ_hi : Int.fract ((V1 : ℝ) * τ) ≤ 5 / 6 - 5 * (V1 : ℝ) / (6 * V3) := by
    rw [hfr1]; exact hj_hi
  have h1safe : 1 / 6 ≤ Int.fract ((V1 : ℝ) * s) ∧
      Int.fract ((V1 : ℝ) * s) ≤ 5 / 6 := by
    have hm_lo : (V1 : ℝ) / (3 * V3) ≤ (V1 : ℝ) * (s - τ) := by
      have h := mul_le_mul_of_nonneg_left hδlo hv1R.le
      rw [show (V1 : ℝ) * (1 / (3 * V3)) = (V1 : ℝ) / (3 * V3) from by ring] at h
      linarith
    have hm_hi : (V1 : ℝ) * (s - τ) ≤ 5 * (V1 : ℝ) / (6 * V3) := by
      have h := mul_le_mul_of_nonneg_left hδhi hv1R.le
      rw [show (V1 : ℝ) * (5 / (6 * V3)) = 5 * (V1 : ℝ) / (6 * V3) from by
        ring] at h
      linarith
    have h0 : 0 ≤ Int.fract ((V1 : ℝ) * τ) + (V1 : ℝ) * (s - τ) := by
      have hfn := Int.fract_nonneg ((V1 : ℝ) * τ)
      have hpos' : (0 : ℝ) < (V1 : ℝ) / (3 * V3) := by positivity
      linarith
    have h1 : Int.fract ((V1 : ℝ) * τ) + (V1 : ℝ) * (s - τ) < 1 := by
      linarith
    have hfs := bhk_fract_translate (V1 : ℝ) τ (s - τ) h0 h1
    rw [show τ + (s - τ) = s from by ring] at hfs
    rw [hfs]
    exact ⟨by linarith, by linarith⟩
  -- Runners 2 and 3: integer position at `τ`, linear motion inside `[0,1)`.
  have hint : ∀ (V M : ℕ), (V : ℝ) * τ = (M : ℝ) →
      1 / 6 ≤ (V : ℝ) * (s - τ) → (V : ℝ) * (s - τ) ≤ 5 / 6 →
      1 / 6 ≤ Int.fract ((V : ℝ) * s) ∧ Int.fract ((V : ℝ) * s) ≤ 5 / 6 := by
    intro V M hMτ hlo' hhi'
    have hsplit : (V : ℝ) * s = (V : ℝ) * (s - τ) + ((M : ℤ) : ℝ) := by
      rw [Int.cast_natCast, ← hMτ]
      ring
    rw [hsplit, Int.fract_add_intCast,
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    exact ⟨hlo', hhi'⟩
  have hmulτ : ∀ c : ℕ, ((c * D : ℕ) : ℝ) * τ = ((c * j : ℕ) : ℝ) := by
    intro c
    rw [hτ_def]
    push_cast
    field_simp
  have h3τ : (V3 : ℝ) * τ = (((k' + 1) * j : ℕ) : ℝ) := by
    rw [show (V3 : ℝ) = (((k' + 1) * D : ℕ) : ℝ) from by rw [hv3']]
    exact hmulτ (k' + 1)
  have h2τ : (V2 : ℝ) * τ = ((k' * j : ℕ) : ℝ) := by
    rw [show (V2 : ℝ) = ((k' * D : ℕ) : ℝ) from by rw [hv2']]
    exact hmulτ k'
  have h3safe := hint V3 ((k' + 1) * j) h3τ
    (by
      have h := mul_le_mul_of_nonneg_left hδlo hv3R.le
      rw [show (V3 : ℝ) * (1 / (3 * V3)) = 1 / 3 from by field_simp] at h
      linarith)
    (by
      have h := mul_le_mul_of_nonneg_left hδhi hv3R.le
      rw [show (V3 : ℝ) * (5 / (6 * V3)) = 5 / 6 from by field_simp] at h
      linarith)
  have h2safe := hint V2 (k' * j) h2τ
    (by
      have h := mul_le_mul_of_nonneg_left hδlo hv2R.le
      rw [show (V2 : ℝ) * (1 / (3 * V3)) = (V2 : ℝ) / (3 * V3) from by
        ring] at h
      have h6 : 1 / 6 ≤ (V2 : ℝ) / (3 * V3) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        linarith
      linarith)
    (by
      have h := mul_le_mul_of_nonneg_left hδhi hv2R.le
      rw [show (V2 : ℝ) * (5 / (6 * V3)) = 5 * (V2 : ℝ) / (6 * V3) from by
        ring] at h
      have h6 : 5 * (V2 : ℝ) / (6 * V3) ≤ 5 / 6 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith)
  -- Convert fract-safety to non-membership in the three unsafe sets.
  rw [Set.mem_compl_iff]
  intro hmem
  have hsafe : ∀ x : ℝ, 1 / 6 ≤ Int.fract x → Int.fract x ≤ 5 / 6 →
      ¬ circDist x < 1 / 6 := by
    intro x hx1 hx2
    rw [not_lt]
    unfold circDist
    exact le_min hx1 (by linarith)
  rcases hmem with (h | h) | h
  · exact hsafe _ h1safe.1 h1safe.2 ((mem_unsafeOf_iff _ _ _).mp h)
  · exact hsafe _ h2safe.1 h2safe.2 ((mem_unsafeOf_iff _ _ _).mp h)
  · exact hsafe _ h3safe.1 h3safe.2 ((mem_unsafeOf_iff _ _ _).mp h)

/-- **The §6 123-gap `I_j` (PROVED).** Under the §6 arithmetic structure
    there is a 123-gap of length exactly `1/(2 v₃)`: pick `j` with
    `{v₁ j/D}` in the (59)-window via `bhk_s6_find_j`, then apply
    `bhk_s6_123_gap_at`. -/
lemma bhk_s6_123_gap (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (D k : ℕ) (hD2 : 2 ≤ D) (hk2 : 2 ≤ k)
    (hv3 : speeds ⟨2, by omega⟩ = k * D)
    (hv2 : speeds ⟨1, by omega⟩ = (k - 1) * D)
    (hndvd : ¬ D ∣ speeds ⟨0, by omega⟩) :
    ∃ a b : ℝ, a ≤ b ∧ b - a = 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) ∧
      Set.Icc a b ⊆ (unsafeOf speeds ⟨0, by omega⟩ ∪
                     unsafeOf speeds ⟨1, by omega⟩ ∪
                     unsafeOf speeds ⟨2, by omega⟩)ᶜ := by
  have hV1pos : 0 < speeds ⟨0, by omega⟩ := hpos _
  set V1 : ℕ := speeds ⟨0, by omega⟩ with hV1_def
  set V3 : ℕ := speeds ⟨2, by omega⟩ with hV3_def
  have hDpos : 0 < D := by omega
  have hv1R : (0 : ℝ) < V1 := by exact_mod_cast hV1pos
  have hv3R : (0 : ℝ) < V3 := by
    exact_mod_cast (show 0 < V3 from by
      rw [hv3]; exact Nat.mul_pos (by omega) (by omega))
  have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hsmallR : 3 * (V1 : ℝ) < V3 := by exact_mod_cast hsmall
  -- The (59)-window for runner 1.
  have hwin_lo : 0 ≤ 1 / 6 - (V1 : ℝ) / (3 * V3) := by
    rw [sub_nonneg, div_le_iff₀ (by positivity)]
    nlinarith
  have hwin_hi : 5 / 6 - 5 * (V1 : ℝ) / (6 * V3) < 1 := by
    have hp : 0 < 5 * (V1 : ℝ) / (6 * V3) := by positivity
    linarith
  have hwin_gap : 1 / 2 ≤ (5 / 6 - 5 * (V1 : ℝ) / (6 * V3))
      - (1 / 6 - (V1 : ℝ) / (3 * V3)) := by
    have h1 : 5 * (V1 : ℝ) / (6 * V3) - (V1 : ℝ) / (3 * V3)
        = (V1 : ℝ) / (2 * V3) := by
      field_simp
      ring
    have h2 : (V1 : ℝ) / (2 * V3) ≤ 1 / 6 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  obtain ⟨j, hj_lo, hj_hi⟩ := bhk_s6_find_j V1 D hDpos hndvd
    (1 / 6 - (V1 : ℝ) / (3 * V3)) (5 / 6 - 5 * (V1 : ℝ) / (6 * V3))
    hwin_lo hwin_hi hwin_gap
  have hab : (j : ℝ) / D + 1 / (3 * (V3 : ℝ)) ≤ (j : ℝ) / D + 5 / (6 * V3) := by
    have h2 : 1 / (3 * (V3 : ℝ)) ≤ 5 / (6 * V3) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hblen : ((j : ℝ) / D + 5 / (6 * (V3 : ℝ)))
      - ((j : ℝ) / D + 1 / (3 * V3)) = 1 / (2 * (V3 : ℝ)) := by
    field_simp
    ring
  exact ⟨(j : ℝ) / D + 1 / (3 * V3), (j : ℝ) / D + 5 / (6 * V3), hab, hblen,
    bhk_s6_123_gap_at speeds hmono hpos hsmall D k hD2 hk2 hv3 hv2 j hj_lo hj_hi⟩

/-- **Condition (60) ⟹ opposite point (PROVED).** If `p := {v₄ j/D}`
    avoids the arc `(1/2 − v₄/(3v₃), 3/2 − 5v₄/(6v₃))` — i.e. satisfies
    BHK (60) — then runner 4 passes exactly opposite the origin at some
    time in the `I_j` gap `[j/D + 1/(3v₃), j/D + 5/(6v₃)]`: during the
    gap runner 4 sweeps an arc of length `v₄/(2v₃) > 1/2` starting at
    `p + v₄/(3v₃)`, and (60) places the half-point inside that sweep. -/
lemma bhk_s6_opposite (V3 V4 D : ℕ) (hD : 0 < D) (hv3pos : 0 < V3)
    (hv34 : V3 < V4) (h43 : 3 * V4 < 4 * V3) (j : ℕ)
    (h60 : Int.fract (((V4 * j : ℕ) : ℝ) / D) ≤ 1/2 - (V4 : ℝ) / (3 * V3) ∨
           3/2 - 5 * (V4 : ℝ) / (6 * V3) ≤ Int.fract (((V4 * j : ℕ) : ℝ) / D)) :
    ∃ t ∈ Set.Icc ((j : ℝ) / D + 1 / (3 * (V3 : ℝ)))
                  ((j : ℝ) / D + 5 / (6 * (V3 : ℝ))),
      Int.fract ((V4 : ℝ) * t) = 1 / 2 := by
  have hv3R : (0 : ℝ) < V3 := by exact_mod_cast hv3pos
  have hv4R : (0 : ℝ) < V4 := by exact_mod_cast (by omega : 0 < V4)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have h34R : (V3 : ℝ) < V4 := by exact_mod_cast hv34
  have h43R : 3 * (V4 : ℝ) < 4 * V3 := by exact_mod_cast h43
  set p : ℝ := Int.fract (((V4 * j : ℕ) : ℝ) / D) with hp_def
  have hp0 : 0 ≤ p := Int.fract_nonneg _
  have hp1 : p < 1 := Int.fract_lt_one _
  have hsplit : (V4 : ℝ) * ((j : ℝ) / D)
      = p + (⌊((V4 * j : ℕ) : ℝ) / D⌋ : ℝ) := by
    rw [hp_def, Int.fract]
    push_cast
    field_simp
    ring
  rcases h60 with h | h
  · -- Left branch: `t = j/D + (1/2 − p)/v₄`.
    refine ⟨(j : ℝ) / D + (1/2 - p) / V4, ⟨?_, ?_⟩, ?_⟩
    · have key : (V4 : ℝ) / (3 * V3) ≤ 1/2 - p := by linarith
      have h1 : 1 / (3 * (V3 : ℝ)) ≤ (1/2 - p) / V4 := by
        rw [div_le_div_iff₀ (by positivity) hv4R]
        have := mul_le_mul_of_nonneg_right key (le_of_lt (by positivity :
          (0 : ℝ) < 3 * V3))
        calc 1 * (V4 : ℝ) = V4 := by ring
        _ = (V4 : ℝ) / (3 * V3) * (3 * V3) := by field_simp
        _ ≤ (1/2 - p) * (3 * V3) := by
            exact mul_le_mul_of_nonneg_right key (by positivity)
      linarith
    · have key : 1/2 - p ≤ 5 * (V4 : ℝ) / (6 * V3) := by
        have h12 : (1 : ℝ)/2 ≤ 5 * (V4 : ℝ) / (6 * V3) := by
          rw [div_le_div_iff₀ (by norm_num) (by positivity)]
          nlinarith
        linarith
      have h1 : (1/2 - p) / V4 ≤ 5 / (6 * (V3 : ℝ)) := by
        rw [div_le_div_iff₀ hv4R (by positivity)]
        calc (1/2 - p) * (6 * (V3 : ℝ))
            ≤ 5 * (V4 : ℝ) / (6 * V3) * (6 * V3) := by
              exact mul_le_mul_of_nonneg_right key (by positivity)
        _ = 5 * (V4 : ℝ) := by field_simp
        _ = 5 * V4 := by ring
      linarith
    · have heq : (V4 : ℝ) * ((j : ℝ) / D + (1/2 - p) / V4)
          = 1/2 + (⌊((V4 * j : ℕ) : ℝ) / D⌋ : ℝ) := by
        rw [mul_add, hsplit, mul_div_cancel₀ _ hv4R.ne']
        ring
      rw [heq, Int.fract_add_intCast]
      norm_num [Int.fract_eq_self]
  · -- Right branch: `t = j/D + (3/2 − p)/v₄`.
    refine ⟨(j : ℝ) / D + (3/2 - p) / V4, ⟨?_, ?_⟩, ?_⟩
    · have key : (V4 : ℝ) / (3 * V3) ≤ 3/2 - p := by
        have h12 : (V4 : ℝ) / (3 * V3) ≤ 1/2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        linarith
      have h1 : 1 / (3 * (V3 : ℝ)) ≤ (3/2 - p) / V4 := by
        rw [div_le_div_iff₀ (by positivity) hv4R]
        calc 1 * (V4 : ℝ) = (V4 : ℝ) / (3 * V3) * (3 * V3) := by field_simp
        _ ≤ (3/2 - p) * (3 * V3) := by
            exact mul_le_mul_of_nonneg_right key (by positivity)
      linarith
    · have key : 3/2 - p ≤ 5 * (V4 : ℝ) / (6 * V3) := by linarith
      have h1 : (3/2 - p) / V4 ≤ 5 / (6 * (V3 : ℝ)) := by
        rw [div_le_div_iff₀ hv4R (by positivity)]
        calc (3/2 - p) * (6 * (V3 : ℝ))
            ≤ 5 * (V4 : ℝ) / (6 * V3) * (6 * V3) := by
              exact mul_le_mul_of_nonneg_right key (by positivity)
        _ = 5 * V4 := by field_simp
      linarith
    · have heq : (V4 : ℝ) * ((j : ℝ) / D + (3/2 - p) / V4)
          = 1/2 + ((⌊((V4 * j : ℕ) : ℝ) / D⌋ + 1 : ℤ) : ℝ) := by
        rw [mul_add, hsplit, mul_div_cancel₀ _ hv4R.ne']
        push_cast
        ring
      rw [heq, Int.fract_add_intCast]
      norm_num [Int.fract_eq_self]

/-- **The §6 witness bridge (PROVED).** An index `j` satisfying (59) and
    (60) yields a lonely time: `I_j` is a 123-gap of length
    `1/(2v₃) ≥ 1/(3v₃)` containing a time with `{v₄ t} = 1/2`, so
    Lemma 22 applies. -/
lemma bhk_s6_j_lonely (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (D k : ℕ) (hD2 : 2 ≤ D) (hk2 : 2 ≤ k)
    (hv3 : speeds ⟨2, by omega⟩ = k * D)
    (hv2 : speeds ⟨1, by omega⟩ = (k - 1) * D)
    (h43 : 3 * speeds ⟨3, by omega⟩ < 4 * speeds ⟨2, by omega⟩)
    (j : ℕ)
    (h59lo : 1/6 - (speeds ⟨0, by omega⟩ : ℝ) / (3 * speeds ⟨2, by omega⟩)
      ≤ Int.fract (((speeds ⟨0, by omega⟩ * j : ℕ) : ℝ) / D))
    (h59hi : Int.fract (((speeds ⟨0, by omega⟩ * j : ℕ) : ℝ) / D)
      ≤ 5/6 - 5 * (speeds ⟨0, by omega⟩ : ℝ) / (6 * speeds ⟨2, by omega⟩))
    (h60 : Int.fract (((speeds ⟨3, by omega⟩ * j : ℕ) : ℝ) / D)
        ≤ 1/2 - (speeds ⟨3, by omega⟩ : ℝ) / (3 * speeds ⟨2, by omega⟩) ∨
      3/2 - 5 * (speeds ⟨3, by omega⟩ : ℝ) / (6 * speeds ⟨2, by omega⟩)
        ≤ Int.fract (((speeds ⟨3, by omega⟩ * j : ℕ) : ℝ) / D)) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  have hD : 0 < D := by omega
  have hv34 : speeds ⟨2, by omega⟩ < speeds ⟨3, by omega⟩ :=
    hmono (Fin.mk_lt_mk.mpr (by omega))
  have hv3R : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h123 := bhk_s6_123_gap_at speeds hmono hpos hsmall D k hD2 hk2
    hv3 hv2 j h59lo h59hi
  obtain ⟨t, ht, h4⟩ := bhk_s6_opposite (speeds ⟨2, by omega⟩)
    (speeds ⟨3, by omega⟩) D hD (hpos _) hv34 h43 j h60
  have hab : (j : ℝ) / D + 1 / (3 * (speeds ⟨2, by omega⟩ : ℝ))
      ≤ (j : ℝ) / D + 5 / (6 * (speeds ⟨2, by omega⟩ : ℝ)) := by
    have h2 : 1 / (3 * (speeds ⟨2, by omega⟩ : ℝ))
        ≤ 5 / (6 * (speeds ⟨2, by omega⟩ : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hlen : 1 / (3 * (speeds ⟨2, by omega⟩ : ℝ))
      ≤ ((j : ℝ) / D + 5 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
        - ((j : ℝ) / D + 1 / (3 * (speeds ⟨2, by omega⟩ : ℝ))) := by
    have heq : ((j : ℝ) / D + 5 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
        - ((j : ℝ) / D + 1 / (3 * (speeds ⟨2, by omega⟩ : ℝ)))
        = 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by
      field_simp
      ring
    rw [heq, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  exact bhk_s6_lemma_22 speeds hmono hpos _ _ hab h123 hlen t ht h4

/-! ## The §6 witness stack

The reduced group data is `(n, c₁, c₄, g)` with `g·n = D`, `g·c₁ = v₁`,
`g·c₄ = v₄` (`g := gcd(D, gcd(v₁, v₄))`). Points of the §6 orbit group
have fractional coordinates `({c₁k/n}, {c₄k/n})`; an index `k` whose
coordinates satisfy (59) and (60) yields a lonely time via the bridge. -/

/-- **Membership ⟹ index (PROVED).** A `ZMod`-pair in the cyclic group
    `⟨(c₁, c₄)⟩ ⊆ (ZMod n)²` is hit by a ℕ-multiple. -/
lemma bhk_s6_mem_k (n c₁ c₄ : ℕ) (hn : 0 < n) (a b : ℕ)
    (hmem : (((a : ℕ) : ZMod n), ((b : ℕ) : ZMod n)) ∈
      AddSubgroup.zmultiples ((c₁ : ZMod n), (c₄ : ZMod n))) :
    ∃ k : ℕ, c₁ * k % n = a % n ∧ c₄ * k % n = b % n := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  set k : ℕ := (z % (n : ℤ)).toNat with hk_def
  have hk_cast : ((k : ℕ) : ℤ) = z % (n : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg z (by exact_mod_cast (by omega : n ≠ 0)))
  have hzk : ((z : ℤ) : ZMod n) = ((k : ℕ) : ZMod n) := by
    rw [show ((k : ℕ) : ZMod n) = (((k : ℕ) : ℤ) : ZMod n) from by push_cast; rfl,
        hk_cast, ZMod.intCast_mod]
  refine ⟨k, ?_, ?_⟩
  · have h1 : ((a : ℕ) : ZMod n) = z • (c₁ : ZMod n) := by
      have := congr_arg Prod.fst hz
      simpa using this.symm
    have h2 : ((c₁ * k : ℕ) : ZMod n) = ((a : ℕ) : ZMod n) := by
      rw [h1, zsmul_eq_mul, hzk]
      push_cast
      ring
    have := congr_arg ZMod.val h2
    rwa [ZMod.val_natCast, ZMod.val_natCast] at this
  · have h1 : ((b : ℕ) : ZMod n) = z • (c₄ : ZMod n) := by
      have := congr_arg Prod.snd hz
      simpa using this.symm
    have h2 : ((c₄ * k : ℕ) : ZMod n) = ((b : ℕ) : ZMod n) := by
      rw [h1, zsmul_eq_mul, hzk]
      push_cast
      ring
    have := congr_arg ZMod.val h2
    rwa [ZMod.val_natCast, ZMod.val_natCast] at this

/-- **Real-window witness (PROVED).** An index `k` whose orbit coordinates
    `((c₁k mod n)/n, (c₄k mod n)/n)` satisfy the exact (59)/(60) windows
    yields a lonely time. -/
lemma bhk_s6_witness_real (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (D K : ℕ) (hD2 : 2 ≤ D) (hK2 : 2 ≤ K)
    (hv3 : speeds ⟨2, by omega⟩ = K * D)
    (hv2 : speeds ⟨1, by omega⟩ = (K - 1) * D)
    (h43 : 3 * speeds ⟨3, by omega⟩ < 4 * speeds ⟨2, by omega⟩)
    (n c₁ c₄ g : ℕ) (hnpos : 0 < n) (hgpos : 0 < g)
    (hd : g * n = D) (hc1 : g * c₁ = speeds ⟨0, by omega⟩)
    (hc4 : g * c₄ = speeds ⟨3, by omega⟩)
    (k : ℕ)
    (h59lo : 1 / 6 - (speeds ⟨0, by omega⟩ : ℝ) / (3 * speeds ⟨2, by omega⟩)
      ≤ ((c₁ * k % n : ℕ) : ℝ) / n)
    (h59hi : ((c₁ * k % n : ℕ) : ℝ) / n
      ≤ 5 / 6 - 5 * (speeds ⟨0, by omega⟩ : ℝ) / (6 * speeds ⟨2, by omega⟩))
    (h60 : ((c₄ * k % n : ℕ) : ℝ) / n
        ≤ 1 / 2 - (speeds ⟨3, by omega⟩ : ℝ) / (3 * speeds ⟨2, by omega⟩) ∨
      3 / 2 - 5 * (speeds ⟨3, by omega⟩ : ℝ) / (6 * speeds ⟨2, by omega⟩)
        ≤ ((c₄ * k % n : ℕ) : ℝ) / n) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hgpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hDpos : 0 < D := by omega
  have hfr : ∀ V c : ℕ, g * c = V →
      Int.fract (((V * k : ℕ) : ℝ) / D) = ((c * k % n : ℕ) : ℝ) / n := by
    intro V c hVc
    have hcast : ((V * k : ℕ) : ℝ) / D = ((c * k : ℕ) : ℝ) / n := by
      rw [← hVc, ← hd]
      push_cast
      rw [show (g : ℝ) * c * k / (g * n) = (c : ℝ) * k / n * (g / g) from by ring,
          div_self hgR.ne', mul_one]
    rw [hcast, bhk_fract_nat_div _ _ hnpos]
  exact bhk_s6_j_lonely speeds hmono hpos hsmall D K hD2 hK2 hv3 hv2 h43 k
    (by rw [hfr _ _ hc1]; exact h59lo)
    (by rw [hfr _ _ hc1]; exact h59hi)
    (by rw [hfr _ _ hc4]; exact h60)

/-- **Sufficient ℕ-window witness (PROVED).** Via BHK (61), the fixed
    sub-rectangle `[1/6, 5/9] × ([2/3, 1) ∪ {0})` lies inside the true
    (59)/(60) windows for all admissible speeds; with `a := c₁k mod n`,
    `b := c₄k mod n` the conditions become the ℕ-inequalities
    `n ≤ 6a`, `9a ≤ 5n`, `2n ≤ 3b ∨ b = 0` — `omega`-friendly. -/
lemma bhk_s6_witness_num (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (D K : ℕ) (hD2 : 2 ≤ D) (hK2 : 2 ≤ K)
    (hv3 : speeds ⟨2, by omega⟩ = K * D)
    (hv2 : speeds ⟨1, by omega⟩ = (K - 1) * D)
    (h43 : 3 * speeds ⟨3, by omega⟩ < 4 * speeds ⟨2, by omega⟩)
    (n c₁ c₄ g : ℕ) (hnpos : 0 < n) (hgpos : 0 < g)
    (hd : g * n = D) (hc1 : g * c₁ = speeds ⟨0, by omega⟩)
    (hc4 : g * c₄ = speeds ⟨3, by omega⟩)
    (k : ℕ)
    (h_alo : n ≤ 6 * (c₁ * k % n)) (h_ahi : 9 * (c₁ * k % n) ≤ 5 * n)
    (h_b : 2 * n ≤ 3 * (c₄ * k % n) ∨ c₄ * k % n = 0) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hV1R : (0 : ℝ) < speeds ⟨0, by omega⟩ := by exact_mod_cast hpos _
  have hV3R : (0 : ℝ) < speeds ⟨2, by omega⟩ := by exact_mod_cast hpos _
  have hV4R : (0 : ℝ) < speeds ⟨3, by omega⟩ := by exact_mod_cast hpos _
  have hsmallR : 3 * (speeds ⟨0, by omega⟩ : ℝ) < speeds ⟨2, by omega⟩ := by
    exact_mod_cast hsmall
  have h43R : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * speeds ⟨2, by omega⟩ := by
    exact_mod_cast h43
  have h34R : (speeds ⟨2, by omega⟩ : ℝ) < speeds ⟨3, by omega⟩ := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (by omega))
  have h_aloR : (n : ℝ) ≤ 6 * ((c₁ * k % n : ℕ) : ℝ) := by exact_mod_cast h_alo
  have h_ahiR : 9 * ((c₁ * k % n : ℕ) : ℝ) ≤ 5 * n := by exact_mod_cast h_ahi
  apply bhk_s6_witness_real speeds hmono hpos hsmall D K hD2 hK2 hv3 hv2 h43
    n c₁ c₄ g hnpos hgpos hd hc1 hc4 k
  · -- `1/6 ≤ a/n` suffices since the (59) lower end is below `1/6`.
    have h1 : (1 : ℝ) / 6 ≤ ((c₁ * k % n : ℕ) : ℝ) / n := by
      rw [le_div_iff₀ hnR]; linarith
    have h2 : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) / (3 * speeds ⟨2, by omega⟩) := by
      positivity
    linarith
  · -- `a/n ≤ 5/9` suffices since the (59) upper end is above `5/9`.
    have h1 : ((c₁ * k % n : ℕ) : ℝ) / n ≤ 5 / 9 := by
      rw [div_le_iff₀ hnR]; linarith
    have h2 : 5 * (speeds ⟨0, by omega⟩ : ℝ) / (6 * speeds ⟨2, by omega⟩)
        ≤ 5 / 18 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  · rcases h_b with h | h
    · -- `b/n ≥ 2/3` suffices since the (60) lower end is below `2/3`.
      refine Or.inr ?_
      have h1 : (2 : ℝ) / 3 ≤ ((c₄ * k % n : ℕ) : ℝ) / n := by
        rw [le_div_iff₀ hnR]
        have : (2 : ℝ) * n ≤ 3 * ((c₄ * k % n : ℕ) : ℝ) := by exact_mod_cast h
        linarith
      have h2 : 3 / 2 - 5 * (speeds ⟨3, by omega⟩ : ℝ)
          / (6 * speeds ⟨2, by omega⟩) ≤ 2 / 3 := by
        have key : (5 : ℝ) / 6 ≤ 5 * (speeds ⟨3, by omega⟩ : ℝ)
            / (6 * speeds ⟨2, by omega⟩) := by
          rw [div_le_div_iff₀ (by norm_num) (by positivity)]
          nlinarith
        linarith
      linarith
    · -- `b = 0` lies in the wrapped part of the (60) window.
      refine Or.inl ?_
      have h1 : ((c₄ * k % n : ℕ) : ℝ) / n = 0 := by rw [h]; simp
      have h2 : (speeds ⟨3, by omega⟩ : ℝ) / (3 * speeds ⟨2, by omega⟩)
          ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith

/-- **Hit ⟹ lonely (PROVED).** A `ZMod`-pair `(a, b)` of the cyclic
    group satisfying the sufficient ℕ-window yields a lonely time. -/
lemma bhk_s6_hit_num (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (D K : ℕ) (hD2 : 2 ≤ D) (hK2 : 2 ≤ K)
    (hv3 : speeds ⟨2, by omega⟩ = K * D)
    (hv2 : speeds ⟨1, by omega⟩ = (K - 1) * D)
    (h43 : 3 * speeds ⟨3, by omega⟩ < 4 * speeds ⟨2, by omega⟩)
    (n c₁ c₄ g : ℕ) (hnpos : 0 < n) (hgpos : 0 < g)
    (hd : g * n = D) (hc1 : g * c₁ = speeds ⟨0, by omega⟩)
    (hc4 : g * c₄ = speeds ⟨3, by omega⟩)
    (a b : ℕ) (ha : a < n) (hb : b < n)
    (hmem : (((a : ℕ) : ZMod n), ((b : ℕ) : ZMod n)) ∈
      AddSubgroup.zmultiples ((c₁ : ZMod n), (c₄ : ZMod n)))
    (h_alo : n ≤ 6 * a) (h_ahi : 9 * a ≤ 5 * n)
    (h_b : 2 * n ≤ 3 * b ∨ b = 0) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  obtain ⟨k, hk1, hk4⟩ := bhk_s6_mem_k n c₁ c₄ hnpos a b hmem
  rw [Nat.mod_eq_of_lt ha] at hk1
  rw [Nat.mod_eq_of_lt hb] at hk4
  exact bhk_s6_witness_num speeds hmono hpos hsmall D K hD2 hK2 hv3 hv2 h43
    n c₁ c₄ g hnpos hgpos hd hc1 hc4 k (by omega) (by omega) (by omega)

/-! ## The §6 exceptional cases (BHK Cases 6.1–6.5)

Corollary 6 leaves a short list of group structures; each is discharged
by an explicit multiple of the exceptional element landing in the
sufficient window, except 6.2 and 6.5.1 (ad hoc, see below). -/

/-- **Multiple of an exceptional pair.** `(1, e) ∈ H ⟹ (m, m·e) ∈ H`. -/
lemma bhk_s6_pair_mul (n c₁ c₄ : ℕ) (e : ZMod n)
    (hmem : ((1 : ZMod n), e) ∈
      AddSubgroup.zmultiples ((c₁ : ZMod n), (c₄ : ZMod n))) (m : ℕ) :
    (((m : ℕ) : ZMod n), (m : ZMod n) * e) ∈
      AddSubgroup.zmultiples ((c₁ : ZMod n), (c₄ : ZMod n)) := by
  have h := AddSubgroup.nsmul_mem _ hmem m
  simpa [Prod.smul_mk, nsmul_eq_mul, mul_one] using h

/-- **Generic exceptional-pair discharge (PROVED).** From `(1, e) ∈ H`
    and an explicit multiplier `m` whose pair `(m, b)` satisfies the
    sufficient ℕ-window, produce a lonely time. -/
lemma bhk_s6_pair_witness (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (D K : ℕ) (hD2 : 2 ≤ D) (hK2 : 2 ≤ K)
    (hv3 : speeds ⟨2, by omega⟩ = K * D)
    (hv2 : speeds ⟨1, by omega⟩ = (K - 1) * D)
    (h43 : 3 * speeds ⟨3, by omega⟩ < 4 * speeds ⟨2, by omega⟩)
    (n c₁ c₄ g : ℕ) (hnpos : 0 < n) (hgpos : 0 < g)
    (hd : g * n = D) (hc1 : g * c₁ = speeds ⟨0, by omega⟩)
    (hc4 : g * c₄ = speeds ⟨3, by omega⟩)
    (e : ZMod n)
    (hmem : ((1 : ZMod n), e) ∈
      AddSubgroup.zmultiples ((c₁ : ZMod n), (c₄ : ZMod n)))
    (m b : ℕ) (hm : m < n) (hb : b < n)
    (hbe : ((b : ℕ) : ZMod n) = (m : ZMod n) * e)
    (h_alo : n ≤ 6 * m) (h_ahi : 9 * m ≤ 5 * n)
    (h_b : 2 * n ≤ 3 * b ∨ b = 0) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  have hpair := bhk_s6_pair_mul n c₁ c₄ e hmem m
  rw [← hbe] at hpair
  exact bhk_s6_hit_num speeds hmono hpos hsmall D K hD2 hK2 hv3 hv2 h43
    n c₁ c₄ g hnpos hgpos hd hc1 hc4 m b hm hb hpair h_alo h_ahi h_b

/-- **BHK Case 6.1 (PROVED).** `n ∣ c₄` (the second projection of the
    orbit group is trivial, BHK's `n₂ = 1`): then `gcd(n, c₁) = 1`, so a
    Bezout multiplier steers the first coordinate into `[1/6, 5/9]`
    while the second stays at `0`, which lies in the wrapped part of the
    (60) window. -/
lemma bhk_s6_case_61 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (D K : ℕ) (hD2 : 2 ≤ D) (hK2 : 2 ≤ K)
    (hv3 : speeds ⟨2, by omega⟩ = K * D)
    (hv2 : speeds ⟨1, by omega⟩ = (K - 1) * D)
    (h43 : 3 * speeds ⟨3, by omega⟩ < 4 * speeds ⟨2, by omega⟩)
    (n c₁ c₄ g : ℕ) (hn : 1 < n) (hgpos : 0 < g)
    (hd : g * n = D) (hc1 : g * c₁ = speeds ⟨0, by omega⟩)
    (hc4 : g * c₄ = speeds ⟨3, by omega⟩)
    (hcop : Nat.gcd n (Nat.gcd c₁ c₄) = 1)
    (hdvd : n ∣ c₄) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  have hnpos : 0 < n := by omega
  -- `gcd(n, c₁) = 1`: any common divisor also divides `c₄`.
  have hg1 : Nat.gcd n c₁ = 1 := by
    have h1 : Nat.gcd n c₁ ∣ Nat.gcd c₁ c₄ :=
      Nat.dvd_gcd (Nat.gcd_dvd_right n c₁)
        ((Nat.gcd_dvd_left n c₁).trans hdvd)
    have h2 : Nat.gcd n c₁ ∣ Nat.gcd n (Nat.gcd c₁ c₄) :=
      Nat.dvd_gcd (Nat.gcd_dvd_left n c₁) h1
    rw [hcop] at h2
    exact Nat.dvd_one.mp h2
  -- Bezout multiplier `t₁` with `c₁ t₁ ≡ 1`, then `k := t₁ · m`.
  obtain ⟨t₁, ht₁⟩ := bhk_s7_bezout_mod n c₁ hnpos
  rw [hg1, Nat.mod_eq_of_lt hn] at ht₁
  set m : ℕ := (n + 5) / 6 with hm_def
  have hk1 : c₁ * (t₁ * m) % n = m := by
    rw [show t₁ * m = m * t₁ from mul_comm t₁ m, bhk_s7_mul_mod c₁ t₁ m n, ht₁,
        show 1 * m = m from one_mul m, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨q, hq⟩ := hdvd
  have hk4 : c₄ * (t₁ * m) % n = 0 := by
    rw [hq, show n * q * (t₁ * m) = n * (q * (t₁ * m)) from by ring]
    exact Nat.mul_mod_right _ _
  exact bhk_s6_witness_num speeds hmono hpos hsmall D K hD2 hK2 hv3 hv2 h43
    n c₁ c₄ g hnpos hgpos hd hc1 hc4 (t₁ * m)
    (by omega) (by omega) (by rw [hk4]; omega)

/-- **BHK Case 6.3 (PROVED).** `(1/n, −1/n) ∈ G`, `n ≥ 3`: the multiple
    `m = ⌈n/6⌉` gives `(m/n, (n−m)/n)` in the sufficient window. -/
lemma bhk_s6_case_63 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (D K : ℕ) (hD2 : 2 ≤ D) (hK2 : 2 ≤ K)
    (hv3 : speeds ⟨2, by omega⟩ = K * D)
    (hv2 : speeds ⟨1, by omega⟩ = (K - 1) * D)
    (h43 : 3 * speeds ⟨3, by omega⟩ < 4 * speeds ⟨2, by omega⟩)
    (n c₁ c₄ g : ℕ) (hn : 3 ≤ n) (hgpos : 0 < g)
    (hd : g * n = D) (hc1 : g * c₁ = speeds ⟨0, by omega⟩)
    (hc4 : g * c₄ = speeds ⟨3, by omega⟩)
    (hmem : ((1 : ZMod n), (-1 : ZMod n)) ∈
      AddSubgroup.zmultiples ((c₁ : ZMod n), (c₄ : ZMod n))) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  set m : ℕ := (n + 5) / 6 with hm_def
  refine bhk_s6_pair_witness speeds hmono hpos hsmall D K hD2 hK2 hv3 hv2 h43
    n c₁ c₄ g (by omega) hgpos hd hc1 hc4 (-1 : ZMod n) hmem
    m (n - m) (by omega) (by omega) ?_ (by omega) (by omega) (by omega)
  rw [Nat.cast_sub (by omega : m ≤ n), ZMod.natCast_self]
  ring

/-- **BHK Case 6.4 (PROVED).** `(1/n, 2/n) ∈ G`, `n ≥ 4`: the multiple
    `m = ⌈n/3⌉` has `m/n ∈ [1/3, 1/2]`, so `(m/n, 2m/n)` lands in the
    sufficient window (`2m = n` giving the wrapped point `0`). -/
lemma bhk_s6_case_64 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (D K : ℕ) (hD2 : 2 ≤ D) (hK2 : 2 ≤ K)
    (hv3 : speeds ⟨2, by omega⟩ = K * D)
    (hv2 : speeds ⟨1, by omega⟩ = (K - 1) * D)
    (h43 : 3 * speeds ⟨3, by omega⟩ < 4 * speeds ⟨2, by omega⟩)
    (n c₁ c₄ g : ℕ) (hn : 4 ≤ n) (hgpos : 0 < g)
    (hd : g * n = D) (hc1 : g * c₁ = speeds ⟨0, by omega⟩)
    (hc4 : g * c₄ = speeds ⟨3, by omega⟩)
    (hmem : ((1 : ZMod n), (2 : ZMod n)) ∈
      AddSubgroup.zmultiples ((c₁ : ZMod n), (c₄ : ZMod n))) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  rcases (by omega : 2 * ((n + 2) / 3) < n ∨ 2 * ((n + 2) / 3) = n) with h | h
  · -- `2m < n`: the pair `(m, 2m)`.
    refine bhk_s6_pair_witness speeds hmono hpos hsmall D K hD2 hK2 hv3 hv2
      h43 n c₁ c₄ g (by omega) hgpos hd hc1 hc4 (2 : ZMod n) hmem
      ((n + 2) / 3) (2 * ((n + 2) / 3)) (by omega) h ?_
      (by omega) (by omega) (by omega)
    push_cast
    ring
  · -- `2m = n`: the wrapped pair `(m, 0)`.
    refine bhk_s6_pair_witness speeds hmono hpos hsmall D K hD2 hK2 hv3 hv2
      h43 n c₁ c₄ g (by omega) hgpos hd hc1 hc4 (2 : ZMod n) hmem
      ((n + 2) / 3) 0 (by omega) (by omega) ?_
      (by omega) (by omega) (by omega)
    have h0 : ((2 * ((n + 2) / 3) : ℕ) : ZMod n) = 0 := by
      rw [h, ZMod.natCast_self]
    push_cast at h0 ⊢
    linear_combination -h0

/-- **BHK Case 6.5, generic `n` (PROVED).** `(1/n, −2/n) ∈ G`, `n ≥ 4`,
    `n ∉ {5, 7}`: the multiple `m = ⌈n/2⌉` has `m/n ∈ [1/2, 5/9]`
    (using `n` even or `n ≥ 9`), so `(m/n, (2n−2m)/n)` lands in the
    sufficient window. -/
lemma bhk_s6_case_65 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (D K : ℕ) (hD2 : 2 ≤ D) (hK2 : 2 ≤ K)
    (hv3 : speeds ⟨2, by omega⟩ = K * D)
    (hv2 : speeds ⟨1, by omega⟩ = (K - 1) * D)
    (h43 : 3 * speeds ⟨3, by omega⟩ < 4 * speeds ⟨2, by omega⟩)
    (n c₁ c₄ g : ℕ) (hn : 4 ≤ n) (hn' : n % 2 = 0 ∨ 9 ≤ n) (hgpos : 0 < g)
    (hd : g * n = D) (hc1 : g * c₁ = speeds ⟨0, by omega⟩)
    (hc4 : g * c₄ = speeds ⟨3, by omega⟩)
    (hmem : ((1 : ZMod n), (-2 : ZMod n)) ∈
      AddSubgroup.zmultiples ((c₁ : ZMod n), (c₄ : ZMod n))) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  have hn0 : ((n : ℕ) : ZMod n) = 0 := ZMod.natCast_self n
  rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with h | h
  · -- `n` even: `2m = n`, the wrapped pair `(m, 0)`.
    refine bhk_s6_pair_witness speeds hmono hpos hsmall D K hD2 hK2 hv3 hv2
      h43 n c₁ c₄ g (by omega) hgpos hd hc1 hc4 (-2 : ZMod n) hmem
      ((n + 1) / 2) 0 (by omega) (by omega) ?_
      (by omega) (by omega) (by omega)
    have h0 : ((2 * ((n + 1) / 2) : ℕ) : ZMod n) = ((n : ℕ) : ZMod n) := by
      congr 1
      omega
    rw [hn0] at h0
    push_cast at h0 ⊢
    linear_combination h0
  · -- `n` odd (hence `n ≥ 9`): `2m = n + 1`, the pair `(m, n − 1)`.
    refine bhk_s6_pair_witness speeds hmono hpos hsmall D K hD2 hK2 hv3 hv2
      h43 n c₁ c₄ g (by omega) hgpos hd hc1 hc4 (-2 : ZMod n) hmem
      ((n + 1) / 2) (n - 1) (by omega) (by omega) ?_
      (by omega) (by omega) (by omega)
    have h1 : ((2 * ((n + 1) / 2) : ℕ) : ZMod n) = ((n + 1 : ℕ) : ZMod n) := by
      congr 1
      omega
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast at h1 ⊢
    rw [hn0] at h1 ⊢
    linear_combination h1

/-- **The `(1, ±3)` case (PROVED).** Omitted from BHK's §6 case list but
    reachable in the cone when `3v₁ + v₄ > 2v₃`; (13)-minimality forces
    `n ≥ 6` (else `(1, 3∓n)` is a smaller non-corner element), and then
    an explicit multiple `m ≈ n/3` lands in the sufficient window. -/
lemma bhk_s6_case_66 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (D K : ℕ) (hD2 : 2 ≤ D) (hK2 : 2 ≤ K)
    (hv3 : speeds ⟨2, by omega⟩ = K * D)
    (hv2 : speeds ⟨1, by omega⟩ = (K - 1) * D)
    (h43 : 3 * speeds ⟨3, by omega⟩ < 4 * speeds ⟨2, by omega⟩)
    (n c₁ c₄ g : ℕ) (hn : 6 ≤ n) (hgpos : 0 < g)
    (hd : g * n = D) (hc1 : g * c₁ = speeds ⟨0, by omega⟩)
    (hc4 : g * c₄ = speeds ⟨3, by omega⟩)
    (e : ℤ) (he : e = 3 ∨ e = -3)
    (hmem : ((1 : ZMod n), (e : ZMod n)) ∈
      AddSubgroup.zmultiples ((c₁ : ZMod n), (c₄ : ZMod n))) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  have hn0 : ((n : ℕ) : ZMod n) = 0 := ZMod.natCast_self n
  rcases he with rfl | rfl
  · -- `e = 3`: `m = ⌊n/3⌋`, `b = 3m mod n ∈ {0, n−1, n−2}`.
    rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
    · refine bhk_s6_pair_witness speeds hmono hpos hsmall D K hD2 hK2 hv3 hv2
        h43 n c₁ c₄ g (by omega) hgpos hd hc1 hc4 ((3 : ℤ) : ZMod n) hmem
        (n / 3) 0 (by omega) (by omega) ?_ (by omega) (by omega) (by omega)
      have h0 : ((3 * (n / 3) : ℕ) : ZMod n) = ((n : ℕ) : ZMod n) := by
        congr 1
        omega
      rw [hn0] at h0
      push_cast at h0 ⊢
      linear_combination -h0
    · refine bhk_s6_pair_witness speeds hmono hpos hsmall D K hD2 hK2 hv3 hv2
        h43 n c₁ c₄ g (by omega) hgpos hd hc1 hc4 ((3 : ℤ) : ZMod n) hmem
        (n / 3) (n - 1) (by omega) (by omega) ?_
        (by omega) (by omega) (by omega)
      have h1 : ((3 * (n / 3) : ℕ) : ZMod n) = ((n - 1 : ℕ) : ZMod n) := by
        congr 1
        omega
      rw [← h1]
      push_cast
      ring
    · refine bhk_s6_pair_witness speeds hmono hpos hsmall D K hD2 hK2 hv3 hv2
        h43 n c₁ c₄ g (by omega) hgpos hd hc1 hc4 ((3 : ℤ) : ZMod n) hmem
        (n / 3) (n - 2) (by omega) (by omega) ?_
        (by omega) (by omega) (by omega)
      have h1 : ((3 * (n / 3) : ℕ) : ZMod n) = ((n - 2 : ℕ) : ZMod n) := by
        congr 1
        omega
      rw [← h1]
      push_cast
      ring
  · -- `e = −3`: `m = ⌈n/3⌉`, `b = (3n − 3m) mod n ∈ {0, n−1, n−2}`.
    rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
    · refine bhk_s6_pair_witness speeds hmono hpos hsmall D K hD2 hK2 hv3 hv2
        h43 n c₁ c₄ g (by omega) hgpos hd hc1 hc4 ((-3 : ℤ) : ZMod n) hmem
        (n / 3) 0 (by omega) (by omega) ?_ (by omega) (by omega) (by omega)
      have h0 : ((3 * (n / 3) : ℕ) : ZMod n) = ((n : ℕ) : ZMod n) := by
        congr 1
        omega
      rw [hn0] at h0
      push_cast at h0 ⊢
      linear_combination h0
    · refine bhk_s6_pair_witness speeds hmono hpos hsmall D K hD2 hK2 hv3 hv2
        h43 n c₁ c₄ g (by omega) hgpos hd hc1 hc4 ((-3 : ℤ) : ZMod n) hmem
        (n / 3 + 1) (n - 2) (by omega) (by omega) ?_
        (by omega) (by omega) (by omega)
      have h1 : ((3 * (n / 3 + 1) : ℕ) : ZMod n) = ((n + 2 : ℕ) : ZMod n) := by
        congr 1
        omega
      rw [Nat.cast_sub (by omega : 2 ≤ n)]
      push_cast at h1 ⊢
      rw [hn0] at h1 ⊢
      linear_combination h1
    · refine bhk_s6_pair_witness speeds hmono hpos hsmall D K hD2 hK2 hv3 hv2
        h43 n c₁ c₄ g (by omega) hgpos hd hc1 hc4 ((-3 : ℤ) : ZMod n) hmem
        (n / 3 + 1) (n - 1) (by omega) (by omega) ?_
        (by omega) (by omega) (by omega)
      have h1 : ((3 * (n / 3 + 1) : ℕ) : ZMod n) = ((n + 1 : ℕ) : ZMod n) := by
        congr 1
        omega
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      push_cast at h1 ⊢
      rw [hn0] at h1 ⊢
      linear_combination h1

/-- **BHK Case 6.5.2, `n = 7` (PROVED).** `(1/7, −2/7) ∈ G`: one of the
    two points `(1/7, 5/7)`, `(4/7, 6/7)` lies in the true (59)/(60)
    window — the first when `v₃ ≤ 14 v₁`, the second when `14 v₁ < v₃`. -/
lemma bhk_s6_case_652 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (D K : ℕ) (hD2 : 2 ≤ D) (hK2 : 2 ≤ K)
    (hv3 : speeds ⟨2, by omega⟩ = K * D)
    (hv2 : speeds ⟨1, by omega⟩ = (K - 1) * D)
    (h43 : 3 * speeds ⟨3, by omega⟩ < 4 * speeds ⟨2, by omega⟩)
    (c₁ c₄ g : ℕ) (hgpos : 0 < g)
    (hd : g * 7 = D) (hc1 : g * c₁ = speeds ⟨0, by omega⟩)
    (hc4 : g * c₄ = speeds ⟨3, by omega⟩)
    (hmem : ((1 : ZMod 7), (-2 : ZMod 7)) ∈
      AddSubgroup.zmultiples ((c₁ : ZMod 7), (c₄ : ZMod 7))) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  have hV1R : (0 : ℝ) < speeds ⟨0, by omega⟩ := by exact_mod_cast hpos _
  have hV3R : (0 : ℝ) < speeds ⟨2, by omega⟩ := by exact_mod_cast hpos _
  have hV4R : (0 : ℝ) < speeds ⟨3, by omega⟩ := by exact_mod_cast hpos _
  have hsmallR : 3 * (speeds ⟨0, by omega⟩ : ℝ) < speeds ⟨2, by omega⟩ := by
    exact_mod_cast hsmall
  have h34R : (speeds ⟨2, by omega⟩ : ℝ) < speeds ⟨3, by omega⟩ := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (by omega))
  rcases le_or_gt (speeds ⟨2, by omega⟩ : ℝ) (14 * speeds ⟨0, by omega⟩)
    with h14 | h14
  · -- `v₃ ≤ 14 v₁`: the point `(1/7, 5/7)`.
    have hpair : (((1 : ℕ) : ZMod 7), ((5 : ℕ) : ZMod 7)) ∈
        AddSubgroup.zmultiples ((c₁ : ZMod 7), (c₄ : ZMod 7)) := by
      have : (((1 : ℕ) : ZMod 7), ((5 : ℕ) : ZMod 7))
          = ((1 : ZMod 7), (-2 : ZMod 7)) := by decide
      rw [this]
      exact hmem
    obtain ⟨k, hk1, hk4⟩ := bhk_s6_mem_k 7 c₁ c₄ (by omega) 1 5 hpair
    have hcast1 : ((1 % 7 : ℕ) : ℝ) / ((7 : ℕ) : ℝ) = 1 / 7 := by norm_num
    have hcast5 : ((5 % 7 : ℕ) : ℝ) / ((7 : ℕ) : ℝ) = 5 / 7 := by norm_num
    apply bhk_s6_witness_real speeds hmono hpos hsmall D K hD2 hK2 hv3 hv2
      h43 7 c₁ c₄ g (by omega) hgpos hd hc1 hc4 k
    · rw [hk1, hcast1]
      have hb : (1 : ℝ) / 42
          ≤ (speeds ⟨0, by omega⟩ : ℝ) / (3 * speeds ⟨2, by omega⟩) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      linarith
    · rw [hk1, hcast1]
      have hb : 5 * (speeds ⟨0, by omega⟩ : ℝ) / (6 * speeds ⟨2, by omega⟩)
          ≤ 5 / 18 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    · refine Or.inr ?_
      rw [hk4, hcast5]
      have hb : (5 : ℝ) / 6
          ≤ 5 * (speeds ⟨3, by omega⟩ : ℝ) / (6 * speeds ⟨2, by omega⟩) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      linarith
  · -- `14 v₁ < v₃`: the point `(4/7, 6/7)`.
    have hpair : (((4 : ℕ) : ZMod 7), ((6 : ℕ) : ZMod 7)) ∈
        AddSubgroup.zmultiples ((c₁ : ZMod 7), (c₄ : ZMod 7)) := by
      have h4 := bhk_s6_pair_mul 7 c₁ c₄ (-2 : ZMod 7) hmem 4
      have : (((4 : ℕ) : ZMod 7), ((6 : ℕ) : ZMod 7))
          = (((4 : ℕ) : ZMod 7), ((4 : ℕ) : ZMod 7) * (-2 : ZMod 7)) := by
        decide
      rw [this]
      exact h4
    obtain ⟨k, hk1, hk4⟩ := bhk_s6_mem_k 7 c₁ c₄ (by omega) 4 6 hpair
    have hcast4 : ((4 % 7 : ℕ) : ℝ) / ((7 : ℕ) : ℝ) = 4 / 7 := by norm_num
    have hcast6 : ((6 % 7 : ℕ) : ℝ) / ((7 : ℕ) : ℝ) = 6 / 7 := by norm_num
    apply bhk_s6_witness_real speeds hmono hpos hsmall D K hD2 hK2 hv3 hv2
      h43 7 c₁ c₄ g (by omega) hgpos hd hc1 hc4 k
    · rw [hk1, hcast4]
      have hb : (0 : ℝ)
          ≤ (speeds ⟨0, by omega⟩ : ℝ) / (3 * speeds ⟨2, by omega⟩) := by
        positivity
      linarith
    · rw [hk1, hcast4]
      have hb : 5 * (speeds ⟨0, by omega⟩ : ℝ) / (6 * speeds ⟨2, by omega⟩)
          ≤ 5 / 84 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    · refine Or.inr ?_
      rw [hk4, hcast6]
      have hb : (5 : ℝ) / 6
          ≤ 5 * (speeds ⟨3, by omega⟩ : ℝ) / (6 * speeds ⟨2, by omega⟩) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      linarith

/-- **BHK Case 6.2** (OPEN — BHK pp. 41–42). `(1/n, 1/n) ∈ G`, `n ≥ 2`:
    the ad hoc argument. Pick `j` with
    `γ = {v₁jt₀} = {v₄jt₀} ∈ [1/3, 1/2]`; sub-cases `v₂ = v₃/2`
    (Lemma 23: `[7/6, 10/6]/v₃ ⊄ B₄ ∪ B₅`, then `m = 2`,
    `v₄ = v₃ + v₁`, runner 5 cannot cover both `jt₀ + 5/(6v₃)` and
    `jt₀ + 7/(6v₃)`) and `2v₂ ≥ 3v₃/2` (a `[jt₀ + 1/(4v₃), jt₀ + 5/(6v₃)]`
    123-gap, `8v₄ > 7v₃`, flanked 4-block, `n = 2` endgame). -/
lemma bhk_s6_case_62 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (D K : ℕ) (hD2 : 2 ≤ D) (hK2 : 2 ≤ K)
    (hv3 : speeds ⟨2, by omega⟩ = K * D)
    (hv2 : speeds ⟨1, by omega⟩ = (K - 1) * D)
    (h43 : 3 * speeds ⟨3, by omega⟩ < 4 * speeds ⟨2, by omega⟩)
    (n c₁ c₄ g : ℕ) (hn : 2 ≤ n) (hgpos : 0 < g)
    (hd : g * n = D) (hc1 : g * c₁ = speeds ⟨0, by omega⟩)
    (hc4 : g * c₄ = speeds ⟨3, by omega⟩)
    (hmem : ((1 : ZMod n), (1 : ZMod n)) ∈
      AddSubgroup.zmultiples ((c₁ : ZMod n), (c₄ : ZMod n))) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  sorry

/-- **§6.5.1 1234-gap inclusion.** Under failure of loneliness, the
    interval `[1/(6 v₁), 5/(6 v₄)]` is covered by runner 5 alone: it lies
    inside the `k = 0` safe gap of each of runners 1–4 (uses only
    monotonicity; mirror of the §8.1 inclusion in `Cases.lean`, restated
    here because `Cases.lean` imports this file). -/
lemma bhk_s6_651_1234_gap_incl (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (h_no_lonely : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1/6) :
    Set.Icc (1 / (6 * (speeds ⟨0, by omega⟩ : ℝ)))
            (5 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
    ⊆ unsafeOf speeds ⟨4, by omega⟩ := by
  set v1 : ℝ := (speeds ⟨0, by omega⟩ : ℝ) with hv1_def
  set v2 : ℝ := (speeds ⟨1, by omega⟩ : ℝ) with hv2_def
  set v3 : ℝ := (speeds ⟨2, by omega⟩ : ℝ) with hv3_def
  set v4 : ℝ := (speeds ⟨3, by omega⟩ : ℝ) with hv4_def
  have hv1_pos : 0 < v1 := by rw [hv1_def]; exact_mod_cast hpos _
  have hv2_pos : 0 < v2 := by rw [hv2_def]; exact_mod_cast hpos _
  have hv3_pos : 0 < v3 := by rw [hv3_def]; exact_mod_cast hpos _
  have hv4_pos : 0 < v4 := by rw [hv4_def]; exact_mod_cast hpos _
  have hv1_le_v2 : v1 ≤ v2 := by
    rw [hv1_def, hv2_def]
    exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr (show (0:ℕ) < 1 by omega)))
  have hv1_le_v3 : v1 ≤ v3 := by
    rw [hv1_def, hv3_def]
    exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr (show (0:ℕ) < 2 by omega)))
  have hv1_le_v4 : v1 ≤ v4 := by
    rw [hv1_def, hv4_def]
    exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr (show (0:ℕ) < 3 by omega)))
  have hv2_le_v4 : v2 ≤ v4 := by
    rw [hv2_def, hv4_def]
    exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr (show (1:ℕ) < 3 by omega)))
  have hv3_le_v4 : v3 ≤ v4 := by
    rw [hv3_def, hv4_def]
    exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr (show (2:ℕ) < 3 by omega)))
  intro t ht
  obtain ⟨htL, htR⟩ := ht
  obtain ⟨i, hi_unsafe⟩ := h_no_lonely t
  rw [← mem_unsafeOf_iff] at hi_unsafe
  have hnot0 : t ∉ unsafeOf speeds ⟨0, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨0, by omega⟩ (hpos _) 0 t
    · rw [show ((0:ℤ):ℝ) + 1/6 = 1/6 from by norm_num, div_div]
      rw [hv1_def] at htL; exact htL
    · rw [show ((0:ℤ):ℝ) + 5/6 = 5/6 from by norm_num, div_div]
      calc t ≤ 5 / (6 * v4) := htR
        _ ≤ 5 / (6 * (speeds ⟨0, by omega⟩ : ℝ)) := by
            rw [hv1_def] at hv1_le_v4 hv1_pos
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            nlinarith [hv1_le_v4, hv1_pos, hv4_pos]
  have hnot1 : t ∉ unsafeOf speeds ⟨1, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨1, by omega⟩ (hpos _) 0 t
    · rw [show ((0:ℤ):ℝ) + 1/6 = 1/6 from by norm_num, div_div]
      calc (1 : ℝ) / (6 * (speeds ⟨1, by omega⟩ : ℝ))
          ≤ 1 / (6 * v1) := by
            rw [hv2_def] at hv1_le_v2
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            nlinarith [hv1_le_v2, hv1_pos, hv2_pos]
        _ ≤ t := by rw [hv1_def] at htL; exact htL
    · rw [show ((0:ℤ):ℝ) + 5/6 = 5/6 from by norm_num, div_div]
      calc t ≤ 5 / (6 * v4) := htR
        _ ≤ 5 / (6 * (speeds ⟨1, by omega⟩ : ℝ)) := by
            rw [hv2_def] at hv2_le_v4
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            nlinarith [hv2_le_v4, hv2_pos, hv4_pos]
  have hnot2 : t ∉ unsafeOf speeds ⟨2, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨2, by omega⟩ (hpos _) 0 t
    · rw [show ((0:ℤ):ℝ) + 1/6 = 1/6 from by norm_num, div_div]
      calc (1 : ℝ) / (6 * (speeds ⟨2, by omega⟩ : ℝ))
          ≤ 1 / (6 * v1) := by
            rw [hv3_def] at hv1_le_v3
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            nlinarith [hv1_le_v3, hv1_pos, hv3_pos]
        _ ≤ t := by rw [hv1_def] at htL; exact htL
    · rw [show ((0:ℤ):ℝ) + 5/6 = 5/6 from by norm_num, div_div]
      calc t ≤ 5 / (6 * v4) := htR
        _ ≤ 5 / (6 * (speeds ⟨2, by omega⟩ : ℝ)) := by
            rw [hv3_def] at hv3_le_v4
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            nlinarith [hv3_le_v4, hv3_pos, hv4_pos]
  have hnot3 : t ∉ unsafeOf speeds ⟨3, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨3, by omega⟩ (hpos _) 0 t
    · rw [show ((0:ℤ):ℝ) + 1/6 = 1/6 from by norm_num, div_div]
      calc (1 : ℝ) / (6 * (speeds ⟨3, by omega⟩ : ℝ))
          ≤ 1 / (6 * v1) := by
            rw [hv4_def] at hv1_le_v4
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            nlinarith [hv1_le_v4, hv1_pos, hv4_pos]
        _ ≤ t := by rw [hv1_def] at htL; exact htL
    · rw [show ((0:ℤ):ℝ) + 5/6 = 5/6 from by norm_num, div_div]
      rw [hv4_def] at htR; exact htR
  fin_cases i
  · exact absurd hi_unsafe hnot0
  · exact absurd hi_unsafe hnot1
  · exact absurd hi_unsafe hnot2
  · exact absurd hi_unsafe hnot3
  · exact hi_unsafe

/-- **§6.5.1 step-1 kernel.** A runner-5 block index `j ≥ 2` for the
    1234-gap contradicts (62) + (63): the bracketing forces
    `875 (6j−1) v₁ < 675 (6j+1) v₁`, i.e. `1200 j < 1550`. -/
lemma bhk_s6_651_step1_kernel (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (h62 : 25 * (speeds ⟨3, by omega⟩ : ℤ) < 27 * (speeds ⟨2, by omega⟩ : ℤ))
    (h63 : 7 * (speeds ⟨2, by omega⟩ : ℤ) < 25 * (speeds ⟨0, by omega⟩ : ℤ))
    (j : ℤ) (hj : 2 ≤ j)
    (hjL : (6 * j - 1) * (speeds ⟨0, by omega⟩ : ℤ) <
              (speeds ⟨4, by omega⟩ : ℤ))
    (hjR : 5 * (speeds ⟨4, by omega⟩ : ℤ) <
              (6 * j + 1) * (speeds ⟨3, by omega⟩ : ℤ)) :
    False := by
  have hv1 : (0 : ℤ) < (speeds ⟨0, by omega⟩ : ℤ) := by
    exact_mod_cast hpos ⟨0, by omega⟩
  have h6jp1_pos : (0 : ℤ) < 6 * j + 1 := by linarith
  have step62 : (6 * j + 1) * (25 * (speeds ⟨3, by omega⟩ : ℤ)) <
                (6 * j + 1) * (27 * (speeds ⟨2, by omega⟩ : ℤ)) :=
    mul_lt_mul_of_pos_left h62 h6jp1_pos
  have step63 : (6 * j + 1) * (7 * (speeds ⟨2, by omega⟩ : ℤ)) <
                (6 * j + 1) * (25 * (speeds ⟨0, by omega⟩ : ℤ)) :=
    mul_lt_mul_of_pos_left h63 h6jp1_pos
  have hkey : (0 : ℤ) < (1200 * j - 1550) * (speeds ⟨0, by omega⟩ : ℤ) :=
    mul_pos (by linarith) hv1
  nlinarith [step62, step63, hjL, hjR, hkey]

/-- **§6.5.1 derivation of the (64) bracketing.** From the 1234-gap
    inclusion, runner 5's covering block index is forced to `1`:
    `5 v₁ < v₅` and `5 v₅ < 7 v₄`. -/
lemma bhk_s6_651_find_64 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (h62 : 25 * (speeds ⟨3, by omega⟩ : ℤ) < 27 * (speeds ⟨2, by omega⟩ : ℤ))
    (h63 : 7 * (speeds ⟨2, by omega⟩ : ℤ) < 25 * (speeds ⟨0, by omega⟩ : ℤ))
    (h_incl : Set.Icc (1 / (6 * (speeds ⟨0, by omega⟩ : ℝ)))
                       (5 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
              ⊆ unsafeOf speeds ⟨4, by omega⟩) :
    (5 * (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ)) ∧
    (5 * (speeds ⟨4, by omega⟩ : ℤ) < 7 * (speeds ⟨3, by omega⟩ : ℤ)) := by
  have hv1 : 0 < speeds ⟨0, by omega⟩ := hpos _
  have hv4 : 0 < speeds ⟨3, by omega⟩ := hpos _
  have hv5 : 0 < speeds ⟨4, by omega⟩ := hpos _
  have hv1R : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hv1
  have hv4R : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hv4
  have h6v1R : (0 : ℝ) < 6 * (speeds ⟨0, by omega⟩ : ℝ) := by positivity
  have h6v4R : (0 : ℝ) < 6 * (speeds ⟨3, by omega⟩ : ℝ) := by positivity
  set a : ℝ := 1 / (6 * (speeds ⟨0, by omega⟩ : ℝ)) with ha_def
  set b : ℝ := 5 / (6 * (speeds ⟨3, by omega⟩ : ℝ)) with hb_def
  -- a ≤ b ⟺ v_4 ≤ 5 v_1: (62)+(63) give 175 v_4 < 189 v_3 < 675 v_1.
  have hab : a ≤ b := by
    rw [ha_def, hb_def, div_le_div_iff₀ h6v1R h6v4R]
    have h62R : (25 : ℝ) * (speeds ⟨3, by omega⟩ : ℝ) <
        27 * (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast h62
    have h63R : (7 : ℝ) * (speeds ⟨2, by omega⟩ : ℝ) <
        25 * (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast h63
    nlinarith [h62R, h63R]
  obtain ⟨k, hk_lo, hk_hi⟩ := block_containment speeds ⟨4, by omega⟩ hv5 a b hab h_incl
  have hva_eq : (speeds ⟨4, by omega⟩ : ℝ) * a =
                (speeds ⟨4, by omega⟩ : ℝ) / (6 * (speeds ⟨0, by omega⟩ : ℝ)) := by
    rw [ha_def]; ring
  have hvb_eq : (speeds ⟨4, by omega⟩ : ℝ) * b =
                5 * (speeds ⟨4, by omega⟩ : ℝ) / (6 * (speeds ⟨3, by omega⟩ : ℝ)) := by
    rw [hb_def]; ring
  rw [hva_eq] at hk_lo
  rw [hvb_eq] at hk_hi
  have hjL_R : (6 * (k : ℝ) - 1) * (speeds ⟨0, by omega⟩ : ℝ) <
               (speeds ⟨4, by omega⟩ : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hk_lo h6v1R
    have hclear : ((speeds ⟨4, by omega⟩ : ℝ) / (6 * (speeds ⟨0, by omega⟩ : ℝ))) *
                  (6 * (speeds ⟨0, by omega⟩ : ℝ)) = (speeds ⟨4, by omega⟩ : ℝ) := by
      field_simp
    nlinarith [hmul, hclear]
  have hjR_R : 5 * (speeds ⟨4, by omega⟩ : ℝ) <
               (6 * (k : ℝ) + 1) * (speeds ⟨3, by omega⟩ : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hk_hi h6v4R
    have hclear : (5 * (speeds ⟨4, by omega⟩ : ℝ) / (6 * (speeds ⟨3, by omega⟩ : ℝ))) *
                  (6 * (speeds ⟨3, by omega⟩ : ℝ)) = 5 * (speeds ⟨4, by omega⟩ : ℝ) := by
      field_simp
    nlinarith [hmul, hclear]
  have hjL : (6 * k - 1) * (speeds ⟨0, by omega⟩ : ℤ) <
             (speeds ⟨4, by omega⟩ : ℤ) := by exact_mod_cast hjL_R
  have hjR : 5 * (speeds ⟨4, by omega⟩ : ℤ) <
             (6 * k + 1) * (speeds ⟨3, by omega⟩ : ℤ) := by exact_mod_cast hjR_R
  have hv4_int : (0 : ℤ) < (speeds ⟨3, by omega⟩ : ℤ) := by exact_mod_cast hv4
  have hv5_int : (0 : ℤ) < (speeds ⟨4, by omega⟩ : ℤ) := by exact_mod_cast hv5
  have hv45 : (speeds ⟨3, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ) := by
    have hflt : (⟨3, by omega⟩ : Fin 5) < ⟨4, by omega⟩ :=
      Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast hmono hflt
  have hk_ge_1 : 1 ≤ k := by nlinarith [hjR, hv45, hv4_int, hv5_int]
  have hk_le_1 : k ≤ 1 := by
    by_contra hk_gt
    push_neg at hk_gt
    exact bhk_s6_651_step1_kernel speeds hpos h62 h63 k hk_gt hjL hjR
  have hk_eq_1 : k = 1 := le_antisymm hk_le_1 hk_ge_1
  subst hk_eq_1
  refine ⟨?_, ?_⟩
  · linarith [hjL]
  · linarith [hjR]

-- Large sequential gap-exclusion proof; the default heartbeat budget is
-- exceeded by the five per-runner `nlinarith` window checks.
set_option maxHeartbeats 800000 in
/-- **§6.5.1: runner 2 must cover `t = 7/(6 v₃)`.** At `t₁ = 7/(6 v₃)`
    runners 1, 3, 4, 5 sit in safe gaps (using (62), (63), (64));
    failure of loneliness forces runner 2 into its `k = 1` block, whose
    left edge reads `5 v₃ < 7 v₂`. -/
lemma bhk_s6_651_find_2b (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (h2v2 : (speeds ⟨2, by omega⟩ : ℤ) ≤ 2 * (speeds ⟨1, by omega⟩ : ℤ))
    (h62 : 25 * (speeds ⟨3, by omega⟩ : ℤ) < 27 * (speeds ⟨2, by omega⟩ : ℤ))
    (h64b : 5 * (speeds ⟨4, by omega⟩ : ℤ) < 7 * (speeds ⟨3, by omega⟩ : ℤ))
    (h63 : 7 * (speeds ⟨2, by omega⟩ : ℤ) < 25 * (speeds ⟨0, by omega⟩ : ℤ))
    (h_no_lonely : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1/6) :
    5 * (speeds ⟨2, by omega⟩ : ℤ) < 7 * (speeds ⟨1, by omega⟩ : ℤ) := by
  set v1 : ℝ := (speeds ⟨0, by omega⟩ : ℝ) with hv1_def
  set v2 : ℝ := (speeds ⟨1, by omega⟩ : ℝ) with hv2_def
  set v3 : ℝ := (speeds ⟨2, by omega⟩ : ℝ) with hv3_def
  set v4 : ℝ := (speeds ⟨3, by omega⟩ : ℝ) with hv4_def
  set v5 : ℝ := (speeds ⟨4, by omega⟩ : ℝ) with hv5_def
  have hv1_pos : 0 < v1 := by rw [hv1_def]; exact_mod_cast hpos _
  have hv2_pos : 0 < v2 := by rw [hv2_def]; exact_mod_cast hpos _
  have hv3_pos : 0 < v3 := by rw [hv3_def]; exact_mod_cast hpos _
  have hv4_pos : 0 < v4 := by rw [hv4_def]; exact_mod_cast hpos _
  have hv5_pos : 0 < v5 := by rw [hv5_def]; exact_mod_cast hpos _
  have hsmallR : 3 * v1 < v3 := by rw [hv1_def, hv3_def]; exact_mod_cast hsmall
  have h62R : 25 * v4 < 27 * v3 := by rw [hv4_def, hv3_def]; exact_mod_cast h62
  have h63R : 7 * v3 < 25 * v1 := by rw [hv3_def, hv1_def]; exact_mod_cast h63
  have h64bR : 5 * v5 < 7 * v4 := by rw [hv5_def, hv4_def]; exact_mod_cast h64b
  have hv34R : v3 < v4 := by
    rw [hv3_def, hv4_def]
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (2:ℕ) < 3 by omega))
  have hv35R : v3 < v5 := by
    rw [hv3_def, hv5_def]
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (2:ℕ) < 4 by omega))
  set t : ℝ := 7 / (6 * v3) with ht_def
  obtain ⟨i, hi_unsafe⟩ := h_no_lonely t
  rw [← mem_unsafeOf_iff] at hi_unsafe
  -- Runner 1: k=0 gap [1/(6 v_1), 5/(6 v_1)].
  have hnot0 : t ∉ unsafeOf speeds ⟨0, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨0, by omega⟩ (hpos _) 0 t
    · rw [show ((0:ℤ):ℝ) + 1/6 = 1/6 from by norm_num, div_div, ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 6 v_3 ≤ 42 v_1 from 7 v_3 < 25 v_1.
      nlinarith [h63R, hv1_pos]
    · rw [show ((0:ℤ):ℝ) + 5/6 = 5/6 from by norm_num, div_div, ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 42 v_1 ≤ 30 v_3 from 3 v_1 < v_3.
      nlinarith [hsmallR, hv3_pos]
  -- Runner 3: k=1 gap [7/(6 v_3), 11/(6 v_3)]; t is the left boundary.
  have hnot2 : t ∉ unsafeOf speeds ⟨2, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨2, by omega⟩ (hpos _) 1 t
    · rw [show ((1:ℤ):ℝ) + 1/6 = 7/6 from by norm_num, div_div, ht_def]
    · rw [show ((1:ℤ):ℝ) + 5/6 = 11/6 from by norm_num, div_div, ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hv3_pos]
  -- Runner 4: k=1 gap [7/(6 v_4), 11/(6 v_4)].
  have hnot3 : t ∉ unsafeOf speeds ⟨3, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨3, by omega⟩ (hpos _) 1 t
    · rw [show ((1:ℤ):ℝ) + 1/6 = 7/6 from by norm_num, div_div, ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 42 v_3 ≤ 42 v_4 from v_3 < v_4.
      nlinarith [hv34R]
    · rw [show ((1:ℤ):ℝ) + 5/6 = 11/6 from by norm_num, div_div, ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 42 v_4 ≤ 66 v_3 from 25 v_4 < 27 v_3.
      nlinarith [h62R, hv3_pos]
  -- Runner 5: k=1 gap [7/(6 v_5), 11/(6 v_5)].
  have hnot4 : t ∉ unsafeOf speeds ⟨4, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨4, by omega⟩ (hpos _) 1 t
    · rw [show ((1:ℤ):ℝ) + 1/6 = 7/6 from by norm_num, div_div, ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 42 v_3 ≤ 42 v_5 from v_3 < v_5.
      nlinarith [hv35R]
    · rw [show ((1:ℤ):ℝ) + 5/6 = 11/6 from by norm_num, div_div, ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 42 v_5 ≤ 66 v_3 from 125 v_5 < 175 v_4 < 189 v_3.
      nlinarith [h64bR, h62R, hv3_pos]
  -- Hence runner 2 (= i = 1) must be unsafe at t.
  have hi_eq_1 : i = ⟨1, by omega⟩ := by
    fin_cases i
    · exact absurd hi_unsafe hnot0
    · rfl
    · exact absurd hi_unsafe hnot2
    · exact absurd hi_unsafe hnot3
    · exact absurd hi_unsafe hnot4
  rw [hi_eq_1] at hi_unsafe
  rw [mem_unsafeOf_iff_bhkB] at hi_unsafe
  obtain ⟨k, hk⟩ := hi_unsafe
  -- hk : |v_2 · t - k| < 1/6 where t = 7/(6 v_3).
  have hk_lo_R : ((k : ℝ) - 1/6) < v2 * t := by
    have := neg_lt_of_abs_lt hk; linarith
  have hk_hi_R : v2 * t < ((k : ℝ) + 1/6) := by
    have := lt_of_abs_lt hk; linarith
  have hv2t_eq : v2 * t = 7 * v2 / (6 * v3) := by rw [ht_def]; ring
  rw [hv2t_eq] at hk_lo_R hk_hi_R
  have h6v3_pos : (0 : ℝ) < 6 * v3 := by positivity
  have hkL_R : (6 * (k : ℝ) - 1) * v3 < 7 * v2 := by
    have hmul := mul_lt_mul_of_pos_right hk_lo_R h6v3_pos
    have hclear : (7 * v2 / (6 * v3)) * (6 * v3) = 7 * v2 := by field_simp
    nlinarith [hmul, hclear]
  have hkR_R : 7 * v2 < (6 * (k : ℝ) + 1) * v3 := by
    have hmul := mul_lt_mul_of_pos_right hk_hi_R h6v3_pos
    have hclear : (7 * v2 / (6 * v3)) * (6 * v3) = 7 * v2 := by field_simp
    nlinarith [hmul, hclear]
  have hkL : (6 * k - 1) * (speeds ⟨2, by omega⟩ : ℤ) <
             7 * (speeds ⟨1, by omega⟩ : ℤ) := by
    have := hkL_R; rw [hv3_def, hv2_def] at this; exact_mod_cast this
  have hkR : 7 * (speeds ⟨1, by omega⟩ : ℤ) <
             (6 * k + 1) * (speeds ⟨2, by omega⟩ : ℤ) := by
    have := hkR_R; rw [hv2_def, hv3_def] at this; exact_mod_cast this
  have hv2_int : (0 : ℤ) < (speeds ⟨1, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  have hv3_int : (0 : ℤ) < (speeds ⟨2, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  have hv23 : (speeds ⟨1, by omega⟩ : ℤ) < (speeds ⟨2, by omega⟩ : ℤ) := by
    have hflt : (⟨1, by omega⟩ : Fin 5) < ⟨2, by omega⟩ :=
      Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast hmono hflt
  -- Force k = 1: k ≤ 0 gives 7 v_2 < v_3 ≤ 2 v_2; k ≥ 2 gives 11 v_3 < 7 v_2 < 7 v_3.
  have hk_ge_1 : 1 ≤ k := by
    by_contra hk_lt
    push_neg at hk_lt
    have hstep : (6 * k + 1) * (speeds ⟨2, by omega⟩ : ℤ) ≤
                 1 * (speeds ⟨2, by omega⟩ : ℤ) :=
      mul_le_mul_of_nonneg_right (by omega) (le_of_lt hv3_int)
    linarith [hkR, h2v2, hv2_int]
  have hk_le_1 : k ≤ 1 := by
    by_contra hk_gt
    push_neg at hk_gt
    have hstep : 11 * (speeds ⟨2, by omega⟩ : ℤ) ≤
                 (6 * k - 1) * (speeds ⟨2, by omega⟩ : ℤ) :=
      mul_le_mul_of_nonneg_right (by omega) (le_of_lt hv3_int)
    linarith [hkL, hv23, hv3_int]
  have hk_eq_1 : k = 1 := le_antisymm hk_le_1 hk_ge_1
  subst hk_eq_1
  linarith [hkL]

-- Large sequential gap-exclusion proof; the default heartbeat budget is
-- exceeded by the five per-runner `nlinarith` window checks.
set_option maxHeartbeats 800000 in
/-- **§6.5.1: runner 5 must cover `t = 7/(6 v₂)` in its `k = 2` block.**
    At `t₂ = 7/(6 v₂)` runners 1, 2, 3, 4 sit in safe gaps (using (62),
    (63), (64) and `5 v₃ < 7 v₂`); failure of loneliness forces runner 5
    into its `k = 2` block: `11 v₂ < 7 v₅ < 13 v₂`. -/
lemma bhk_s6_651_find_5b (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (h62 : 25 * (speeds ⟨3, by omega⟩ : ℤ) < 27 * (speeds ⟨2, by omega⟩ : ℤ))
    (h63 : 7 * (speeds ⟨2, by omega⟩ : ℤ) < 25 * (speeds ⟨0, by omega⟩ : ℤ))
    (h64a : 5 * (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ))
    (h64b : 5 * (speeds ⟨4, by omega⟩ : ℤ) < 7 * (speeds ⟨3, by omega⟩ : ℤ))
    (h2b : 5 * (speeds ⟨2, by omega⟩ : ℤ) < 7 * (speeds ⟨1, by omega⟩ : ℤ))
    (h_no_lonely : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1/6) :
    (11 * (speeds ⟨1, by omega⟩ : ℤ) < 7 * (speeds ⟨4, by omega⟩ : ℤ)) ∧
    (7 * (speeds ⟨4, by omega⟩ : ℤ) < 13 * (speeds ⟨1, by omega⟩ : ℤ)) := by
  set v1 : ℝ := (speeds ⟨0, by omega⟩ : ℝ) with hv1_def
  set v2 : ℝ := (speeds ⟨1, by omega⟩ : ℝ) with hv2_def
  set v3 : ℝ := (speeds ⟨2, by omega⟩ : ℝ) with hv3_def
  set v4 : ℝ := (speeds ⟨3, by omega⟩ : ℝ) with hv4_def
  set v5 : ℝ := (speeds ⟨4, by omega⟩ : ℝ) with hv5_def
  have hv1_pos : 0 < v1 := by rw [hv1_def]; exact_mod_cast hpos _
  have hv2_pos : 0 < v2 := by rw [hv2_def]; exact_mod_cast hpos _
  have hv3_pos : 0 < v3 := by rw [hv3_def]; exact_mod_cast hpos _
  have hv4_pos : 0 < v4 := by rw [hv4_def]; exact_mod_cast hpos _
  have hv5_pos : 0 < v5 := by rw [hv5_def]; exact_mod_cast hpos _
  have hsmallR : 3 * v1 < v3 := by rw [hv1_def, hv3_def]; exact_mod_cast hsmall
  have h62R : 25 * v4 < 27 * v3 := by rw [hv4_def, hv3_def]; exact_mod_cast h62
  have h63R : 7 * v3 < 25 * v1 := by rw [hv3_def, hv1_def]; exact_mod_cast h63
  have h2bR : 5 * v3 < 7 * v2 := by rw [hv3_def, hv2_def]; exact_mod_cast h2b
  have hv23R : v2 < v3 := by
    rw [hv2_def, hv3_def]
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (1:ℕ) < 2 by omega))
  have hv24R : v2 < v4 := by
    rw [hv2_def, hv4_def]
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (1:ℕ) < 3 by omega))
  set t : ℝ := 7 / (6 * v2) with ht_def
  obtain ⟨i, hi_unsafe⟩ := h_no_lonely t
  rw [← mem_unsafeOf_iff] at hi_unsafe
  -- Runner 1: k=0 gap [1/(6 v_1), 5/(6 v_1)].
  have hnot0 : t ∉ unsafeOf speeds ⟨0, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨0, by omega⟩ (hpos _) 0 t
    · rw [show ((0:ℤ):ℝ) + 1/6 = 1/6 from by norm_num, div_div, ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 6 v_2 ≤ 42 v_1 from v_2 < v_3, 7 v_3 < 25 v_1.
      nlinarith [hv23R, h63R, hv1_pos]
    · rw [show ((0:ℤ):ℝ) + 5/6 = 5/6 from by norm_num, div_div, ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 42 v_1 ≤ 30 v_2 from 35 v_2 > 25 v_3 > 75 v_1.
      nlinarith [h2bR, hsmallR, hv2_pos]
  -- Runner 2: k=1 gap [7/(6 v_2), 11/(6 v_2)]; t is the left boundary.
  have hnot1 : t ∉ unsafeOf speeds ⟨1, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨1, by omega⟩ (hpos _) 1 t
    · rw [show ((1:ℤ):ℝ) + 1/6 = 7/6 from by norm_num, div_div, ht_def]
    · rw [show ((1:ℤ):ℝ) + 5/6 = 11/6 from by norm_num, div_div, ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hv2_pos]
  -- Runner 3: k=1 gap [7/(6 v_3), 11/(6 v_3)].
  have hnot2 : t ∉ unsafeOf speeds ⟨2, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨2, by omega⟩ (hpos _) 1 t
    · rw [show ((1:ℤ):ℝ) + 1/6 = 7/6 from by norm_num, div_div, ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 42 v_2 ≤ 42 v_3 from v_2 < v_3.
      nlinarith [hv23R]
    · rw [show ((1:ℤ):ℝ) + 5/6 = 11/6 from by norm_num, div_div, ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 42 v_3 ≤ 66 v_2 from 5 v_3 < 7 v_2.
      nlinarith [h2bR, hv2_pos]
  -- Runner 4: k=1 gap [7/(6 v_4), 11/(6 v_4)].
  have hnot3 : t ∉ unsafeOf speeds ⟨3, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨3, by omega⟩ (hpos _) 1 t
    · rw [show ((1:ℤ):ℝ) + 1/6 = 7/6 from by norm_num, div_div, ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 42 v_2 ≤ 42 v_4 from v_2 < v_4.
      nlinarith [hv24R]
    · rw [show ((1:ℤ):ℝ) + 5/6 = 11/6 from by norm_num, div_div, ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 42 v_4 ≤ 66 v_2 from 875 v_4 < 945 v_3 < 1323 v_2.
      nlinarith [h62R, h2bR, hv2_pos]
  -- Hence runner 5 (= i = 4) must be unsafe at t.
  have hi_eq_4 : i = ⟨4, by omega⟩ := by
    fin_cases i
    · exact absurd hi_unsafe hnot0
    · exact absurd hi_unsafe hnot1
    · exact absurd hi_unsafe hnot2
    · exact absurd hi_unsafe hnot3
    · rfl
  rw [hi_eq_4] at hi_unsafe
  rw [mem_unsafeOf_iff_bhkB] at hi_unsafe
  obtain ⟨k, hk⟩ := hi_unsafe
  -- hk : |v_5 · t - k| < 1/6 where t = 7/(6 v_2).
  have hk_lo_R : ((k : ℝ) - 1/6) < v5 * t := by
    have := neg_lt_of_abs_lt hk; linarith
  have hk_hi_R : v5 * t < ((k : ℝ) + 1/6) := by
    have := lt_of_abs_lt hk; linarith
  have hv5t_eq : v5 * t = 7 * v5 / (6 * v2) := by rw [ht_def]; ring
  rw [hv5t_eq] at hk_lo_R hk_hi_R
  have h6v2_pos : (0 : ℝ) < 6 * v2 := by positivity
  have hkL_R : (6 * (k : ℝ) - 1) * v2 < 7 * v5 := by
    have hmul := mul_lt_mul_of_pos_right hk_lo_R h6v2_pos
    have hclear : (7 * v5 / (6 * v2)) * (6 * v2) = 7 * v5 := by field_simp
    nlinarith [hmul, hclear]
  have hkR_R : 7 * v5 < (6 * (k : ℝ) + 1) * v2 := by
    have hmul := mul_lt_mul_of_pos_right hk_hi_R h6v2_pos
    have hclear : (7 * v5 / (6 * v2)) * (6 * v2) = 7 * v5 := by field_simp
    nlinarith [hmul, hclear]
  have hkL : (6 * k - 1) * (speeds ⟨1, by omega⟩ : ℤ) <
             7 * (speeds ⟨4, by omega⟩ : ℤ) := by
    have := hkL_R; rw [hv2_def, hv5_def] at this; exact_mod_cast this
  have hkR : 7 * (speeds ⟨4, by omega⟩ : ℤ) <
             (6 * k + 1) * (speeds ⟨1, by omega⟩ : ℤ) := by
    have := hkR_R; rw [hv5_def, hv2_def] at this; exact_mod_cast this
  have hv2_int : (0 : ℤ) < (speeds ⟨1, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  have hv25 : (speeds ⟨1, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ) := by
    have hflt : (⟨1, by omega⟩ : Fin 5) < ⟨4, by omega⟩ :=
      Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast hmono hflt
  -- Force k = 2: k ≤ 1 gives 7 v_5 < 7 v_2; k ≥ 3 gives 17 v_2 < 7 v_5,
  -- contradicting 875 v_5 < 1323 v_3 and 945 v_3 < 1323 v_2.
  have hk_ge_2 : 2 ≤ k := by
    by_contra hk_lt
    push_neg at hk_lt
    have hstep : (6 * k + 1) * (speeds ⟨1, by omega⟩ : ℤ) ≤
                 7 * (speeds ⟨1, by omega⟩ : ℤ) :=
      mul_le_mul_of_nonneg_right (by omega) (le_of_lt hv2_int)
    linarith [hkR, hv25]
  have hk_le_2 : k ≤ 2 := by
    by_contra hk_gt
    push_neg at hk_gt
    have hstep : 17 * (speeds ⟨1, by omega⟩ : ℤ) ≤
                 (6 * k - 1) * (speeds ⟨1, by omega⟩ : ℤ) :=
      mul_le_mul_of_nonneg_right (by omega) (le_of_lt hv2_int)
    linarith [hkL, h64b, h62, h2b, hv2_int]
  have hk_eq_2 : k = 2 := le_antisymm hk_le_2 hk_ge_2
  subst hk_eq_2
  exact ⟨by linarith [hkL], by linarith [hkR]⟩

-- Large sequential gap-exclusion proof; the default heartbeat budget is
-- exceeded by the five per-runner `nlinarith` window checks.
set_option maxHeartbeats 800000 in
/-- **§6.5.1 final witness: `t = 13/(6 v₅)` is uncovered.** With the full
    bound chain (62), (63), (64), `5 v₃ < 7 v₂`, `11 v₂ < 7 v₅ < 13 v₂`,
    every runner sits in a safe gap at `t₃ = 13/(6 v₅)`, contradicting
    the failure of loneliness. -/
lemma bhk_s6_651_final (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (h62 : 25 * (speeds ⟨3, by omega⟩ : ℤ) < 27 * (speeds ⟨2, by omega⟩ : ℤ))
    (h63 : 7 * (speeds ⟨2, by omega⟩ : ℤ) < 25 * (speeds ⟨0, by omega⟩ : ℤ))
    (h64a : 5 * (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ))
    (h64b : 5 * (speeds ⟨4, by omega⟩ : ℤ) < 7 * (speeds ⟨3, by omega⟩ : ℤ))
    (hC1 : 11 * (speeds ⟨1, by omega⟩ : ℤ) < 7 * (speeds ⟨4, by omega⟩ : ℤ))
    (hC2 : 7 * (speeds ⟨4, by omega⟩ : ℤ) < 13 * (speeds ⟨1, by omega⟩ : ℤ))
    (h_no_lonely : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1/6) :
    False := by
  set v1 : ℝ := (speeds ⟨0, by omega⟩ : ℝ) with hv1_def
  set v2 : ℝ := (speeds ⟨1, by omega⟩ : ℝ) with hv2_def
  set v3 : ℝ := (speeds ⟨2, by omega⟩ : ℝ) with hv3_def
  set v4 : ℝ := (speeds ⟨3, by omega⟩ : ℝ) with hv4_def
  set v5 : ℝ := (speeds ⟨4, by omega⟩ : ℝ) with hv5_def
  have hv1_pos : 0 < v1 := by rw [hv1_def]; exact_mod_cast hpos _
  have hv2_pos : 0 < v2 := by rw [hv2_def]; exact_mod_cast hpos _
  have hv3_pos : 0 < v3 := by rw [hv3_def]; exact_mod_cast hpos _
  have hv4_pos : 0 < v4 := by rw [hv4_def]; exact_mod_cast hpos _
  have hv5_pos : 0 < v5 := by rw [hv5_def]; exact_mod_cast hpos _
  have h62R : 25 * v4 < 27 * v3 := by rw [hv4_def, hv3_def]; exact_mod_cast h62
  have h63R : 7 * v3 < 25 * v1 := by rw [hv3_def, hv1_def]; exact_mod_cast h63
  have h64aR : 5 * v1 < v5 := by rw [hv1_def, hv5_def]; exact_mod_cast h64a
  have h64bR : 5 * v5 < 7 * v4 := by rw [hv5_def, hv4_def]; exact_mod_cast h64b
  have hC1R : 11 * v2 < 7 * v5 := by rw [hv2_def, hv5_def]; exact_mod_cast hC1
  have hC2R : 7 * v5 < 13 * v2 := by rw [hv5_def, hv2_def]; exact_mod_cast hC2
  set t : ℝ := 13 / (6 * v5) with ht_def
  obtain ⟨i, hi_unsafe⟩ := h_no_lonely t
  rw [← mem_unsafeOf_iff] at hi_unsafe
  -- Runner 1: k=0 gap [1/(6 v_1), 5/(6 v_1)].
  have hnot0 : t ∉ unsafeOf speeds ⟨0, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨0, by omega⟩ (hpos _) 0 t
    · rw [show ((0:ℤ):ℝ) + 1/6 = 1/6 from by norm_num, div_div, ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 6 v_5 ≤ 78 v_1 from 875 v_5 < 1323 v_3 < 4725 v_1.
      nlinarith [h64bR, h62R, h63R, hv1_pos]
    · rw [show ((0:ℤ):ℝ) + 5/6 = 5/6 from by norm_num, div_div, ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 78 v_1 ≤ 30 v_5 from 5 v_1 < v_5.
      nlinarith [h64aR, hv1_pos]
  -- Runner 2: k=1 gap [7/(6 v_2), 11/(6 v_2)].
  have hnot1 : t ∉ unsafeOf speeds ⟨1, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨1, by omega⟩ (hpos _) 1 t
    · rw [show ((1:ℤ):ℝ) + 1/6 = 7/6 from by norm_num, div_div, ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 42 v_5 ≤ 78 v_2 from 7 v_5 < 13 v_2.
      nlinarith [hC2R, hv2_pos]
    · rw [show ((1:ℤ):ℝ) + 5/6 = 11/6 from by norm_num, div_div, ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 78 v_2 ≤ 66 v_5 from 11 v_2 < 7 v_5.
      nlinarith [hC1R, hv5_pos]
  -- Runner 3: k=1 gap [7/(6 v_3), 11/(6 v_3)].
  have hnot2 : t ∉ unsafeOf speeds ⟨2, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨2, by omega⟩ (hpos _) 1 t
    · rw [show ((1:ℤ):ℝ) + 1/6 = 7/6 from by norm_num, div_div, ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 42 v_5 ≤ 78 v_3 from 875 v_5 < 1323 v_3.
      nlinarith [h64bR, h62R, hv3_pos]
    · rw [show ((1:ℤ):ℝ) + 5/6 = 11/6 from by norm_num, div_div, ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 78 v_3 ≤ 66 v_5 from 7 v_3 < 25 v_1 < 5 v_5.
      nlinarith [h63R, h64aR, hv5_pos]
  -- Runner 4: k=1 gap [7/(6 v_4), 11/(6 v_4)].
  have hnot3 : t ∉ unsafeOf speeds ⟨3, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨3, by omega⟩ (hpos _) 1 t
    · rw [show ((1:ℤ):ℝ) + 1/6 = 7/6 from by norm_num, div_div, ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 42 v_5 ≤ 78 v_4 from 5 v_5 < 7 v_4.
      nlinarith [h64bR, hv4_pos]
    · rw [show ((1:ℤ):ℝ) + 5/6 = 11/6 from by norm_num, div_div, ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 78 v_4 ≤ 66 v_5 from 175 v_4 < 189 v_3 = 27·(7 v_3) < 135 v_5.
      nlinarith [h62R, h63R, h64aR, hv5_pos]
  -- Runner 5: k=2 gap [13/(6 v_5), 17/(6 v_5)]; t is the left boundary.
  have hnot4 : t ∉ unsafeOf speeds ⟨4, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨4, by omega⟩ (hpos _) 2 t
    · rw [show ((2:ℤ):ℝ) + 1/6 = 13/6 from by norm_num, div_div, ht_def]
    · rw [show ((2:ℤ):ℝ) + 5/6 = 17/6 from by norm_num, div_div, ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hv5_pos]
  fin_cases i
  · exact absurd hi_unsafe hnot0
  · exact absurd hi_unsafe hnot1
  · exact absurd hi_unsafe hnot2
  · exact absurd hi_unsafe hnot3
  · exact absurd hi_unsafe hnot4

/-- **BHK Case 6.5.1 kernel (PROVED — BHK p. 43, (62)–(64)).** The hard
    core of the `n = 5`, `(1/5, −2/5)` case, with the forced bounds
    (62) `25 v₄ < 27 v₃` and (63) `7 v₃ < 25 v₁` as hypotheses. By
    contradiction: the `[1/(6v₁), 5/(6v₄)]` 1234-gap must lie in a single
    runner-5 block, forced to `j = 1` (chain (64): `5v₁ < v₅`,
    `5v₅ < 7v₄`); then runner 2 must cover `t = 7/(6v₃)` (giving
    `5v₃ < 7v₂`), runner 5 must cover `t = 7/(6v₂)` in its second block
    (giving `11v₂ < 7v₅ < 13v₂`), and finally `t = 13/(6v₅)` is
    uncovered. -/
lemma bhk_s6_case_651_kernel (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (D K : ℕ) (hD2 : 2 ≤ D) (hK2 : 2 ≤ K)
    (hv3 : speeds ⟨2, by omega⟩ = K * D)
    (hv2 : speeds ⟨1, by omega⟩ = (K - 1) * D)
    (h43 : 3 * speeds ⟨3, by omega⟩ < 4 * speeds ⟨2, by omega⟩)
    (c₁ c₄ g : ℕ) (hgpos : 0 < g)
    (hd : g * 5 = D) (hc1 : g * c₁ = speeds ⟨0, by omega⟩)
    (hc4 : g * c₄ = speeds ⟨3, by omega⟩)
    (hmem : ((1 : ZMod 5), (-2 : ZMod 5)) ∈
      AddSubgroup.zmultiples ((c₁ : ZMod 5), (c₄ : ZMod 5)))
    (h62 : 25 * speeds ⟨3, by omega⟩ < 27 * speeds ⟨2, by omega⟩)
    (h63 : 7 * speeds ⟨2, by omega⟩ < 25 * speeds ⟨0, by omega⟩) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  by_contra hno
  push_neg at hno
  have h_no_lonely : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1/6 := hno
  have h62' : 25 * (speeds ⟨3, by omega⟩ : ℤ) < 27 * (speeds ⟨2, by omega⟩ : ℤ) := by
    exact_mod_cast h62
  have h63' : 7 * (speeds ⟨2, by omega⟩ : ℤ) < 25 * (speeds ⟨0, by omega⟩ : ℤ) := by
    exact_mod_cast h63
  -- v₃ ≤ 2 v₂ from the §6 structure v₃ = K·D, v₂ = (K−1)·D, K ≥ 2.
  have h2v2 : (speeds ⟨2, by omega⟩ : ℤ) ≤ 2 * (speeds ⟨1, by omega⟩ : ℤ) := by
    have hKD : speeds ⟨2, by omega⟩ ≤ 2 * speeds ⟨1, by omega⟩ := by
      rw [hv3, hv2]
      calc K * D ≤ (2 * (K - 1)) * D :=
            Nat.mul_le_mul_right D (by omega)
        _ = 2 * ((K - 1) * D) := by ring
    exact_mod_cast hKD
  have h_incl := bhk_s6_651_1234_gap_incl speeds hmono hpos h_no_lonely
  obtain ⟨h64a, h64b⟩ := bhk_s6_651_find_64 speeds hmono hpos h62' h63' h_incl
  have h2b := bhk_s6_651_find_2b speeds hmono hpos hsmall h2v2 h62' h64b h63'
    h_no_lonely
  obtain ⟨hC1, hC2⟩ := bhk_s6_651_find_5b speeds hmono hpos hsmall h62' h63'
    h64a h64b h2b h_no_lonely
  exact bhk_s6_651_final speeds hmono hpos h62' h63' h64a h64b hC1 hC2
    h_no_lonely

/-- **BHK Case 6.5.1, `n = 5`** (BHK p. 43). `(1/5, −2/5) ∈ G`: the
    orbit is `{(0,0), (1,3), (2,1), (3,4), (4,2)}` (fifths). The point
    `(1/5, 3/5)` lies in the true (59)/(60) window when
    `27 v₃ ≤ 25 v₄`; the point `(3/5, 4/5)` when `25 v₁ ≤ 7 v₃`.
    Otherwise the forced bounds (62)/(63) hold and the kernel applies. -/
lemma bhk_s6_case_651 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (D K : ℕ) (hD2 : 2 ≤ D) (hK2 : 2 ≤ K)
    (hv3 : speeds ⟨2, by omega⟩ = K * D)
    (hv2 : speeds ⟨1, by omega⟩ = (K - 1) * D)
    (h43 : 3 * speeds ⟨3, by omega⟩ < 4 * speeds ⟨2, by omega⟩)
    (c₁ c₄ g : ℕ) (hgpos : 0 < g)
    (hd : g * 5 = D) (hc1 : g * c₁ = speeds ⟨0, by omega⟩)
    (hc4 : g * c₄ = speeds ⟨3, by omega⟩)
    (hmem : ((1 : ZMod 5), (-2 : ZMod 5)) ∈
      AddSubgroup.zmultiples ((c₁ : ZMod 5), (c₄ : ZMod 5))) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  have hV1R : (0 : ℝ) < speeds ⟨0, by omega⟩ := by exact_mod_cast hpos _
  have hV3R : (0 : ℝ) < speeds ⟨2, by omega⟩ := by exact_mod_cast hpos _
  have hV4R : (0 : ℝ) < speeds ⟨3, by omega⟩ := by exact_mod_cast hpos _
  have hsmallR : 3 * (speeds ⟨0, by omega⟩ : ℝ) < speeds ⟨2, by omega⟩ := by
    exact_mod_cast hsmall
  have h34R : (speeds ⟨2, by omega⟩ : ℝ) < speeds ⟨3, by omega⟩ := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (by omega))
  rcases le_or_gt (27 * (speeds ⟨2, by omega⟩ : ℝ))
    (25 * speeds ⟨3, by omega⟩) with h62 | h62
  · -- `27 v₃ ≤ 25 v₄`: the point `(1/5, 3/5)`.
    have hpair : (((1 : ℕ) : ZMod 5), ((3 : ℕ) : ZMod 5)) ∈
        AddSubgroup.zmultiples ((c₁ : ZMod 5), (c₄ : ZMod 5)) := by
      have : (((1 : ℕ) : ZMod 5), ((3 : ℕ) : ZMod 5))
          = ((1 : ZMod 5), (-2 : ZMod 5)) := by decide
      rw [this]
      exact hmem
    obtain ⟨k, hk1, hk4⟩ := bhk_s6_mem_k 5 c₁ c₄ (by omega) 1 3 hpair
    have hcast1 : ((1 % 5 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) = 1 / 5 := by norm_num
    have hcast3 : ((3 % 5 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) = 3 / 5 := by norm_num
    apply bhk_s6_witness_real speeds hmono hpos hsmall D K hD2 hK2 hv3 hv2
      h43 5 c₁ c₄ g (by omega) hgpos hd hc1 hc4 k
    · rw [hk1, hcast1]
      have hb : (0 : ℝ)
          ≤ (speeds ⟨0, by omega⟩ : ℝ) / (3 * speeds ⟨2, by omega⟩) := by
        positivity
      linarith
    · rw [hk1, hcast1]
      have hb : 5 * (speeds ⟨0, by omega⟩ : ℝ) / (6 * speeds ⟨2, by omega⟩)
          ≤ 5 / 18 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    · refine Or.inr ?_
      rw [hk4, hcast3]
      have hb : (9 : ℝ) / 10
          ≤ 5 * (speeds ⟨3, by omega⟩ : ℝ) / (6 * speeds ⟨2, by omega⟩) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      linarith
  · rcases le_or_gt (25 * (speeds ⟨0, by omega⟩ : ℝ))
      (7 * speeds ⟨2, by omega⟩) with h63 | h63
    · -- `25 v₁ ≤ 7 v₃`: the point `(3/5, 4/5)`.
      have hpair : (((3 : ℕ) : ZMod 5), ((4 : ℕ) : ZMod 5)) ∈
          AddSubgroup.zmultiples ((c₁ : ZMod 5), (c₄ : ZMod 5)) := by
        have h3 := bhk_s6_pair_mul 5 c₁ c₄ (-2 : ZMod 5) hmem 3
        have : (((3 : ℕ) : ZMod 5), ((4 : ℕ) : ZMod 5))
            = (((3 : ℕ) : ZMod 5), ((3 : ℕ) : ZMod 5) * (-2 : ZMod 5)) := by
          decide
        rw [this]
        exact h3
      obtain ⟨k, hk1, hk4⟩ := bhk_s6_mem_k 5 c₁ c₄ (by omega) 3 4 hpair
      have hcast3 : ((3 % 5 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) = 3 / 5 := by norm_num
      have hcast4 : ((4 % 5 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) = 4 / 5 := by norm_num
      apply bhk_s6_witness_real speeds hmono hpos hsmall D K hD2 hK2 hv3 hv2
        h43 5 c₁ c₄ g (by omega) hgpos hd hc1 hc4 k
      · rw [hk1, hcast3]
        have hb : (0 : ℝ)
            ≤ (speeds ⟨0, by omega⟩ : ℝ) / (3 * speeds ⟨2, by omega⟩) := by
          positivity
        linarith
      · rw [hk1, hcast3]
        have hb : 5 * (speeds ⟨0, by omega⟩ : ℝ) / (6 * speeds ⟨2, by omega⟩)
            ≤ 7 / 30 := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith
        linarith
      · refine Or.inr ?_
        rw [hk4, hcast4]
        have hb : (7 : ℝ) / 10
            ≤ 5 * (speeds ⟨3, by omega⟩ : ℝ) / (6 * speeds ⟨2, by omega⟩) := by
          rw [le_div_iff₀ (by positivity)]
          nlinarith
        linarith
    · -- Forced bounds (62)/(63): the ad hoc kernel.
      exact bhk_s6_case_651_kernel speeds hmono hpos hsmall D K hD2 hK2
        hv3 hv2 h43 c₁ c₄ g hgpos hd hc1 hc4 hmem
        (by exact_mod_cast h62) (by exact_mod_cast h63)

/-- **Wrapped rectangle window.** For `ρ ∈ [0, 1)` and an anchored window
    `[c, c + L]` with `0 ≤ c < 1` that may wrap past `1`:
    `{ρ - c} ≤ L` forces `c ≤ ρ` or `ρ ≤ c + L - 1`. -/
lemma bhk_s6_fract_window_wrap (ρ c L : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (h : Int.fract (ρ - c) ≤ L) :
    c ≤ ρ ∨ ρ ≤ c + L - 1 := by
  rcases le_or_gt c ρ with hge | hlt
  · exact Or.inl hge
  · refine Or.inr ?_
    have hin : Int.fract (ρ - c) = ρ - c + 1 := by
      rw [show ρ - c = (ρ - c + 1) + ((-1 : ℤ) : ℝ) from by push_cast; ring,
          Int.fract_add_intCast,
          Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
      push_cast
      ring
    rw [hin] at h
    linarith

set_option maxHeartbeats 2000000 in
-- The dispatcher below is a single long case analysis (gcd reduction,
-- Corollary 6, seven cone cases); it exceeds the default budget.
/-- **BHK §6 hard core** (OPEN — BHK pp. 41–43). The §6 structure plus
    `3 v₄ < 4 v₃` (BHK's `x₄ > 3/4`, forced by Lemma 4 on the `I_j`
    gap). The remaining pipeline: condition (60) + Lemma 22, else
    Corollary 6 on `G = ⟨({v₁t₀}, {v₄t₀})⟩` with the rectangle
    `R ⊇ [1/6, 5/9] × [2/3, 1]`, then Cases 6.1–6.5 (see module
    docstring). -/
theorem bhk_s6_hard (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (D k : ℕ) (hD2 : 2 ≤ D) (hk2 : 2 ≤ k)
    (hv3 : speeds ⟨2, by omega⟩ = k * D)
    (hv2 : speeds ⟨1, by omega⟩ = (k - 1) * D)
    (hndvd : ¬ D ∣ speeds ⟨0, by omega⟩)
    (h43 : 3 * speeds ⟨3, by omega⟩ < 4 * speeds ⟨2, by omega⟩) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  set V1 : ℕ := speeds ⟨0, by omega⟩ with hV1_def
  set V3 : ℕ := speeds ⟨2, by omega⟩ with hV3_def
  set V4 : ℕ := speeds ⟨3, by omega⟩ with hV4_def
  have hV1pos : 0 < V1 := hpos _
  have hV3pos : 0 < V3 := hpos _
  have hV4pos : 0 < V4 := hpos _
  have hDpos : 0 < D := by omega
  -- Reduce the orbit group: `g := gcd(D, gcd(v₁, v₄))`, `n := D/g`.
  set g : ℕ := Nat.gcd D (Nat.gcd V1 V4) with hg_def
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hDpos
  obtain ⟨n, hn_eq⟩ : g ∣ D := Nat.gcd_dvd_left _ _
  obtain ⟨c₁, hc1_eq⟩ : g ∣ V1 :=
    (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  obtain ⟨c₄, hc4_eq⟩ : g ∣ V4 :=
    (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h
    · rw [h0, mul_zero] at hn_eq; omega
    · exact h
  have hcop : Nat.gcd n (Nat.gcd c₁ c₄) = 1 := by
    have key : Nat.gcd D (Nat.gcd V1 V4) = g * Nat.gcd n (Nat.gcd c₁ c₄) := by
      rw [hn_eq, hc1_eq, hc4_eq, Nat.gcd_mul_left g c₁ c₄,
          Nat.gcd_mul_left g n (Nat.gcd c₁ c₄)]
    rw [← hg_def] at key
    exact (Nat.eq_of_mul_eq_mul_left hgpos
      (by rw [mul_one, ← key] : g * 1 = g * Nat.gcd n (Nat.gcd c₁ c₄))).symm
  have hndvd1 : ¬ n ∣ c₁ := by
    rintro ⟨q, hq⟩
    exact hndvd ⟨q, by rw [hc1_eq, hq, hn_eq]; ring⟩
  have hn1 : 1 < n := by
    rcases (by omega : n = 1 ∨ 1 < n) with rfl | h
    · exact absurd (one_dvd c₁) hndvd1
    · exact h
  -- Case 6.1 first: `n ∣ c₄`.
  by_cases hdvd4 : n ∣ c₄
  · exact bhk_s6_case_61 speeds hmono hpos hsmall D k hD2 hk2 hv3 hv2 h43
      n c₁ c₄ g hn1 hgpos hn_eq.symm hc1_eq.symm hc4_eq.symm hcop hdvd4
  have hc1m0 : c₁ % n ≠ 0 := fun h => hndvd1 (Nat.dvd_of_mod_eq_zero h)
  have hc4m0 : c₄ % n ≠ 0 := fun h => hdvd4 (Nat.dvd_of_mod_eq_zero h)
  rcases (by omega : n = 2 ∨ n = 3 ∨ 4 ≤ n) with rfl | rfl | hn4
  · -- `n = 2`: both `c₁`, `c₄` odd, so `(1, 1) ∈ H` — Case 6.2.
    have e1 : ((c₁ : ℕ) : ZMod 2) = 1 := by
      rw [← ZMod.natCast_mod, (by omega : c₁ % 2 = 1), Nat.cast_one]
    have e4 : ((c₄ : ℕ) : ZMod 2) = 1 := by
      rw [← ZMod.natCast_mod, (by omega : c₄ % 2 = 1), Nat.cast_one]
    have hmem : ((1 : ZMod 2), (1 : ZMod 2)) ∈
        AddSubgroup.zmultiples ((c₁ : ZMod 2), (c₄ : ZMod 2)) := by
      rw [show ((1 : ZMod 2), (1 : ZMod 2)) = ((c₁ : ZMod 2), (c₄ : ZMod 2))
        from by rw [e1, e4]]
      exact AddSubgroup.mem_zmultiples _
    exact bhk_s6_case_62 speeds hmono hpos hsmall D k hD2 hk2 hv3 hv2 h43
      2 c₁ c₄ g (by omega) hgpos hn_eq.symm hc1_eq.symm hc4_eq.symm hmem
  · -- `n = 3`: `(c₁, c₄) mod 3` lies in `{1,2}²` — Case 6.2 or 6.3.
    have hgen : (((c₁ % 3 : ℕ) : ZMod 3), ((c₄ % 3 : ℕ) : ZMod 3)) ∈
        AddSubgroup.zmultiples ((c₁ : ZMod 3), (c₄ : ZMod 3)) := by
      rw [show (((c₁ % 3 : ℕ) : ZMod 3), ((c₄ % 3 : ℕ) : ZMod 3))
          = ((c₁ : ZMod 3), (c₄ : ZMod 3)) from by
        rw [ZMod.natCast_mod, ZMod.natCast_mod]]
      exact AddSubgroup.mem_zmultiples _
    have hgen_neg : (-(((c₁ % 3 : ℕ) : ZMod 3), ((c₄ % 3 : ℕ) : ZMod 3))) ∈
        AddSubgroup.zmultiples ((c₁ : ZMod 3), (c₄ : ZMod 3)) :=
      AddSubgroup.neg_mem _ hgen
    rcases (by omega : c₁ % 3 = 1 ∧ c₄ % 3 = 1 ∨ c₁ % 3 = 2 ∧ c₄ % 3 = 2 ∨
        c₁ % 3 = 1 ∧ c₄ % 3 = 2 ∨ c₁ % 3 = 2 ∧ c₄ % 3 = 1) with
      ⟨h1, h4⟩ | ⟨h1, h4⟩ | ⟨h1, h4⟩ | ⟨h1, h4⟩
    · rw [h1, h4] at hgen
      exact bhk_s6_case_62 speeds hmono hpos hsmall D k hD2 hk2 hv3 hv2 h43
        3 c₁ c₄ g (by omega) hgpos hn_eq.symm hc1_eq.symm hc4_eq.symm
        (by rw [show ((1 : ZMod 3), (1 : ZMod 3))
              = (((1 : ℕ) : ZMod 3), ((1 : ℕ) : ZMod 3)) from by decide]
            exact hgen)
    · rw [h1, h4] at hgen_neg
      exact bhk_s6_case_62 speeds hmono hpos hsmall D k hD2 hk2 hv3 hv2 h43
        3 c₁ c₄ g (by omega) hgpos hn_eq.symm hc1_eq.symm hc4_eq.symm
        (by rw [show ((1 : ZMod 3), (1 : ZMod 3))
              = -(((2 : ℕ) : ZMod 3), ((2 : ℕ) : ZMod 3)) from by decide]
            exact hgen_neg)
    · rw [h1, h4] at hgen
      exact bhk_s6_case_63 speeds hmono hpos hsmall D k hD2 hk2 hv3 hv2 h43
        3 c₁ c₄ g (by omega) hgpos hn_eq.symm hc1_eq.symm hc4_eq.symm
        (by rw [show ((1 : ZMod 3), (-1 : ZMod 3))
              = (((1 : ℕ) : ZMod 3), ((2 : ℕ) : ZMod 3)) from by decide]
            exact hgen)
    · rw [h1, h4] at hgen_neg
      exact bhk_s6_case_63 speeds hmono hpos hsmall D k hD2 hk2 hv3 hv2 h43
        3 c₁ c₄ g (by omega) hgpos hn_eq.symm hc1_eq.symm hc4_eq.symm
        (by rw [show ((1 : ZMod 3), (-1 : ZMod 3))
              = -(((2 : ℕ) : ZMod 3), ((1 : ℕ) : ZMod 3)) from by decide]
            exact hgen_neg)
  -- `n ≥ 4`: apply Corollary 6 with (13)-minimality.
  have hV1R : (0 : ℝ) < V1 := by exact_mod_cast hV1pos
  have hV3R : (0 : ℝ) < V3 := by exact_mod_cast hV3pos
  have hV4R : (0 : ℝ) < V4 := by exact_mod_cast hV4pos
  have hsmallR : 3 * (V1 : ℝ) < V3 := by exact_mod_cast hsmall
  have h43R : 3 * (V4 : ℝ) < 4 * V3 := by exact_mod_cast h43
  have h34R : (V3 : ℝ) < V4 := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (by omega))
  have hG_int : ∀ a b : ℤ,
      ((a : ℝ) / n, (b : ℝ) / n) ∈ bhkS7Group n c₁ c₄ ↔
      ((a : ZMod n), (b : ZMod n)) ∈
        AddSubgroup.zmultiples ((c₁ : ZMod n), (c₄ : ZMod n)) :=
    fun a b => bhk_lift_int_mem_iff _ n hn1 _ (fun _ => Iff.rfl) a b
  set α : ℝ := 2 / 3 - (V1 : ℝ) / (2 * V3) with hα_def
  set β : ℝ := (V4 : ℝ) / (2 * V3) with hβ_def
  have hα_lo : 1 / 2 < α := by
    have h16 : (V1 : ℝ) / (2 * V3) < 1 / 6 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    rw [hα_def]
    linarith
  have hα_hi : α < 1 := by
    have hp : (0 : ℝ) < (V1 : ℝ) / (2 * V3) := by positivity
    rw [hα_def]
    linarith
  have hβ_lo : 1 / 2 < β := by
    rw [hβ_def, lt_div_iff₀ (by positivity)]
    linarith
  have hβ_hi : β < 2 / 3 := by
    rw [hβ_def, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hαβ : α * β ≥ 1 / (n : ℝ) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have h4n : (4 : ℝ) ≤ n := by exact_mod_cast hn4
    have h14 : 1 / (n : ℝ) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) h4n
    nlinarith
  have h_nβ : 1 / β ≤ (n : ℝ) := by
    have h2 : 1 / β < 2 := by
      rw [div_lt_iff₀ (by linarith)]
      linarith
    have h2n : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
    linarith
  rcases bhk_s7_corollary_6_minimal (bhkS7Group n c₁ c₄) n hn1
      (bhk_s7_lift n c₁ c₄ hn1 hcop) α β (by linarith) hα_hi (by linarith)
      (by linarith) hαβ h_nβ with
    hAll | ⟨⟨i, j⟩, hij_ne, hij_G, hi_nonneg, hi_lt, hj_lo, hj_hi, hmin⟩
  · -- All rectangles hit: extract a meeting index for the true windows.
    obtain ⟨p, hpG, hpR⟩ := hAll (1 / 6 - (V1 : ℝ) / (3 * V3))
      (3 / 2 - 5 * (V4 : ℝ) / (6 * V3))
    obtain ⟨kk, hk1, hk4⟩ := bhk_s7_extract n c₁ c₄ hn1 p hpG
    obtain ⟨hpR1a, hpR1b, hpR2a, hpR2b⟩ := hpR
    have hshift : ∀ x c : ℝ,
        Int.fract (x - c) = Int.fract (Int.fract x - c) := by
      intro x c
      conv_lhs => rw [← Int.fract_add_floor x]
      rw [show Int.fract x + (⌊x⌋ : ℝ) - c
            = Int.fract x - c + (⌊x⌋ : ℤ) from by push_cast; ring,
          Int.fract_add_intCast]
    have hx₁0 : 0 ≤ 1 / 6 - (V1 : ℝ) / (3 * V3) := by
      have h19 : (V1 : ℝ) / (3 * V3) < 1 / 9 := by
        rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    have hx₁α : (1 / 6 - (V1 : ℝ) / (3 * V3)) + α < 1 := by
      have hp : (0 : ℝ) < (V1 : ℝ) / (3 * V3) := by positivity
      have hp2 : (0 : ℝ) < (V1 : ℝ) / (2 * V3) := by positivity
      rw [hα_def]
      linarith
    have hwin1 := bhk_fract_window (Int.fract p.1)
      (1 / 6 - (V1 : ℝ) / (3 * V3)) α (Int.fract_nonneg _)
      (Int.fract_lt_one _) hx₁0 hx₁α (by rw [← hshift]; exact hpR1b)
    have hx₂0 : 0 ≤ 3 / 2 - 5 * (V4 : ℝ) / (6 * V3) := by
      have h109 : 5 * (V4 : ℝ) / (6 * V3) < 10 / 9 := by
        rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    have hx₂1 : 3 / 2 - 5 * (V4 : ℝ) / (6 * V3) < 1 := by
      have h56 : (5 : ℝ) / 6 < 5 * (V4 : ℝ) / (6 * V3) := by
        rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
        nlinarith
      linarith
    have hwin4 := bhk_s6_fract_window_wrap (Int.fract p.2)
      (3 / 2 - 5 * (V4 : ℝ) / (6 * V3)) β (Int.fract_nonneg _)
      (Int.fract_lt_one _) hx₂0 hx₂1 (by rw [← hshift]; exact hpR2b)
    have hfr1 : Int.fract p.1 = ((c₁ * kk % n : ℕ) : ℝ) / n := by
      rw [hk1, bhk_fract_nat_div _ _ hnpos]
    have hfr4 : Int.fract p.2 = ((c₄ * kk % n : ℕ) : ℝ) / n := by
      rw [hk4, bhk_fract_nat_div _ _ hnpos]
    apply bhk_s6_witness_real speeds hmono hpos hsmall D k hD2 hk2 hv3 hv2
      h43 n c₁ c₄ g hnpos hgpos hn_eq.symm hc1_eq.symm hc4_eq.symm kk
    · rw [← hfr1]
      exact hwin1.1
    · have hsum : (1 / 6 - (V1 : ℝ) / (3 * V3)) + α
          = 5 / 6 - 5 * (V1 : ℝ) / (6 * V3) := by
        rw [hα_def]
        field_simp
        ring
      rw [← hfr1]
      linarith [hwin1.2]
    · have hsum : (3 / 2 - 5 * (V4 : ℝ) / (6 * V3)) + β - 1
          = 1 / 2 - (V4 : ℝ) / (3 * V3) := by
        rw [hβ_def]
        field_simp
        ring
      rw [← hfr4]
      rcases hwin4 with h | h
      · exact Or.inr h
      · exact Or.inl (by linarith)
  · -- Cone element `(i, j)`: `i ∈ {0, 1}`, `|j| ≤ 3`.
    have hβ_inv : 1 / β < 2 := by
      rw [div_lt_iff₀ (by linarith)]
      linarith
    have hα_inv : 1 / α < 2 := by
      rw [div_lt_iff₀ (by linarith)]
      linarith
    have hβα : β / α < 4 / 3 := by
      rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    have hβα0 : 0 ≤ β / α := by positivity
    have hi2 : i < 2 := by
      have : (i : ℝ) < 2 := lt_trans hi_lt hβ_inv
      exact_mod_cast this
    have hi0 : 0 ≤ i := hi_nonneg
    have hiR1 : (i : ℝ) ≤ 1 := by
      exact_mod_cast (by omega : i ≤ 1)
    have hiR0 : (0 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi0
    have hj4 : j < 4 := by
      have hR : (j : ℝ) < 4 := by
        have h1 : (j : ℝ) < 1 / α + β / α * i := hj_hi
        nlinarith
      exact_mod_cast hR
    have hjm4 : -4 < j := by
      have hR : (-4 : ℝ) < (j : ℝ) := by
        have h1 : -1 / α - β / α * i < (j : ℝ) := hj_lo
        have hprod : β / α * (i : ℝ) ≤ β / α * 1 :=
          mul_le_mul_of_nonneg_left hiR1 hβα0
        have hneg : (-1 : ℝ) / α - β / α * (i : ℝ)
            = -(1 / α + β / α * (i : ℝ)) := by ring
        rw [hneg] at h1
        linarith
      exact_mod_cast hR
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · -- `i = 0`: `j = ±1` and `(0, ±1/n) ∈ G` forces `n ∣ c₁` — absurd.
      exfalso
      have hj_ne : j ≠ 0 := by
        rintro rfl
        exact hij_ne rfl
      have hcast0 : ((0 : ℤ) : ℝ) = 0 := by norm_num
      have hj1 : j = 1 ∨ j = -1 := by
        have hhi : (j : ℝ) < 1 / α := by
          have := hj_hi
          rw [hcast0, mul_zero, add_zero] at this
          exact this
        have hlo : -1 / α < (j : ℝ) := by
          have := hj_lo
          rw [hcast0, mul_zero, sub_zero] at this
          exact this
        have h2 : (j : ℝ) < 2 := lt_trans hhi hα_inv
        have hm2 : (-2 : ℝ) < (j : ℝ) := by
          have : -1 / α = -(1 / α) := by ring
          rw [this] at hlo
          linarith
        have hj2 : j < 2 := by exact_mod_cast h2
        have hjm2 : -2 < j := by exact_mod_cast hm2
        omega
      have hmem' := (hG_int 0 j).mp hij_G
      rw [Int.cast_zero] at hmem'
      obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem'
      have hz1 : (z : ZMod n) * (c₁ : ZMod n) = 0 := by
        have := congr_arg Prod.fst hz
        simpa [zsmul_eq_mul] using this
      have hz4 : (z : ZMod n) * (c₄ : ZMod n) = ((j : ℤ) : ZMod n) := by
        have := congr_arg Prod.snd hz
        simpa [zsmul_eq_mul] using this
      have hkey : ((c₁ : ℕ) : ZMod n) * ((j : ℤ) : ZMod n) = 0 := by
        calc ((c₁ : ℕ) : ZMod n) * ((j : ℤ) : ZMod n)
            = (c₄ : ZMod n) * ((z : ZMod n) * (c₁ : ZMod n)) := by
              rw [← hz4]; ring
          _ = 0 := by rw [hz1, mul_zero]
      have hc10 : ((c₁ : ℕ) : ZMod n) = 0 := by
        rcases hj1 with rfl | rfl
        · simpa using hkey
        · rw [show (((-1 : ℤ)) : ZMod n) = -1 from by push_cast; ring,
              mul_neg, mul_one, neg_eq_zero] at hkey
          exact hkey
      exact hndvd1 ((ZMod.natCast_eq_zero_iff c₁ n).mp hc10)
    · -- `i = 1`: dispatch on `j ∈ {−3, …, 3}`.
      have hmemH : (((1 : ℤ) : ZMod n), ((j : ℤ) : ZMod n)) ∈
          AddSubgroup.zmultiples ((c₁ : ZMod n), (c₄ : ZMod n)) :=
        (hG_int 1 j).mp hij_G
      rw [Int.cast_one] at hmemH
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = -1 ∨ j = 2 ∨ j = -2 ∨
          j = 3 ∨ j = -3) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · -- `j = 0` would give `n ∣ c₄` — already excluded.
        exfalso
        obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hmemH
        have hz1 : (z : ZMod n) * (c₁ : ZMod n) = 1 := by
          have := congr_arg Prod.fst hz
          simpa [zsmul_eq_mul] using this
        have hz4 : (z : ZMod n) * (c₄ : ZMod n) = 0 := by
          have := congr_arg Prod.snd hz
          simpa [zsmul_eq_mul] using this
        have hkey : ((c₄ : ℕ) : ZMod n) = 0 := by
          calc ((c₄ : ℕ) : ZMod n)
              = (c₄ : ZMod n) * ((z : ZMod n) * (c₁ : ZMod n)) := by
                rw [hz1, mul_one]
            _ = (c₁ : ZMod n) * ((z : ZMod n) * (c₄ : ZMod n)) := by ring
            _ = 0 := by rw [hz4, mul_zero]
        exact hdvd4 ((ZMod.natCast_eq_zero_iff c₄ n).mp hkey)
      · -- `j = 1`: Case 6.2.
        rw [Int.cast_one] at hmemH
        exact bhk_s6_case_62 speeds hmono hpos hsmall D k hD2 hk2 hv3 hv2
          h43 n c₁ c₄ g (by omega) hgpos hn_eq.symm hc1_eq.symm hc4_eq.symm
          hmemH
      · -- `j = −1`: Case 6.3.
        rw [show (((-1 : ℤ)) : ZMod n) = -1 from by push_cast; ring] at hmemH
        exact bhk_s6_case_63 speeds hmono hpos hsmall D k hD2 hk2 hv3 hv2
          h43 n c₁ c₄ g (by omega) hgpos hn_eq.symm hc1_eq.symm hc4_eq.symm
          hmemH
      · -- `j = 2`: Case 6.4.
        rw [show (((2 : ℤ)) : ZMod n) = 2 from by push_cast; ring] at hmemH
        exact bhk_s6_case_64 speeds hmono hpos hsmall D k hD2 hk2 hv3 hv2
          h43 n c₁ c₄ g hn4 hgpos hn_eq.symm hc1_eq.symm hc4_eq.symm hmemH
      · -- `j = −2`: Cases 6.5 / 6.5.1 / 6.5.2.
        rw [show (((-2 : ℤ)) : ZMod n) = -2 from by push_cast; ring] at hmemH
        rcases (by omega : n = 5 ∨ n = 7 ∨ (n % 2 = 0 ∨ 9 ≤ n)) with
          rfl | rfl | hn'
        · exact bhk_s6_case_651 speeds hmono hpos hsmall D k hD2 hk2 hv3
            hv2 h43 c₁ c₄ g hgpos hn_eq.symm hc1_eq.symm hc4_eq.symm hmemH
        · exact bhk_s6_case_652 speeds hmono hpos hsmall D k hD2 hk2 hv3
            hv2 h43 c₁ c₄ g hgpos hn_eq.symm hc1_eq.symm hc4_eq.symm hmemH
        · exact bhk_s6_case_65 speeds hmono hpos hsmall D k hD2 hk2 hv3 hv2
            h43 n c₁ c₄ g hn4 hn' hgpos hn_eq.symm hc1_eq.symm hc4_eq.symm
            hmemH
      · -- `j = 3`: (13)-minimality forces `n ≥ 6`, then the `(1, 3)` case.
        have hn6 : 6 ≤ n := by
          by_contra h'
          have hn5 : n = 4 ∨ n = 5 := by omega
          have habs : |(3 - (n : ℤ))| ≤ |(3 : ℤ)| := by
            rcases hn5 with rfl | rfl <;> decide
          have hcorner : ¬(|((1 : ℤ))| = |(1 : ℤ)| ∧
              |(3 - (n : ℤ))| = |(3 : ℤ)|) := by
            rintro ⟨-, h2⟩
            rcases hn5 with rfl | rfl <;> exact absurd h2 (by decide)
          have hG_mem : (((1 : ℤ) : ℝ) / n, ((3 - (n : ℤ) : ℤ) : ℝ) / n) ∈
              bhkS7Group n c₁ c₄ := by
            rw [hG_int]
            rw [show ((3 - (n : ℤ) : ℤ) : ZMod n) = ((3 : ℤ) : ZMod n) from by
              rw [Int.cast_sub, Int.cast_natCast, ZMod.natCast_self,
                  sub_zero]]
            push_cast
            push_cast at hmemH
            exact hmemH
          exact hmin (1, 3 - (n : ℤ)) (by simp) (le_refl _) habs hcorner
            hG_mem
        rw [show (((3 : ℤ)) : ZMod n) = ((3 : ℤ) : ZMod n) from rfl] at hmemH
        exact bhk_s6_case_66 speeds hmono hpos hsmall D k hD2 hk2 hv3 hv2
          h43 n c₁ c₄ g hn6 hgpos hn_eq.symm hc1_eq.symm hc4_eq.symm
          3 (Or.inl rfl) hmemH
      · -- `j = −3`: symmetric minimality bound, then the `(1, −3)` case.
        have hn6 : 6 ≤ n := by
          by_contra h'
          have hn5 : n = 4 ∨ n = 5 := by omega
          have habs : |((n : ℤ) - 3)| ≤ |(-3 : ℤ)| := by
            rcases hn5 with rfl | rfl <;> decide
          have hcorner : ¬(|((1 : ℤ))| = |(1 : ℤ)| ∧
              |((n : ℤ) - 3)| = |(-3 : ℤ)|) := by
            rintro ⟨-, h2⟩
            rcases hn5 with rfl | rfl <;> exact absurd h2 (by decide)
          have hG_mem : (((1 : ℤ) : ℝ) / n, (((n : ℤ) - 3 : ℤ) : ℝ) / n) ∈
              bhkS7Group n c₁ c₄ := by
            rw [hG_int]
            rw [show (((n : ℤ) - 3 : ℤ) : ZMod n) = ((-3 : ℤ) : ZMod n)
              from by
              rw [Int.cast_sub, Int.cast_natCast, ZMod.natCast_self,
                  zero_sub, Int.cast_neg]]
            push_cast
            push_cast at hmemH
            exact hmemH
          exact hmin (1, (n : ℤ) - 3) (by simp) (le_refl _) habs hcorner
            hG_mem
        exact bhk_s6_case_66 speeds hmono hpos hsmall D k hD2 hk2 hv3 hv2
          h43 n c₁ c₄ g hn6 hgpos hn_eq.symm hc1_eq.symm hc4_eq.symm
          (-3) (Or.inr rfl) hmemH

/-- **BHK §6 analytic core (PROVED dispatcher).** Integer speeds with
    the §6 arithmetic structure exposed: `D := v₃ - v₂ ≥ 2` divides both
    `v₂` and `v₃` (`v₃ = k·D`, `v₂ = (k−1)·D`, `k ≥ 2`) but not `v₁`,
    and `3 v₁ < v₃`. The `I_j` gap of length `1/(2v₃)` either directly
    contains a lonely time, or (via Lemma 4: a 45-covered interval is
    shorter than `2/(3v₄)`) forces `3 v₄ < 4 v₃` and hands off to
    `bhk_s6_hard`. -/
theorem bhk_s6_reduced (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (D k : ℕ) (hD2 : 2 ≤ D) (hk2 : 2 ≤ k)
    (hv3 : speeds ⟨2, by omega⟩ = k * D)
    (hv2 : speeds ⟨1, by omega⟩ = (k - 1) * D)
    (hndvd : ¬ D ∣ speeds ⟨0, by omega⟩) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  obtain ⟨a, b, hab, hlen, h123gap⟩ :=
    bhk_s6_123_gap speeds hmono hpos hsmall D k hD2 hk2 hv3 hv2 hndvd
  rcases Classical.em (∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t)
      ≥ (1 : ℝ) / 6) with h | hno
  · exact h
  -- No lonely time: the gap is covered by runners 4 and 5; Lemma 4
  -- bounds its length, forcing `3 v₄ < 4 v₃`.
  have hcover : Set.Icc a b ⊆ unsafeOf speeds ⟨3, by omega⟩ ∪
                              unsafeOf speeds ⟨4, by omega⟩ := by
    intro t ht
    push_neg at hno
    obtain ⟨i, hi⟩ := hno t
    have h123 := h123gap ht
    have ht_unsafe : t ∈ unsafeOf speeds i :=
      (mem_unsafeOf_iff speeds i t).mpr hi
    fin_cases i
    · exact absurd (Or.inl (Or.inl ht_unsafe)) h123
    · exact absurd (Or.inl (Or.inr ht_unsafe)) h123
    · exact absurd (Or.inr ht_unsafe) h123
    · exact Or.inl ht_unsafe
    · exact Or.inr ht_unsafe
  have hbnd : b - a < 2 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) :=
    bhk_lemma_4 speeds hmono hpos a b hab hcover
  have hv3R : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hpos (⟨2, by omega⟩ : Fin 5)
  have hv4R : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by
    exact_mod_cast hpos (⟨3, by omega⟩ : Fin 5)
  have h43 : 3 * speeds ⟨3, by omega⟩ < 4 * speeds ⟨2, by omega⟩ := by
    have hR : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ) := by
      rw [hlen] at hbnd
      rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hbnd
      nlinarith
    exact_mod_cast hR
  exact bhk_s6_hard speeds hmono hpos hgcd hsmall D k hD2 hk2 hv3 hv2
    hndvd h43

/-- **BHK §6 reduction (PROVED).** The fract hypotheses of the §6 case
    branch yield the arithmetic structure required by `bhk_s6_reduced`:
    `{v₃ t₀} = 0` gives `D ∣ v₃` hence `D ∣ v₂` (as `D = v₃ − v₂`), so
    `v₃ = k·D`, `v₂ = (k−1)·D` with `k ≥ 2` (`k = 1` would force
    `v₂ = 0`); `{v₁ t₀} ≠ 0` gives `D ∤ v₁`, which forces `D ≥ 2`. -/
theorem bhk_s6_main (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (ht0 : Int.fract ((speeds ⟨2, by omega⟩ : ℝ) *
              (1 / ((speeds ⟨2, by omega⟩ : ℝ) - speeds ⟨1, by omega⟩))) = 0)
    (hv1t0 : Int.fract ((speeds ⟨0, by omega⟩ : ℝ) *
              (1 / ((speeds ⟨2, by omega⟩ : ℝ) - speeds ⟨1, by omega⟩))) ≠ 0) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  set V1 : ℕ := speeds ⟨0, by omega⟩ with hV1_def
  set V2 : ℕ := speeds ⟨1, by omega⟩ with hV2_def
  set V3 : ℕ := speeds ⟨2, by omega⟩ with hV3_def
  have hV12 : V1 < V2 := hmono (Fin.mk_lt_mk.mpr (by omega))
  have hV23 : V2 < V3 := hmono (Fin.mk_lt_mk.mpr (by omega))
  have hV1pos : 0 < V1 := hpos _
  have hV2pos : 0 < V2 := hpos _
  set D : ℕ := V3 - V2 with hD_def
  have hDpos : 0 < D := by omega
  have hD_cast : ((D : ℕ) : ℝ) = (V3 : ℝ) - V2 := by
    rw [hD_def, Nat.cast_sub hV23.le]
  -- `D ∣ V3` from `{v₃ t₀} = 0`.
  have hdvd3 : D ∣ V3 := by
    have h0 : Int.fract ((V3 : ℝ) / D) = 0 := by
      rw [show (V3 : ℝ) / D = (V3 : ℝ) * (1 / ((V3 : ℝ) - V2)) from by
        rw [← hD_cast]; ring]
      exact ht0
    exact (bhk_fract_nat_div_eq_zero_iff V3 D hDpos).mp h0
  -- `D ∤ V1` from `{v₁ t₀} ≠ 0`.
  have hndvd1 : ¬ D ∣ V1 := by
    intro hdvd
    apply hv1t0
    rw [show (V1 : ℝ) * (1 / ((V3 : ℝ) - V2)) = (V1 : ℝ) / D from by
      rw [← hD_cast]; ring]
    exact (bhk_fract_nat_div_eq_zero_iff V1 D hDpos).mpr hdvd
  -- `D ≥ 2`: `D = 1` would divide everything.
  have hD2 : 2 ≤ D := by
    rcases (by omega : D = 1 ∨ 2 ≤ D) with h1 | h2
    · exact absurd (h1 ▸ one_dvd V1) hndvd1
    · exact h2
  -- `V3 = k·D` and `V2 = (k−1)·D` with `k ≥ 2`.
  obtain ⟨k, hkD⟩ := hdvd3
  have hk2 : 2 ≤ k := by
    rcases (by omega : k = 0 ∨ k = 1 ∨ 2 ≤ k) with rfl | rfl | h
    · omega
    · -- `k = 1` gives `V3 = D = V3 − V2`, i.e. `V2 = 0`.
      omega
    · exact h
  have hv2_eq : V2 = (k - 1) * D := by
    have h1 : (k - 1) * D = D * k - D := by
      cases k with
      | zero => simp
      | succ k' => rw [Nat.add_sub_cancel, Nat.mul_succ, Nat.add_sub_cancel,
          Nat.mul_comm]
    rw [h1, ← hkD]
    omega
  exact bhk_s6_reduced speeds hmono hpos hgcd hsmall D k hD2 hk2
    (by rw [← hV3_def, hkD, mul_comm]) (by rw [← hV2_def, hv2_eq]) hndvd1

end BHK
