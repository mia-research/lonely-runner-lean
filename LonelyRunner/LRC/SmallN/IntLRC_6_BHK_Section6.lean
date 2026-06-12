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

/-- **BHK §6 analytic core** (OPEN — BHK pp. 40–43). Integer speeds with
    the §6 arithmetic structure exposed: `D := v₃ - v₂ ≥ 2` divides both
    `v₂` and `v₃` (`v₃ = k·D`, `v₂ = (k−1)·D`, `k ≥ 2`) but not `v₁`,
    and `3 v₁ < v₃`. Concludes a lonely time exists. The proof is the
    Lemma 22 / Corollary 6 / Cases 6.1–6.5 pipeline described in the
    module docstring. -/
theorem bhk_s6_reduced (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (D k : ℕ) (hD2 : 2 ≤ D) (hk2 : 2 ≤ k)
    (hv3 : speeds ⟨2, by omega⟩ = k * D)
    (hv2 : speeds ⟨1, by omega⟩ = (k - 1) * D)
    (hndvd : ¬ D ∣ speeds ⟨0, by omega⟩) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  sorry

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
