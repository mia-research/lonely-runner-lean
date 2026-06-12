import LonelyRunner.LRC.SmallN.IntLRC_6_BHK_Section7

/-!
# BHK §5 — the case `{v₁ t₀} = 0` (skeleton + dispatcher)

Here runner 1 sits at the origin whenever runner 3 passes runner 2:
`D ∣ v₁` for `D := v₃ - v₂`, so `v₁ = k·D` for some `k ≥ 1` (BHK (20)).
BHK split on `k`:

* **Case 5.1** (`k ≥ 3`): no 123-gap of length `2/3` exists, but there are
  two or more nearby 123-gaps of length `≥ 1/2` ("triple configurations");
  sub-cases 5.1.1 (`k ≥ 3`, `x₁ < 14/3`) and 5.1.2 (`k = 3`,
  `8 < x₁ < 26/3`). OPEN (`bhk_s5_k_ge_3`).
* **Case 5.2** (`k ∈ {1, 2}`): **Proposition 11** — for speeds
  `v₁ < ⋯ < v₅` with `v₁ + v₂ = v₃` and `v₁ < v₃/3` there is a time with
  all runners `≥ 1/6` from the origin (part 1), and when `v₁ < v₃/6` the
  first runner can moreover avoid the half-point window
  (`{v₁t} ∉ (5/12, 7/12)`, part 2). The proof of Proposition 11 is the
  long core of BHK (pp. 17–40, Parts 1–6: initial reductions, denominator
  analysis, main-lemma application, exceptional-pair table).
  OPEN (`bhk_prop11_part1/2`).

The **dispatcher** (`bhk_s5_main`, PROVED) reduces `{v₁t₀} = 0` to these:
`k = 1` gives `v₁ + v₂ = v₃` directly; `k = 2` applies part 2 to the
halved collection `(D, v₂, …, v₅)` (where `6D = 3v₁ < v₃`) and doubles
the window — `2·([1/6, 5/6] ∖ (5/12, 7/12)) ⊆ [1/6, 5/6] (mod 1)`.

## Source

T. Bohman, R. Holzman, D. Kleitman, *Six Lonely Runners*, EJC **8**
(2001) R3, §5.
-/

open MeasureTheory Set

namespace BHK

/-- **BHK Proposition 11, part 1** (OPEN — BHK pp. 17–40). Integer speeds
    `w₀ < ⋯ < w₄` with `w₀ + w₁ = w₂` and `3 w₀ < w₂` admit a time at which
    every runner is `≥ 1/6` from the origin. (BHK state this for rational
    speeds normalised to `v₃ = 1`; clearing denominators gives the integer
    form, which is what the §5 dispatcher needs.) -/
theorem bhk_prop11_part1 (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩) :
    ∃ t : ℝ, ∀ i, circDist ((w i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  sorry

/-- **BHK Proposition 11, part 2** (OPEN — BHK pp. 17–40). Under the
    stronger hypothesis `6 w₀ < w₂` (`v₁ < 1/6`), the time can be chosen
    with the additional window `{w₀ t} ∉ (5/12, 7/12)`. -/
theorem bhk_prop11_part2 (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩) :
    ∃ t : ℝ, (∀ i, circDist ((w i : ℝ) * t) ≥ (1 : ℝ) / 6) ∧
      Int.fract ((w ⟨0, by omega⟩ : ℝ) * t) ∉ Set.Ioo (5/12 : ℝ) (7/12) := by
  sorry

/-- **BHK §5, Case 5.1** (OPEN). `v₁ = k·D` with `k ≥ 3`, `D = v₃ - v₂`:
    the "triple configuration" analysis — two or more nearby 123-gaps of
    length `≥ 1/2`, BHK (27)/(28), sub-cases 5.1.1 and 5.1.2. -/
theorem bhk_s5_k_ge_3 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (k D : ℕ) (hk3 : 3 ≤ k)
    (hD : D = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hkD : speeds ⟨0, by omega⟩ = D * k) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  sorry

/-- **Window extraction.** `circDist x ≥ 1/6` gives the fract window. -/
lemma bhk_fract_of_circDist {x : ℝ} (h : (1 : ℝ)/6 ≤ circDist x) :
    1/6 ≤ Int.fract x ∧ Int.fract x ≤ 5/6 := by
  unfold circDist at h
  refine ⟨le_trans h (min_le_left _ _), ?_⟩
  have := le_trans h (min_le_right _ _)
  linarith

/-- **The doubling window.** If `{y} ∈ [1/6, 5/6] ∖ (5/12, 7/12)` then
    `{2y} ∈ [1/3, 5/6] ∪ [1/6, 2/3]`, so `circDist (2y) ≥ 1/6`. This is the
    point of part 2 of Proposition 11: it makes the window survive the
    substitution `v₁ ↦ v₁/2`. -/
lemma bhk_s5_double_window (y : ℝ) (h1 : 1/6 ≤ Int.fract y)
    (h2 : Int.fract y ≤ 5/6)
    (h3 : Int.fract y ∉ Set.Ioo (5/12 : ℝ) (7/12)) :
    (1 : ℝ)/6 ≤ circDist (2 * y) := by
  have hsplit : Int.fract (2 * y) = Int.fract (2 * Int.fract y) := by
    conv_lhs => rw [← Int.fract_add_floor y]
    rw [show 2 * (Int.fract y + (⌊y⌋ : ℝ))
          = 2 * Int.fract y + ((2 * ⌊y⌋ : ℤ) : ℝ) from by push_cast; ring,
        Int.fract_add_intCast]
  simp only [Set.mem_Ioo, not_and_or, not_lt] at h3
  unfold circDist
  rw [hsplit]
  rcases h3 with h3 | h3
  · -- `{y} ≤ 5/12`: `{2{y}} = 2{y} ∈ [1/3, 5/6]`.
    have hf : Int.fract (2 * Int.fract y) = 2 * Int.fract y :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [hf]
    exact le_min (by linarith) (by linarith)
  · -- `{y} ≥ 7/12`: `{2{y}} = 2{y} - 1 ∈ [1/6, 2/3]`.
    have hf : Int.fract (2 * Int.fract y) = 2 * Int.fract y - 1 := by
      conv_lhs => rw [show 2 * Int.fract y
            = (2 * Int.fract y - 1) + ((1 : ℤ) : ℝ) from by push_cast; ring]
      rw [Int.fract_add_intCast]
      exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [hf]
    exact le_min (by linarith) (by linarith)

/-- **BHK §5 dispatcher (PROVED).** `{v₁ t₀} = 0` means `D ∣ v₁`
    (`D := v₃ - v₂`); write `v₁ = k·D` and dispatch on `k`:

    * `k = 1`: `v₁ + v₂ = v₃` — Proposition 11 part 1 applies directly;
    * `k = 2`: Proposition 11 part 2 applied to `(D, v₂, v₃, v₄, v₅)`
      (note `6D = 3v₁ < v₃`), then the doubling window recovers runner 1;
    * `k ≥ 3`: Case 5.1. -/
theorem bhk_s5_main (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (ht0 : Int.fract ((speeds ⟨0, by omega⟩ : ℝ) *
              (1 / ((speeds ⟨2, by omega⟩ : ℝ) - speeds ⟨1, by omega⟩))) = 0) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  set V1 : ℕ := speeds ⟨0, by omega⟩ with hV1_def
  set V2 : ℕ := speeds ⟨1, by omega⟩ with hV2_def
  set V3 : ℕ := speeds ⟨2, by omega⟩ with hV3_def
  have hV12 : V1 < V2 := hmono (Fin.mk_lt_mk.mpr (by omega))
  have hV23 : V2 < V3 := hmono (Fin.mk_lt_mk.mpr (by omega))
  have hV1pos : 0 < V1 := hpos _
  set D : ℕ := V3 - V2 with hD_def
  have hDpos : 0 < D := by omega
  have hD_cast : ((D : ℕ) : ℝ) = (V3 : ℝ) - V2 := by
    rw [hD_def, Nat.cast_sub hV23.le]
  -- `D ∣ V1` from the fract-zero hypothesis.
  have hdvd : D ∣ V1 := by
    have h0 : Int.fract ((V1 : ℝ) / D) = 0 := by
      rw [show (V1 : ℝ) / D = (V1 : ℝ) * (1 / ((V3 : ℝ) - V2)) from by
        rw [← hD_cast]; ring]
      exact ht0
    exact (bhk_fract_nat_div_eq_zero_iff V1 D hDpos).mp h0
  obtain ⟨k, hkD⟩ := hdvd
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h
    · rw [h0, mul_zero] at hkD; omega
    · exact h
  rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | hk3
  · -- `k = 1`: `v₁ + v₂ = v₃`.
    have hsum : V1 + V2 = V3 := by omega
    exact bhk_prop11_part1 speeds hmono hpos hsum hsmall
  · -- `k = 2`: halve the first speed.
    set w : Fin 5 → ℕ := fun i => if i.val = 0 then D else speeds i with hw_def
    have hw0 : w ⟨0, by omega⟩ = D := rfl
    have hw_ne : ∀ i : Fin 5, i.val ≠ 0 → w i = speeds i := by
      intro i hi
      show (if i.val = 0 then D else speeds i) = speeds i
      exact if_neg hi
    have hDV2 : D < V2 := by omega
    have hwmono : StrictMono w := by
      intro i j hij
      have hij' : i.val < j.val := Fin.lt_def.mp hij
      by_cases hi : i.val = 0
      · have hj : j.val ≠ 0 := by omega
        have hwi : w i = D := by
          show (if i.val = 0 then D else speeds i) = D
          exact if_pos hi
        have h1j : (⟨1, by omega⟩ : Fin 5) ≤ j :=
          Fin.le_def.mpr (show 1 ≤ j.val by omega)
        rw [hwi, hw_ne j hj]
        exact lt_of_lt_of_le hDV2 (hmono.monotone h1j)
      · have hj : j.val ≠ 0 := by omega
        rw [hw_ne i hi, hw_ne j hj]
        exact hmono hij
    have hwpos : ∀ i, 0 < w i := by
      intro i
      by_cases hi : i.val = 0
      · have hwi : w i = D := by
          show (if i.val = 0 then D else speeds i) = D
          exact if_pos hi
        rw [hwi]
        exact hDpos
      · rw [hw_ne i hi]
        exact hpos i
    have hwsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩ := by
      have h1 : w ⟨1, by omega⟩ = V2 := hw_ne ⟨1, by omega⟩ (by norm_num)
      have h2 : w ⟨2, by omega⟩ = V3 := hw_ne ⟨2, by omega⟩ (by norm_num)
      rw [hw0, h1, h2]
      omega
    have hwsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩ := by
      have h2 : w ⟨2, by omega⟩ = V3 := hw_ne ⟨2, by omega⟩ (by norm_num)
      rw [hw0, h2]
      omega
    obtain ⟨t, hwin, hfr⟩ := bhk_prop11_part2 w hwmono hwpos hwsum hwsmall6
    refine ⟨t, fun i => ?_⟩
    by_cases hi : i.val = 0
    · -- runner 1: `v₁ = 2D`, use the doubling window.
      have hi_eq : i = ⟨0, by omega⟩ := Fin.ext hi
      obtain ⟨hf1, hf2⟩ := bhk_fract_of_circDist (hwin ⟨0, by omega⟩)
      rw [hw0] at hf1 hf2
      have hfr' : Int.fract ((D : ℝ) * t) ∉ Set.Ioo (5/12 : ℝ) (7/12) := by
        rw [← hw0]
        exact hfr
      have hdouble := bhk_s5_double_window ((D : ℝ) * t) hf1 hf2 hfr'
      have hcast : ((speeds i : ℕ) : ℝ) * t = 2 * ((D : ℝ) * t) := by
        rw [hi_eq, ← hV1_def, hkD]
        push_cast
        ring
      rw [hcast]
      exact hdouble
    · rw [show ((speeds i : ℕ) : ℝ) = ((w i : ℕ) : ℝ) from by rw [hw_ne i hi]]
      exact hwin i
  · -- `k ≥ 3`: Case 5.1.
    exact bhk_s5_k_ge_3 speeds hmono hpos hgcd hsmall k D hk3 hD_def hkD

end BHK
