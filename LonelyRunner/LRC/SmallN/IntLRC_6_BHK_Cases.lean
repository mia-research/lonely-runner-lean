import LonelyRunner.LRC.SmallN.IntLRC_6_BHK_Lemma4
import LonelyRunner.LRC.SmallN.IntLRC_6_BHK_MainLemma

/-!
# BHK §§5–8 — Case branches of the Six Lonely Runners proof

Four case branches dispatched by the main theorem (`bhk_theorem_2`):

* §5: `{v_1 t_0} = 0`              ⟶ `bhk_case_v1t0_zero`
* §6: `{t_0} = 0`                  ⟶ `bhk_case_t0_zero`
* §7: `3 ≤ x_1 < 4` (both ≠ 0)     ⟶ `bhk_case_v1_small_generic`
* §8: `x_1 ≤ 3` (i.e. `v_3 ≤ 3 v_1`) ⟶ `bhk_case_v1_large`

where `t_0 := 1 / (v_3 - v_2)` is the elementary period (runner 3 passing
runner 2) and `x_i := 1 / v_i`.

The main theorem dispatches: `v_3 ≤ 3 v_1` → §8; else split on `{t_0}`,
`{v_1 t_0}` zero/nonzero.

## Source

T. Bohman, R. Holzman, D. Kleitman, *Six Lonely Runners*, EJC **8** (2001)
R3, §§5–8.
-/

open MeasureTheory Set

namespace BHK

/-- **BHK §5.** Case `{v_1 t_0} = 0` under "small `v_1`" (`3 v_1 < v_3`).
    The deepest case branch; uses Proposition 11 (BHK §5, p17–40) which
    itself has 6 parts and 12 sub-cases. -/
theorem bhk_case_v1t0_zero (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (ht0 : Int.fract ((speeds ⟨0, by omega⟩ : ℝ) *
              (1 / ((speeds ⟨2, by omega⟩ : ℝ) - speeds ⟨1, by omega⟩))) = 0) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  sorry

/-- **BHK §6.** Case `{t_0} = 0` under "small `v_1`" (`3 v_1 < v_3`).
    Applies the Main Lemma to a specific rectangle constructed from the
    23-gap geometry. -/
theorem bhk_case_t0_zero (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (ht0 : Int.fract ((1 : ℝ) / ((speeds ⟨2, by omega⟩ : ℝ) - speeds ⟨1, by omega⟩)) = 0) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  sorry

/-- **BHK §7.** Case `3 ≤ x_1 < 4` (i.e. `v_3 / 4 ≤ v_1` and `3 v_1 < v_3`)
    with both `{t_0} ≠ 0` and `{v_1 t_0} ≠ 0`. Direct Main Lemma application
    to the standard `2/3 × 2/9` rectangle inside `P`, plus 12 exceptional
    pair cases (BHK Table 10). -/
theorem bhk_case_v1_small_generic (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (ht0 : Int.fract ((1 : ℝ) / ((speeds ⟨2, by omega⟩ : ℝ) - speeds ⟨1, by omega⟩)) ≠ 0)
    (hv1t0 : Int.fract ((speeds ⟨0, by omega⟩ : ℝ) *
              (1 / ((speeds ⟨2, by omega⟩ : ℝ) - speeds ⟨1, by omega⟩))) ≠ 0) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  sorry

/-- **Arithmetic kernel for BHK §8.1 step 1 (1234-gap forces `j = 1`).**
    Given an integer `j ≥ 2` satisfying the 1234-gap conditions
    `(6j-1) v_1 < v_5` and `5 v_5 < (6j+1) v_4` (existence of such a `j`
    is the structural part), together with `h81 : 5 v_4 < 7 v_3`
    (§8.1 entry condition `x_4 > 5/7`) and `hlarge : v_3 ≤ 3 v_1` (§8 entry
    `x_1 ≤ 3`), derive a contradiction.

    This rules out `j ≥ 2`. A structural lemma showing `j > 0` then forces
    `j = 1`, yielding BHK's (65): `5 v_1 < v_5` and `5 v_5 < 7 v_4`.

    Arithmetic chain (identical structure to `bhk_case_8_2_1_kernel`):

    * `(6j-1) v_1 < v_5` × 5 + chain with `5 v_5 < (6j+1) v_4`:
      `5(6j-1) v_1 < (6j+1) v_4`.
    * `h81` × `(6j+1)`: `5 (6j+1) v_4 < 7 (6j+1) v_3`.
    * Combine: `25 (6j-1) v_1 < 7 (6j+1) v_3`.
    * `hlarge` × `7 (6j+1)`: `7 (6j+1) v_3 ≤ 21 (6j+1) v_1`.
    * Chain → `25 (6j-1) < 21 (6j+1)`, i.e. `24 j < 46`. Contradicts `j ≥ 2`. -/
lemma bhk_8_1_step1_kernel (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (hlarge : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ))
    (h81 : 5 * (speeds ⟨3, by omega⟩ : ℤ) < 7 * (speeds ⟨2, by omega⟩ : ℤ))
    (j : ℤ) (hj : 2 ≤ j)
    (hjL : (6 * j - 1) * (speeds ⟨0, by omega⟩ : ℤ) <
              (speeds ⟨4, by omega⟩ : ℤ))
    (hjR : 5 * (speeds ⟨4, by omega⟩ : ℤ) <
              (6 * j + 1) * (speeds ⟨3, by omega⟩ : ℤ)) :
    False := by
  have hv1 : (0 : ℤ) < (speeds ⟨0, by omega⟩ : ℤ) := by exact_mod_cast hpos ⟨0, by omega⟩
  have h6jp1_pos : 0 < 6 * j + 1 := by linarith
  have step81 : (6 * j + 1) * (5 * (speeds ⟨3, by omega⟩ : ℤ)) <
                (6 * j + 1) * (7 * (speeds ⟨2, by omega⟩ : ℤ)) :=
    mul_lt_mul_of_pos_left h81 h6jp1_pos
  have step_large : 7 * (speeds ⟨2, by omega⟩ : ℤ) ≤
                    7 * (3 * (speeds ⟨0, by omega⟩ : ℤ)) := by linarith
  nlinarith [step81, step_large, hjL, hjR, hv1, hj, h6jp1_pos,
             mul_le_mul_of_nonneg_left step_large (le_of_lt h6jp1_pos)]

/-- **Common 1234-gap inclusion for §8.1 (used in §8.1.1 and §8.1.2).** Under
    the failure of loneliness (`h_no_lonely`), the 1234-gap
    `[1/(6 v_1), 5/(6 v_4)]` is covered by runner 5 alone. The interval lies
    inside the k=0 safe gap of each of runners 1..4 (using only monotonicity
    `v_1 ≤ v_i ≤ v_4`), so any unsafe runner at any `t` in the interval must
    be runner 5. -/
lemma bhk_8_1_1234_gap_incl (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
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

/-- **§8.1 step 1 derivation of BHK (65) from 1234-gap inclusion.** From the
    BHK §8.1 inclusion `[1/(6 v_1), 5/(6 v_4)] ⊆ unsafeOf speeds ⟨4⟩` (the
    1234-gap covered by 5-blocks alone), derive BHK's (65):

    * `5 v_1 < v_5`         (i.e. `5 x_5 < x_1`)
    * `5 v_5 < 7 v_4`        (i.e. `5 x_4 < 7 x_5`)

    Strategy:
    1. `block_containment` gives an integer `k` with `(6k-1) v_1 < v_5` and
       `5 v_5 < (6k+1) v_4`.
    2. Positivity arguments (using `hmono : v_4 < v_5`) force `k ≥ 1`.
    3. `bhk_8_1_step1_kernel` rules out `k ≥ 2`.
    4. So `k = 1` exactly, and substitution gives (65).

    Combined with the §8.1.1 kernel (and similar find-lemmas for (70b),
    (71b)) this gives a path to fully decompose §8.1.1. -/
lemma bhk_8_1_step1_find_65 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hlarge : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ))
    (h81 : 5 * (speeds ⟨3, by omega⟩ : ℤ) < 7 * (speeds ⟨2, by omega⟩ : ℤ))
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
  -- a ≤ b ⟺ v_4 ≤ 5 v_1, which follows from h81 + hlarge:
  -- h81: 5 v_4 < 7 v_3, hlarge: v_3 ≤ 3 v_1, so 5 v_4 < 21 v_1 < 25 v_1 = 5(5 v_1).
  have hab : a ≤ b := by
    rw [ha_def, hb_def, div_le_div_iff₀ h6v1R h6v4R]
    have h81R : (5 : ℝ) * (speeds ⟨3, by omega⟩ : ℝ) < 7 * (speeds ⟨2, by omega⟩ : ℝ) := by
      exact_mod_cast h81
    have hlargeNat : speeds ⟨2, by omega⟩ ≤ 3 * speeds ⟨0, by omega⟩ := by
      exact_mod_cast hlarge
    have hlargeR : (speeds ⟨2, by omega⟩ : ℝ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℝ) := by
      exact_mod_cast hlargeNat
    nlinarith [h81R, hlargeR]
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
  -- k ≥ 1: if k ≤ 0, hjR gives 5 v_5 < (6k+1) v_4 ≤ v_4 < v_5 (hmono), impossible.
  have hv4_int : (0 : ℤ) < (speeds ⟨3, by omega⟩ : ℤ) := by exact_mod_cast hv4
  have hv5_int : (0 : ℤ) < (speeds ⟨4, by omega⟩ : ℤ) := by exact_mod_cast hv5
  have hv45 : (speeds ⟨3, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ) := by
    have hflt : (⟨3, by omega⟩ : Fin 5) < ⟨4, by omega⟩ :=
      Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast hmono hflt
  have hk_ge_1 : 1 ≤ k := by nlinarith [hjR, hv45, hv4_int, hv5_int]
  -- k ≤ 1: §8.1 step 1 kernel rules out k ≥ 2.
  have hk_le_1 : k ≤ 1 := by
    by_contra hk_gt
    push_neg at hk_gt
    exact bhk_8_1_step1_kernel speeds hpos hlarge h81 k hk_gt hjL hjR
  have hk_eq_1 : k = 1 := le_antisymm hk_le_1 hk_ge_1
  subst hk_eq_1
  refine ⟨?_, ?_⟩
  · linarith [hjL]
  · linarith [hjR]

/-- **1345-gap inclusion for §8.1 setup (post-(65)).** With (65) (`5 v_1 < v_5`,
    `5 v_5 < 7 v_4`) plus `hlarge` and §8.1 entry, the interval
    `[max{7/(6 v_3), 13/(6 v_5)}, 11/(6 v_4)]` lies in `unsafeOf ⟨1⟩`
    (runner 2's unsafe set). This is BHK p46: "the 13-gap [7/6, 11/6] is now
    a 1345-gap on `[max{7, 13 x_5}/6, 11 x_4/6]`."

    Geometry: runners 1, 3, 4, 5 are each safe on this interval:
    * Runner 1 in k=0 gap `[1/(6 v_1), 5/(6 v_1)]` (uses `hlarge`, (65)).
    * Runner 3 in k=1 gap `[7/(6 v_3), 11/(6 v_3)]` (uses `v_3 ≤ v_4`).
    * Runner 4 in k=1 gap `[7/(6 v_4), 11/(6 v_4)]` (uses `v_3 ≤ v_4`).
    * Runner 5 in k=2 gap `[13/(6 v_5), 17/(6 v_5)]` (uses (65) `5 v_5 < 7 v_4`). -/
lemma bhk_8_1_1345_gap_incl (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hlarge : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ))
    (h65 : 5 * (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ))
    (h5v5_lt_7v4 : 5 * (speeds ⟨4, by omega⟩ : ℤ) < 7 * (speeds ⟨3, by omega⟩ : ℤ))
    (h_no_lonely : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1/6) :
    Set.Icc (max (7 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
                 (13 / (6 * (speeds ⟨4, by omega⟩ : ℝ))))
            (11 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
    ⊆ unsafeOf speeds ⟨1, by omega⟩ := by
  set v1 : ℝ := (speeds ⟨0, by omega⟩ : ℝ) with hv1_def
  set v3 : ℝ := (speeds ⟨2, by omega⟩ : ℝ) with hv3_def
  set v4 : ℝ := (speeds ⟨3, by omega⟩ : ℝ) with hv4_def
  set v5 : ℝ := (speeds ⟨4, by omega⟩ : ℝ) with hv5_def
  have hv1_pos : 0 < v1 := by rw [hv1_def]; exact_mod_cast hpos _
  have hv3_pos : 0 < v3 := by rw [hv3_def]; exact_mod_cast hpos _
  have hv4_pos : 0 < v4 := by rw [hv4_def]; exact_mod_cast hpos _
  have hv5_pos : 0 < v5 := by rw [hv5_def]; exact_mod_cast hpos _
  have hv1_le_v3 : v1 ≤ v3 := by
    rw [hv1_def, hv3_def]
    exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr (show (0:ℕ) < 2 by omega)))
  have hv3_le_v4 : v3 ≤ v4 := by
    rw [hv3_def, hv4_def]
    exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr (show (2:ℕ) < 3 by omega)))
  -- Cast hypotheses to ℝ
  have hlarge_R : v3 ≤ 3 * v1 := by
    rw [hv3_def, hv1_def]; exact_mod_cast hlarge
  have h65_R : 5 * v1 < v5 := by
    rw [hv1_def, hv5_def]; exact_mod_cast h65
  have h5v5_lt_7v4_R : 5 * v5 < 7 * v4 := by
    rw [hv5_def, hv4_def]; exact_mod_cast h5v5_lt_7v4
  intro t ht
  obtain ⟨htL, htR⟩ := ht
  have htL3 : 7 / (6 * v3) ≤ t := le_trans (le_max_left _ _) htL
  have htL5 : 13 / (6 * v5) ≤ t := le_trans (le_max_right _ _) htL
  obtain ⟨i, hi_unsafe⟩ := h_no_lonely t
  rw [← mem_unsafeOf_iff] at hi_unsafe
  -- Runner 1 (speeds ⟨0⟩): k=0 gap [1/(6 v_1), 5/(6 v_1)].
  have hnot0 : t ∉ unsafeOf speeds ⟨0, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨0, by omega⟩ (hpos _) 0 t
    · rw [show ((0:ℤ):ℝ) + 1/6 = 1/6 from by norm_num, div_div]
      -- 1/(6 v_1) ≤ 7/(6 v_3) ≤ t via hlarge (v_3 ≤ 3 v_1 ⟹ v_3 ≤ 7 v_1).
      have hbound : 1 / (6 * v1) ≤ 7 / (6 * v3) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hlarge_R, hv1_pos]
      calc 1 / (6 * v1) ≤ 7 / (6 * v3) := hbound
        _ ≤ t := htL3
    · rw [show ((0:ℤ):ℝ) + 5/6 = 5/6 from by norm_num, div_div]
      -- t ≤ 11/(6 v_4) ≤ 5/(6 v_1) ⟺ 11 v_1 ≤ 5 v_4.
      -- From h65: 25 v_1 < 5 v_5; from h5v5_lt_7v4: 5 v_5 < 7 v_4 ⟹ 25 v_1 < 7 v_4.
      -- So 5 v_4 > 125 v_1 / 7 > 11 v_1.
      have hbound : 11 / (6 * v4) ≤ 5 / (6 * v1) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h65_R, h5v5_lt_7v4_R, hv1_pos, hv4_pos, hv5_pos]
      calc t ≤ 11 / (6 * v4) := htR
        _ ≤ 5 / (6 * v1) := hbound
  -- Runner 3 (speeds ⟨2⟩): k=1 gap [7/(6 v_3), 11/(6 v_3)].
  have hnot2 : t ∉ unsafeOf speeds ⟨2, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨2, by omega⟩ (hpos _) 1 t
    · rw [show ((1:ℤ):ℝ) + 1/6 = 7/6 from by norm_num, div_div]
      exact htL3
    · rw [show ((1:ℤ):ℝ) + 5/6 = 11/6 from by norm_num, div_div]
      -- t ≤ 11/(6 v_4) ≤ 11/(6 v_3) (v_3 ≤ v_4)
      have hbound : 11 / (6 * v4) ≤ 11 / (6 * v3) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        nlinarith [hv3_le_v4, hv3_pos]
      linarith [htR, hbound]
  -- Runner 4 (speeds ⟨3⟩): k=1 gap [7/(6 v_4), 11/(6 v_4)].
  have hnot3 : t ∉ unsafeOf speeds ⟨3, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨3, by omega⟩ (hpos _) 1 t
    · rw [show ((1:ℤ):ℝ) + 1/6 = 7/6 from by norm_num, div_div]
      -- 7/(6 v_4) ≤ 7/(6 v_3) ≤ t (v_3 ≤ v_4)
      have hbound : 7 / (6 * v4) ≤ 7 / (6 * v3) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        nlinarith [hv3_le_v4, hv3_pos]
      linarith [htL3, hbound]
    · rw [show ((1:ℤ):ℝ) + 5/6 = 11/6 from by norm_num, div_div]
      exact htR
  -- Runner 5 (speeds ⟨4⟩): k=2 gap [13/(6 v_5), 17/(6 v_5)].
  have hnot4 : t ∉ unsafeOf speeds ⟨4, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨4, by omega⟩ (hpos _) 2 t
    · rw [show ((2:ℤ):ℝ) + 1/6 = 13/6 from by norm_num, div_div]
      exact htL5
    · rw [show ((2:ℤ):ℝ) + 5/6 = 17/6 from by norm_num, div_div]
      -- t ≤ 11/(6 v_4) ≤ 17/(6 v_5) ⟺ 11 v_5 ≤ 17 v_4.
      -- From h5v5_lt_7v4 (5 v_5 < 7 v_4): 55 v_5 < 77 v_4 < 85 v_4 = 17·5·v_4,
      -- so 11 v_5 < 17 v_4.
      have hbound : 11 / (6 * v4) ≤ 17 / (6 * v5) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h5v5_lt_7v4_R, hv4_pos, hv5_pos]
      linarith [htR, hbound]
  fin_cases i
  · exact absurd hi_unsafe hnot0
  · exact hi_unsafe
  · exact absurd hi_unsafe hnot2
  · exact absurd hi_unsafe hnot3
  · exact absurd hi_unsafe hnot4

set_option maxHeartbeats 1200000 in
/-- **§8.1 step 2 derivation of BHK (66) and (67) from 1345-gap inclusion.**
    From the 1345-gap inclusion `[max{7/(6 v_3), 13/(6 v_5)}, 11/(6 v_4)]
    ⊆ unsafeOf ⟨1⟩` (i.e., runner 2 must be unsafe on the whole interval),
    derive BHK (66) and (67):

    * **(66)** `25 v_3 < 39 v_2`   (equivalent to BHK's `x_2 < 39/25`)
    * **(67)** `11 v_2 < 7 v_4`    (equivalent to BHK's `11 x_4 < 7 x_2`)

    Strategy: `block_containment` gives `k ∈ ℤ` with
    `(6k-1)/6 < v_2 · max{7/(6 v_3), 13/(6 v_5)}` and
    `v_2 · 11/(6 v_4) < (6k+1)/6`.

    * `k ≥ 1` (from `h81 + hlarge`): if `k ≤ 0`, then `11 v_2 < v_4`, contradicting
      `v_4 < 7 v_3/5 ≤ 21 v_1/5 ≤ 21 v_2/5 = 4.2 v_2 < 11 v_2`.
    * `k ≤ 1` (from `h65 + hlarge`): if `k ≥ 2`, the lower bound forces either
      `11 v_3 < 7 v_2` (impossible: `v_2 ≤ v_3`) or `11 v_5 < 13 v_2 ≤ 13 v_3
      ≤ 39 v_1` and `11 v_5 > 55 v_1`, giving `55 v_1 < 39 v_1` — false.

    With `k = 1`: (67) is immediate. (66) follows by case analysis on the max
    branch + chaining with `h65 + hlarge`.

    Heartbeat bump (1.2M): max-distribution rewrites + dual case-analysis on
    both `lt_max_iff` branches compound the elaboration cost. -/
lemma bhk_8_1_step2_find_66_67 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hlarge : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ))
    (h81 : 5 * (speeds ⟨3, by omega⟩ : ℤ) < 7 * (speeds ⟨2, by omega⟩ : ℤ))
    (h65 : 5 * (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ))
    (h5v5_lt_7v4 : 5 * (speeds ⟨4, by omega⟩ : ℤ) < 7 * (speeds ⟨3, by omega⟩ : ℤ))
    (h_incl : Set.Icc (max (7 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
                            (13 / (6 * (speeds ⟨4, by omega⟩ : ℝ))))
                       (11 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
              ⊆ unsafeOf speeds ⟨1, by omega⟩) :
    (25 * (speeds ⟨2, by omega⟩ : ℤ) < 39 * (speeds ⟨1, by omega⟩ : ℤ)) ∧
    (11 * (speeds ⟨1, by omega⟩ : ℤ) < 7 * (speeds ⟨3, by omega⟩ : ℤ)) := by
  have hv1 : 0 < speeds ⟨0, by omega⟩ := hpos _
  have hv2 : 0 < speeds ⟨1, by omega⟩ := hpos _
  have hv3 : 0 < speeds ⟨2, by omega⟩ := hpos _
  have hv4 : 0 < speeds ⟨3, by omega⟩ := hpos _
  have hv5 : 0 < speeds ⟨4, by omega⟩ := hpos _
  have hv1R : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hv1
  have hv2R : (0 : ℝ) < (speeds ⟨1, by omega⟩ : ℝ) := by exact_mod_cast hv2
  have hv3R : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hv3
  have hv4R : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hv4
  have hv5R : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hv5
  -- Integer hypotheses re-cast to ℤ form
  have hlarge_int : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ) := hlarge
  have hv2_le_v3 : (speeds ⟨1, by omega⟩ : ℤ) ≤ (speeds ⟨2, by omega⟩ : ℤ) := by
    have hflt : (⟨1, by omega⟩ : Fin 5) < ⟨2, by omega⟩ := Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast Nat.le_of_lt (hmono hflt)
  have hv3_le_v4 : (speeds ⟨2, by omega⟩ : ℤ) ≤ (speeds ⟨3, by omega⟩ : ℤ) := by
    have hflt : (⟨2, by omega⟩ : Fin 5) < ⟨3, by omega⟩ := Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast Nat.le_of_lt (hmono hflt)
  have hv1_lt_v2 : (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨1, by omega⟩ : ℤ) := by
    have hflt : (⟨0, by omega⟩ : Fin 5) < ⟨1, by omega⟩ := Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast hmono hflt
  -- Non-emptiness: max{7/(6 v_3), 13/(6 v_5)} ≤ 11/(6 v_4).
  have h6v3R : (0 : ℝ) < 6 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  have h6v4R : (0 : ℝ) < 6 * (speeds ⟨3, by omega⟩ : ℝ) := by positivity
  have h6v5R : (0 : ℝ) < 6 * (speeds ⟨4, by omega⟩ : ℝ) := by positivity
  have h81_R : (5 : ℝ) * (speeds ⟨3, by omega⟩ : ℝ) < 7 * (speeds ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast h81
  have h5v5_lt_7v4_R : (5 : ℝ) * (speeds ⟨4, by omega⟩ : ℝ) <
                       7 * (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast h5v5_lt_7v4
  have h65_R : (5 : ℝ) * (speeds ⟨0, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    exact_mod_cast h65
  have hlarge_R : (speeds ⟨2, by omega⟩ : ℝ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℝ) := by
    exact_mod_cast hlarge
  have hab1 : 7 / (6 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ 11 / (6 * (speeds ⟨3, by omega⟩ : ℝ)) := by
    rw [div_le_div_iff₀ h6v3R h6v4R]
    nlinarith [h81_R, hv3R, hv4R]
  have hab2 : 13 / (6 * (speeds ⟨4, by omega⟩ : ℝ)) ≤
              11 / (6 * (speeds ⟨3, by omega⟩ : ℝ)) := by
    rw [div_le_div_iff₀ h6v5R h6v4R]
    -- Need: 13·(6·v_4) ≤ 11·(6·v_5), i.e., 13 v_4 ≤ 11 v_5.
    -- 13 v_4 < 91 v_3/5 (from h81); 91 v_3/5 ≤ 273 v_1/5 (hlarge); 275 v_1/5 < 11 v_5 (h65).
    nlinarith [h81_R, h5v5_lt_7v4_R, h65_R, hlarge_R, hv1R, hv3R, hv4R, hv5R]
  have hab : max (7 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
                 (13 / (6 * (speeds ⟨4, by omega⟩ : ℝ))) ≤
             11 / (6 * (speeds ⟨3, by omega⟩ : ℝ)) := max_le hab1 hab2
  -- Apply block_containment on runner 2.
  obtain ⟨k, hk_lo, hk_hi⟩ := block_containment speeds ⟨1, by omega⟩ hv2
    _ _ hab h_incl
  -- Convert hk_hi to integer form: 11 v_2 < (6k+1) v_4.
  -- v_2 · 11/(6 v_4) < k + 1/6 ⟹ 11 v_2 < (6k+1) v_4.
  have hk_hi' : 11 * (speeds ⟨1, by omega⟩ : ℝ) <
                (6 * (k : ℝ) + 1) * (speeds ⟨3, by omega⟩ : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hk_hi h6v4R
    have hclear : ((speeds ⟨1, by omega⟩ : ℝ) * (11 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))) *
                  (6 * (speeds ⟨3, by omega⟩ : ℝ)) =
                  11 * (speeds ⟨1, by omega⟩ : ℝ) := by field_simp
    nlinarith [hmul, hclear]
  have hk_hi_int : 11 * (speeds ⟨1, by omega⟩ : ℤ) <
                   (6 * k + 1) * (speeds ⟨3, by omega⟩ : ℤ) := by exact_mod_cast hk_hi'
  -- k ≥ 1: if k ≤ 0, 11 v_2 < v_4 (from hk_hi_int with k=0) or worse.
  -- But v_4 < 7 v_3/5 ≤ 21 v_1/5 ≤ 21 v_2/5 (using hv2 ≥ hv1), so 5 v_4 < 21 v_2 < 55 v_2.
  -- So 11 v_2 > v_4/5 · 5 = v_4, i.e., 11 v_2 ≥ v_4 + 1 strict (integer).
  have hv1_int : (0 : ℤ) < (speeds ⟨0, by omega⟩ : ℤ) := by exact_mod_cast hv1
  have hv2_int : (0 : ℤ) < (speeds ⟨1, by omega⟩ : ℤ) := by exact_mod_cast hv2
  have hv3_int : (0 : ℤ) < (speeds ⟨2, by omega⟩ : ℤ) := by exact_mod_cast hv3
  have hv4_int : (0 : ℤ) < (speeds ⟨3, by omega⟩ : ℤ) := by exact_mod_cast hv4
  have hv5_int : (0 : ℤ) < (speeds ⟨4, by omega⟩ : ℤ) := by exact_mod_cast hv5
  have hv1_le_v2_int : (speeds ⟨0, by omega⟩ : ℤ) ≤ (speeds ⟨1, by omega⟩ : ℤ) :=
    le_of_lt hv1_lt_v2
  -- Helper: 5 v_4 < 21 v_2 (chain: 5 v_4 < 7 v_3 ≤ 21 v_1 ≤ 21 v_2).
  have h5v4_lt_21v2 : 5 * (speeds ⟨3, by omega⟩ : ℤ) < 21 * (speeds ⟨1, by omega⟩ : ℤ) := by
    nlinarith [h81, hlarge, hv1_le_v2_int]
  have hk_ge_1 : 1 ≤ k := by
    by_contra hk_lt
    push_neg at hk_lt
    -- k ≤ 0, so 6k + 1 ≤ 1. hk_hi_int: 11 v_2 < (6k+1) v_4 ≤ v_4.
    have hk_le_0 : k ≤ 0 := by omega
    have h6kp1_le : 6 * k + 1 ≤ 1 := by linarith
    have h11v2_lt_v4 : 11 * (speeds ⟨1, by omega⟩ : ℤ) < (speeds ⟨3, by omega⟩ : ℤ) := by
      calc 11 * (speeds ⟨1, by omega⟩ : ℤ)
          < (6 * k + 1) * (speeds ⟨3, by omega⟩ : ℤ) := hk_hi_int
        _ ≤ 1 * (speeds ⟨3, by omega⟩ : ℤ) := by
            apply mul_le_mul_of_nonneg_right h6kp1_le (le_of_lt hv4_int)
        _ = (speeds ⟨3, by omega⟩ : ℤ) := one_mul _
    -- Combine 11 v_2 < v_4 and 5 v_4 < 21 v_2: 55 v_2 < 5 v_4 < 21 v_2, so 55 < 21. False.
    nlinarith [h11v2_lt_v4, h5v4_lt_21v2, hv2_int]
  -- Convert hk_lo to integer form using the max structure.
  -- hk_lo : k - 1/6 < v_2 · max{7/(6 v_3), 13/(6 v_5)}.
  -- Case 1: max = 7/(6 v_3). Then k - 1/6 < 7 v_2/(6 v_3), so (6k-1) v_3 < 7 v_2.
  -- Case 2: max = 13/(6 v_5). Then k - 1/6 < 13 v_2/(6 v_5), so (6k-1) v_5 < 13 v_2.
  -- So in either case: (6k-1) min{v_3, v_5/?}... actually we get a disjunction.
  -- Need k ≤ 1: rule out k ≥ 2.
  have hk_le_1 : k ≤ 1 := by
    by_contra hk_gt
    push_neg at hk_gt
    -- k ≥ 2. So 6k - 1 ≥ 11.
    have hk_ge_2 : 2 ≤ k := hk_gt
    have h6km1_ge : (11 : ℝ) ≤ 6 * (k : ℝ) - 1 := by exact_mod_cast (by linarith : (11 : ℤ) ≤ 6 * k - 1)
    -- hk_lo : k - 1/6 < v_2 · max{7/(6 v_3), 13/(6 v_5)}.
    -- 6 · (k - 1/6) = 6k - 1 ≤ ... .
    have h6mul : 6 * ((k : ℝ) - 1/6) < 6 *
                 ((speeds ⟨1, by omega⟩ : ℝ) *
                   max (7 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
                       (13 / (6 * (speeds ⟨4, by omega⟩ : ℝ)))) := by
      apply mul_lt_mul_of_pos_left hk_lo (by norm_num)
    have h6km1_simp : 6 * ((k : ℝ) - 1/6) = 6 * (k : ℝ) - 1 := by ring
    rw [h6km1_simp] at h6mul
    -- 6k - 1 ≥ 11
    have h11_lt : (11 : ℝ) < 6 * ((speeds ⟨1, by omega⟩ : ℝ) *
                   max (7 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
                       (13 / (6 * (speeds ⟨4, by omega⟩ : ℝ)))) := by linarith
    -- Distribute v_2 inside max, then distribute 6 inside.
    have hmax_eq : 6 * ((speeds ⟨1, by omega⟩ : ℝ) *
                   max (7 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
                       (13 / (6 * (speeds ⟨4, by omega⟩ : ℝ)))) =
                   max (7 * (speeds ⟨1, by omega⟩ : ℝ) / (speeds ⟨2, by omega⟩ : ℝ))
                       (13 * (speeds ⟨1, by omega⟩ : ℝ) / (speeds ⟨4, by omega⟩ : ℝ)) := by
      rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ (speeds ⟨1, by omega⟩ : ℝ))]
      rw [mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 6)]
      congr 1
      · field_simp
      · field_simp
    rw [hmax_eq] at h11_lt
    rcases lt_max_iff.mp h11_lt with hcase1 | hcase2
    · -- 11 < 7 v_2 / v_3 ⟹ 11 v_3 < 7 v_2. But v_2 ≤ v_3, so 7 v_2 ≤ 7 v_3 < 11 v_3 contradicts.
      have h11v3_lt_7v2 : 11 * (speeds ⟨2, by omega⟩ : ℝ) < 7 * (speeds ⟨1, by omega⟩ : ℝ) := by
        rw [lt_div_iff₀ hv3R] at hcase1
        linarith
      have h11v3_lt_7v2_int : 11 * (speeds ⟨2, by omega⟩ : ℤ) < 7 * (speeds ⟨1, by omega⟩ : ℤ) := by
        exact_mod_cast h11v3_lt_7v2
      nlinarith [h11v3_lt_7v2_int, hv2_le_v3, hv2_int, hv3_int]
    · -- 11 < 13 v_2 / v_5 ⟹ 11 v_5 < 13 v_2. With h65 5 v_1 < v_5 and hv1_lt_v2:
      -- 55 v_1 < 11 v_5 < 13 v_2 = 13 v_2. And v_2 ≥ v_1 + 1 ⟹ 13 v_2 ≥ 13 v_1 + 13.
      -- So 55 v_1 < 13 v_1 + 13 ⟹ 42 v_1 < 13. With v_1 ≥ 1, 42 ≤ 42 v_1 < 13. False.
      have h11v5_lt_13v2 : 11 * (speeds ⟨4, by omega⟩ : ℝ) < 13 * (speeds ⟨1, by omega⟩ : ℝ) := by
        rw [lt_div_iff₀ hv5R] at hcase2
        linarith
      have h11v5_lt_13v2_int : 11 * (speeds ⟨4, by omega⟩ : ℤ) < 13 * (speeds ⟨1, by omega⟩ : ℤ) := by
        exact_mod_cast h11v5_lt_13v2
      -- From h65 5 v_1 < v_5: integer ⟹ 5 v_1 + 1 ≤ v_5 ⟹ 55 v_1 + 11 ≤ 11 v_5 < 13 v_2.
      -- hv1_lt_v2 (integer): v_1 + 1 ≤ v_2 ⟹ 13 v_1 + 13 ≤ 13 v_2.
      -- Combined: 55 v_1 + 11 < 13 v_2 ≤ ... and 13 v_1 + 13 ≤ 13 v_2.
      -- These don't directly conflict. But subtract: 55 v_1 + 11 < 13 v_2 and (rearranging)
      -- 13 v_2 ≥ 13 v_1 + 13 ⟹ 13 v_2 ≥ 13 v_1 + 13.
      -- So 55 v_1 + 11 < 13 v_2 ≥ 13 v_1 + 13 doesn't give contradiction directly.
      -- We need v_2 ≥ v_1 + 1 to be USED: substitute 13 v_2 ≥ 13 v_1 + 13 INTO upper bound?
      -- Actually the right chain: 55 v_1 < 11 v_5 < 13 v_2 = 13(v_1 + d) for d ≥ 1,
      -- = 13 v_1 + 13 d. So 55 v_1 - 13 v_1 < 13 d ⟹ 42 v_1 < 13 d. With v_1 ≥ 1 and d ≥ 1:
      -- 42 ≤ 42 v_1 < 13 d. So 13 d > 42 ⟹ d ≥ 4. So v_2 ≥ v_1 + 4 ≥ 5.
      -- Not a contradiction in general! We need stronger.
      -- Hmm. Let me re-think. Actually use ALL of:
      -- h11v5_lt_13v2_int: 11 v_5 < 13 v_2 ⟹ v_5 < 13 v_2/11.
      -- h5v5_lt_7v4 (cast): 5 v_5 < 7 v_4. With v_5 > 5 v_1: 25 v_1 < 5 v_5 < 7 v_4.
      -- h81: 5 v_4 < 7 v_3. With hlarge v_3 ≤ 3 v_1: 5 v_4 < 21 v_1 ⟹ v_4 < 21 v_1/5.
      -- Combined: 25 v_1 < 7 v_4 < 7·21 v_1/5 = 147 v_1/5 = 29.4 v_1 ✓ no contradiction.
      -- Use h11v5_lt_13v2: 11 v_5 < 13 v_2 ≤ 13 v_3 ≤ 13·3 v_1 = 39 v_1.
      -- And 11 v_5 > 55 v_1 (h65). So 55 v_1 < 39 v_1 ⟹ 16 v_1 < 0 ⟹ FALSE (v_1 > 0). ✓
      have hv2_le_v3_int : (speeds ⟨1, by omega⟩ : ℤ) ≤ (speeds ⟨2, by omega⟩ : ℤ) :=
        hv2_le_v3
      linarith [h11v5_lt_13v2_int, h65, hv2_le_v3_int, hlarge, hv1_int]
  have hk_eq_1 : k = 1 := le_antisymm hk_le_1 hk_ge_1
  subst hk_eq_1
  -- With k = 1: (67) 11 v_2 < 7 v_4 from hk_hi_int.
  have h67 : 11 * (speeds ⟨1, by omega⟩ : ℤ) < 7 * (speeds ⟨3, by omega⟩ : ℤ) := by
    have := hk_hi_int
    linarith
  -- (66): 25 v_3 < 39 v_2.
  -- From hk_lo with k = 1: 5/6 < v_2 · max{7/(6 v_3), 13/(6 v_5)}.
  -- ⟹ 5 < v_2 · max{7/v_3, 13/v_5} = max{7 v_2/v_3, 13 v_2/v_5}.
  -- Case 1: 5 < 7 v_2/v_3 ⟹ 5 v_3 < 7 v_2 ⟹ 25 v_3 < 35 v_2 < 39 v_2 ✓.
  -- Case 2: 5 < 13 v_2/v_5 ⟹ 5 v_5 < 13 v_2.
  --   With h65 5 v_1 < v_5: 25 v_1 < 5 v_5 < 13 v_2. With hlarge v_3 ≤ 3 v_1:
  --   25 v_3 ≤ 75 v_1 < 75/13 · 13 v_2 = ... actually 75 v_1 < 75/25 · 25 v_1 = 3·25 v_1.
  --   From 25 v_1 < 13 v_2: multiply by 3: 75 v_1 < 39 v_2.
  --   So 25 v_3 ≤ 75 v_1 < 39 v_2 ✓.
  have h66 : 25 * (speeds ⟨2, by omega⟩ : ℤ) < 39 * (speeds ⟨1, by omega⟩ : ℤ) := by
    have h6mul : (6 : ℝ) * ((1 : ℝ) - 1/6) < 6 *
                 ((speeds ⟨1, by omega⟩ : ℝ) *
                   max (7 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
                       (13 / (6 * (speeds ⟨4, by omega⟩ : ℝ)))) := by
      have := hk_lo
      have hsimp : ((1 : ℤ) : ℝ) - 1/6 = 1 - 1/6 := by norm_num
      rw [hsimp] at this
      linarith
    have h5_lt : (5 : ℝ) < 6 * ((speeds ⟨1, by omega⟩ : ℝ) *
                   max (7 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
                       (13 / (6 * (speeds ⟨4, by omega⟩ : ℝ)))) := by linarith
    have hmax_eq : 6 * ((speeds ⟨1, by omega⟩ : ℝ) *
                   max (7 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
                       (13 / (6 * (speeds ⟨4, by omega⟩ : ℝ)))) =
                   max (7 * (speeds ⟨1, by omega⟩ : ℝ) / (speeds ⟨2, by omega⟩ : ℝ))
                       (13 * (speeds ⟨1, by omega⟩ : ℝ) / (speeds ⟨4, by omega⟩ : ℝ)) := by
      rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ (speeds ⟨1, by omega⟩ : ℝ))]
      rw [mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 6)]
      congr 1
      · field_simp
      · field_simp
    rw [hmax_eq] at h5_lt
    rcases lt_max_iff.mp h5_lt with hcase1 | hcase2
    · -- 5 < 7 v_2/v_3 ⟹ 5 v_3 < 7 v_2 ⟹ 25 v_3 < 35 v_2 < 39 v_2
      have h5v3_lt_7v2 : 5 * (speeds ⟨2, by omega⟩ : ℝ) < 7 * (speeds ⟨1, by omega⟩ : ℝ) := by
        rw [lt_div_iff₀ hv3R] at hcase1; linarith
      have h5v3_lt_7v2_int : 5 * (speeds ⟨2, by omega⟩ : ℤ) <
                              7 * (speeds ⟨1, by omega⟩ : ℤ) := by
        exact_mod_cast h5v3_lt_7v2
      linarith [h5v3_lt_7v2_int]
    · -- 5 < 13 v_2/v_5 ⟹ 5 v_5 < 13 v_2. Combined with h65 5 v_1 < v_5:
      -- 25 v_1 < 5 v_5 < 13 v_2. Combined with hlarge v_3 ≤ 3 v_1:
      -- 25 v_3 ≤ 75 v_1 = 3 · 25 v_1 < 3 · 13 v_2 = 39 v_2.
      have h5v5_lt_13v2 : 5 * (speeds ⟨4, by omega⟩ : ℝ) < 13 * (speeds ⟨1, by omega⟩ : ℝ) := by
        rw [lt_div_iff₀ hv5R] at hcase2; linarith
      have h5v5_lt_13v2_int : 5 * (speeds ⟨4, by omega⟩ : ℤ) <
                              13 * (speeds ⟨1, by omega⟩ : ℤ) := by
        exact_mod_cast h5v5_lt_13v2
      nlinarith [h5v5_lt_13v2_int, h65, hlarge]
  exact ⟨h66, h67⟩

/-- **Arithmetic kernel for BHK §8.1.1 step 3 (1235-gap forces `k ≥ 5`).**
    From `23 v_4 < (6k+1) v_3` (the right side of `block_containment` applied
    to the 1235-gap), together with `hlarge`, `h65` (`5 v_1 < v_5`), and
    `h5v5_lt_7v4` (`5 v_5 < 7 v_4` — byproduct of `bhk_8_1_step1_find_65`),
    derive a contradiction when `k ≤ 4`.

    Arithmetic chain:

    * `k ≤ 4` ⟹ `6k+1 ≤ 25`, so `23 v_4 < 25 v_3`. Multiply by 7:
      `161 v_4 < 175 v_3`.
    * `h5v5_lt_7v4` × 23: `115 v_5 < 161 v_4`. Chain: `115 v_5 < 175 v_3`.
    * `h65` × 23 / 1: `115 v_5 > 575 v_1` (since `v_5 > 5 v_1` ⟹ `23 v_5 > 115 v_1`,
      then × 5 gives `115 v_5 > 575 v_1`). So `575 v_1 < 175 v_3`.
    * `hlarge` × 175: `175 v_3 ≤ 525 v_1`. Chain: `575 v_1 < 525 v_1`,
      contradicting `v_1 > 0`. -/
lemma bhk_8_1_step3_kernel (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (hlarge : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ))
    (h65 : 5 * (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ))
    (h5v5_lt_7v4 : 5 * (speeds ⟨4, by omega⟩ : ℤ) < 7 * (speeds ⟨3, by omega⟩ : ℤ))
    (k : ℤ) (hk : k ≤ 4)
    (hjR : 23 * (speeds ⟨3, by omega⟩ : ℤ) <
              (6 * k + 1) * (speeds ⟨2, by omega⟩ : ℤ)) :
    False := by
  have hv1 : (0 : ℤ) < (speeds ⟨0, by omega⟩ : ℤ) := by exact_mod_cast hpos ⟨0, by omega⟩
  have hv3 : (0 : ℤ) < (speeds ⟨2, by omega⟩ : ℤ) := by exact_mod_cast hpos ⟨2, by omega⟩
  have h6kp1_le : 6 * k + 1 ≤ 25 := by linarith
  -- `23 v_4 < 25 v_3` from `hjR` and `6k+1 ≤ 25`.
  have h_23v4_25v3 : 23 * (speeds ⟨3, by omega⟩ : ℤ) <
                     25 * (speeds ⟨2, by omega⟩ : ℤ) := by
    calc 23 * (speeds ⟨3, by omega⟩ : ℤ)
        < (6 * k + 1) * (speeds ⟨2, by omega⟩ : ℤ) := hjR
      _ ≤ 25 * (speeds ⟨2, by omega⟩ : ℤ) := by
          apply mul_le_mul_of_nonneg_right h6kp1_le (le_of_lt hv3)
  nlinarith [h_23v4_25v3, h5v5_lt_7v4, h65, hlarge, hv1]

/-- **§8.1.1 step 3 derivation of BHK (71b) from 1235-gap inclusion.** From
    the BHK §8.1.1 inclusion `[37/(6 v_5), 23/(6 v_3)] ⊆ unsafeOf speeds ⟨3⟩`
    (the 1235-gap covered by runner 4 alone), derive BHK's (71b):

    * `29 v_5 < 37 v_4`         (i.e. `29 x_4 < 37 x_5`)

    Strategy:
    1. `block_containment` gives an integer `k` with `(6k-1) v_5 < 37 v_4` and
       `23 v_4 < (6k+1) v_3`.
    2. `bhk_8_1_step3_kernel` rules out `k ≤ 4`, so `k ≥ 5`.
    3. From `(6k-1) v_5 < 37 v_4` with `k ≥ 5`: `29 v_5 ≤ (6k-1) v_5 < 37 v_4`.

    `hab` (`a ≤ b`) follows from `h65 + hlarge`:
    `37 v_3 ≤ 111 v_1 < 115 v_1 ≤ 23 v_5`. -/
lemma bhk_8_1_step3_find_71b (speeds : Fin 5 → ℕ) (_hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hlarge : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ))
    (h65 : 5 * (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ))
    (h5v5_lt_7v4 : 5 * (speeds ⟨4, by omega⟩ : ℤ) < 7 * (speeds ⟨3, by omega⟩ : ℤ))
    (h_incl : Set.Icc (37 / (6 * (speeds ⟨4, by omega⟩ : ℝ)))
                       (23 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
              ⊆ unsafeOf speeds ⟨3, by omega⟩) :
    29 * (speeds ⟨4, by omega⟩ : ℤ) < 37 * (speeds ⟨3, by omega⟩ : ℤ) := by
  have hv1 : 0 < speeds ⟨0, by omega⟩ := hpos _
  have hv3 : 0 < speeds ⟨2, by omega⟩ := hpos _
  have hv4 : 0 < speeds ⟨3, by omega⟩ := hpos _
  have hv5 : 0 < speeds ⟨4, by omega⟩ := hpos _
  have hv1R : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hv1
  have hv3R : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hv3
  have hv5R : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hv5
  have h6v3R : (0 : ℝ) < 6 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  have h6v5R : (0 : ℝ) < 6 * (speeds ⟨4, by omega⟩ : ℝ) := by positivity
  set a : ℝ := 37 / (6 * (speeds ⟨4, by omega⟩ : ℝ)) with ha_def
  set b : ℝ := 23 / (6 * (speeds ⟨2, by omega⟩ : ℝ)) with hb_def
  -- `a ≤ b` ⟺ `37 v_3 ≤ 23 v_5`. From `h65` and `hlarge`:
  -- `37 v_3 ≤ 111 v_1 < 115 v_1 ≤ 23 v_5`.
  have hab : a ≤ b := by
    rw [ha_def, hb_def, div_le_div_iff₀ h6v5R h6v3R]
    have h65R : (5 : ℝ) * (speeds ⟨0, by omega⟩ : ℝ) <
                (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast h65
    have hlargeR : (speeds ⟨2, by omega⟩ : ℝ) ≤
                   3 * (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hlarge
    nlinarith [h65R, hlargeR, hv1R]
  obtain ⟨k, hk_lo, hk_hi⟩ :=
    block_containment speeds ⟨3, by omega⟩ hv4 a b hab h_incl
  have hva_eq : (speeds ⟨3, by omega⟩ : ℝ) * a =
                37 * (speeds ⟨3, by omega⟩ : ℝ) /
                  (6 * (speeds ⟨4, by omega⟩ : ℝ)) := by
    rw [ha_def]; ring
  have hvb_eq : (speeds ⟨3, by omega⟩ : ℝ) * b =
                23 * (speeds ⟨3, by omega⟩ : ℝ) /
                  (6 * (speeds ⟨2, by omega⟩ : ℝ)) := by
    rw [hb_def]; ring
  rw [hva_eq] at hk_lo
  rw [hvb_eq] at hk_hi
  -- (6k - 1) v_5 < 37 v_4 (from hk_lo).
  have hjL_R : (6 * (k : ℝ) - 1) * (speeds ⟨4, by omega⟩ : ℝ) <
               37 * (speeds ⟨3, by omega⟩ : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hk_lo h6v5R
    have hclear : (37 * (speeds ⟨3, by omega⟩ : ℝ) /
                    (6 * (speeds ⟨4, by omega⟩ : ℝ))) *
                  (6 * (speeds ⟨4, by omega⟩ : ℝ)) =
                  37 * (speeds ⟨3, by omega⟩ : ℝ) := by field_simp
    nlinarith [hmul, hclear]
  -- 23 v_4 < (6k + 1) v_3 (from hk_hi).
  have hjR_R : 23 * (speeds ⟨3, by omega⟩ : ℝ) <
               (6 * (k : ℝ) + 1) * (speeds ⟨2, by omega⟩ : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hk_hi h6v3R
    have hclear : (23 * (speeds ⟨3, by omega⟩ : ℝ) /
                    (6 * (speeds ⟨2, by omega⟩ : ℝ))) *
                  (6 * (speeds ⟨2, by omega⟩ : ℝ)) =
                  23 * (speeds ⟨3, by omega⟩ : ℝ) := by field_simp
    nlinarith [hmul, hclear]
  have hjL : (6 * k - 1) * (speeds ⟨4, by omega⟩ : ℤ) <
             37 * (speeds ⟨3, by omega⟩ : ℤ) := by exact_mod_cast hjL_R
  have hjR : 23 * (speeds ⟨3, by omega⟩ : ℤ) <
             (6 * k + 1) * (speeds ⟨2, by omega⟩ : ℤ) := by exact_mod_cast hjR_R
  -- `k ≥ 5` via the step-3 kernel (rules out `k ≤ 4`).
  have hk_ge_5 : 5 ≤ k := by
    by_contra hk_lt
    push_neg at hk_lt
    have hk_le_4 : k ≤ 4 := by linarith
    exact bhk_8_1_step3_kernel speeds hpos hlarge h65 h5v5_lt_7v4 k hk_le_4 hjR
  -- Conclude `29 v_5 < 37 v_4` from `(6k-1) v_5 < 37 v_4` and `6k - 1 ≥ 29`.
  have hv5_int : (0 : ℤ) < (speeds ⟨4, by omega⟩ : ℤ) := by exact_mod_cast hv5
  have h6km1 : 29 ≤ 6 * k - 1 := by linarith
  have h_chain : 29 * (speeds ⟨4, by omega⟩ : ℤ) ≤
                 (6 * k - 1) * (speeds ⟨4, by omega⟩ : ℤ) :=
    mul_le_mul_of_nonneg_right h6km1 (le_of_lt hv5_int)
  linarith [h_chain, hjL]

/-- **Arithmetic kernel for BHK §8.1.1.** From the three structural
    inequalities derived in BHK p46:

    * (65)  `5 v_1 < v_5`         (i.e. `5 x_5 < x_1`)
    * (70b) `5 v_4 < 19 v_1`      (i.e. `5 x_1 < 19 x_4`)
    * (71b) `29 v_5 < 37 v_4`     (i.e. `29 x_4 < 37 x_5`)

    derive a numerical contradiction.

    Arithmetic chain:

    * From (65) and (71b): `29 · 5 v_1 < 29 v_5 < 37 v_4`, i.e. `145 v_1 < 37 v_4`.
      Multiply by 5: `725 v_1 < 185 v_4`.
    * From (70b) × 37: `185 v_4 < 703 v_1`.
    * Chain: `725 v_1 < 185 v_4 < 703 v_1`, divide by `v_1 > 0`: `725 < 703`. False. -/
lemma bhk_case_8_1_1_kernel (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (h65  : 5 * (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ))
    (h70b : 5 * (speeds ⟨3, by omega⟩ : ℤ) < 19 * (speeds ⟨0, by omega⟩ : ℤ))
    (h71b : 29 * (speeds ⟨4, by omega⟩ : ℤ) < 37 * (speeds ⟨3, by omega⟩ : ℤ)) :
    False := by
  have hv1 : (0 : ℤ) < (speeds ⟨0, by omega⟩ : ℤ) := by exact_mod_cast hpos ⟨0, by omega⟩
  nlinarith [h65, h70b, h71b, hv1]

/-- **BHK §8.1.1.** Sub-case of `x_1 ≤ 3` with `x_4 > 5/7` (de-normalised:
    `5 v_3 < 7 v_2`, since BHK uses `x_3 = 1`, i.e. `5 * speeds ⟨3⟩ < 7 * speeds ⟨2⟩`)
    AND `13 x_4 ≤ 7 x_2` (de-normalised: `13 v_2 ≤ 7 v_4`, i.e.
    `13 * speeds ⟨1⟩ ≤ 7 * speeds ⟨3⟩`). See BHK p46.

    Proof structure: assume for contradiction no lonely `t` exists. BHK then
    derives three structural inequalities via three gap analyses:

    * 1234-gap → (65) `5 x_5 < x_1` (closed via `bhk_8_1_step1_find_65`)
    * 1235-gap → (71b) `29 x_4 < 37 x_5` (closed via `bhk_8_1_step3_find_71b`,
      assuming the inclusion; the inclusion itself remains residual)
    * 123-gap `[13/6, 5 x_1/6]` → (70b) `5 x_1 < 19 x_4` (residual)

    These three contradict via `bhk_case_8_1_1_kernel`. The residual sorry
    now contains exactly two atomic pieces: (a) (70b), and (b) the 1235-gap
    inclusion `[37/(6 v_5), 23/(6 v_3)] ⊆ unsafeOf speeds ⟨3⟩`. -/
theorem bhk_case_8_1_1 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hlarge : speeds ⟨2, by omega⟩ ≤ 3 * speeds ⟨0, by omega⟩)
    (h81 : 5 * speeds ⟨3, by omega⟩ < 7 * speeds ⟨2, by omega⟩)
    (h811 : 13 * speeds ⟨1, by omega⟩ ≤ 7 * speeds ⟨3, by omega⟩) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  by_contra h_no_lonely
  push_neg at h_no_lonely
  -- 1234-gap inclusion via the common helper (depends only on monotonicity).
  have h_1234_incl := bhk_8_1_1234_gap_incl speeds hmono hpos h_no_lonely
  -- Apply find_65 to extract (65) `5 v_1 < v_5` and `5 v_5 < 7 v_4`.
  have hlarge_int : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ) := by
    exact_mod_cast hlarge
  have h81_int : 5 * (speeds ⟨3, by omega⟩ : ℤ) < 7 * (speeds ⟨2, by omega⟩ : ℤ) := by
    exact_mod_cast h81
  obtain ⟨h65, h5v5_lt_7v4⟩ :=
    bhk_8_1_step1_find_65 speeds hmono hpos hlarge_int h81_int h_1234_incl
  -- Structural fact: `v_4 < 2 v_3` via the §8 helper (123-gap + bhk_lemma_4).
  -- Reusable structural fact, not directly load-bearing for §8.1.1's
  -- residual but available for downstream use.
  have _hv4_lt_2v3 : (speeds ⟨3, by omega⟩ : ℝ) < 2 * (speeds ⟨2, by omega⟩ : ℝ) :=
    bhk_8_v4_lt_2v3 speeds hmono hpos hlarge h_no_lonely
  -- Residual structural sorry: derive (70b) `5 v_4 < 19 v_1` and the 1235-gap
  -- inclusion `[37/(6 v_5), 23/(6 v_3)] ⊆ unsafeOf speeds ⟨3⟩` (BHK p46).
  -- The 1235-gap inclusion's geometric proof requires `11 v_5 < 19 v_3` (BHK
  -- (68)), which itself requires the §8.1 cascade: 13-gap → 1345-gap → (66),
  -- (67); → 1234-gap → (68). Each is its own block_containment + arithmetic.
  obtain ⟨h70b, h_1235_incl⟩ :
      (5 * (speeds ⟨3, by omega⟩ : ℤ) < 19 * (speeds ⟨0, by omega⟩ : ℤ)) ∧
      Set.Icc (37 / (6 * (speeds ⟨4, by omega⟩ : ℝ)))
              (23 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
        ⊆ unsafeOf speeds ⟨3, by omega⟩ := by
    sorry
  -- Apply find_71b to derive (71b) `29 v_5 < 37 v_4` from the inclusion.
  have h71b := bhk_8_1_step3_find_71b speeds hmono hpos hlarge_int h65
                                       h5v5_lt_7v4 h_1235_incl
  exact bhk_case_8_1_1_kernel speeds hpos h65 h70b h71b

/-- **BHK §8.1.2.** Sub-case of `x_1 ≤ 3` with `x_4 > 5/7` (de-normalised:
    `5 * speeds ⟨3⟩ < 7 * speeds ⟨2⟩`) AND `7 x_2 < 13 x_4` (de-normalised:
    `7 * speeds ⟨3⟩ < 13 * speeds ⟨1⟩`). See BHK p46–47. -/
theorem bhk_case_8_1_2 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hlarge : speeds ⟨2, by omega⟩ ≤ 3 * speeds ⟨0, by omega⟩)
    (h81 : 5 * speeds ⟨3, by omega⟩ < 7 * speeds ⟨2, by omega⟩)
    (h812 : 7 * speeds ⟨3, by omega⟩ < 13 * speeds ⟨1, by omega⟩) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  sorry

/-- **Arithmetic kernel for BHK §8.2.1.** Given the existence of an integer
    `j ≥ 2` satisfying the BHK `j`-conditions
    `(6j-1) v_4 < 7 v_5` and `5 v_5 < (6j+1) v_3`, together with the case
    hypotheses `5 v_1 < v_4` (§8.2.1) and `v_3 ≤ 3 v_1` (§8 entry),
    derive a contradiction.

    Arithmetic chain (BHK p48):

    * `5 v_1 < v_4`            gives `5 (6j-1) v_1 < (6j-1) v_4 < 7 v_5`.
    * `v_3 ≤ 3 v_1`            gives `5 v_5 < (6j+1) v_3 ≤ 3 (6j+1) v_1`.
    * Multiply by 5 and 7 to get `25 (6j-1) v_1 < 35 v_5 < 21 (6j+1) v_1`.
    * Cancel `v_1 > 0`: `25 (6j-1) < 21 (6j+1)`, i.e. `24 j < 46`.
    * `j ≥ 2` gives `24 j ≥ 48 > 46`, contradiction.

    This is BHK's "j > 1" derivation from §8.2.1; the bound
    `x_1 > 25(6j-1)/(7(6j+1)) ≥ 275/91 > 3` exactly mirrors `24 j < 46`
    contradicting `j ≥ 2`. -/
lemma bhk_case_8_2_1_kernel (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (hlarge : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ))
    (h821 : 5 * (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨3, by omega⟩ : ℤ))
    (j : ℤ) (hj : 2 ≤ j)
    (hjL : (6 * j - 1) * (speeds ⟨3, by omega⟩ : ℤ) < 7 * (speeds ⟨4, by omega⟩ : ℤ))
    (hjR : 5 * (speeds ⟨4, by omega⟩ : ℤ) < (6 * j + 1) * (speeds ⟨2, by omega⟩ : ℤ)) :
    False := by
  have hv1 : (0 : ℤ) < (speeds ⟨0, by omega⟩ : ℤ) := by exact_mod_cast hpos ⟨0, by omega⟩
  have h6jm1_pos : 0 < 6 * j - 1 := by linarith
  have h6jp1_pos : 0 < 6 * j + 1 := by linarith
  have stepA : (6 * j - 1) * (5 * (speeds ⟨0, by omega⟩ : ℤ)) <
                (6 * j - 1) * (speeds ⟨3, by omega⟩ : ℤ) :=
    mul_lt_mul_of_pos_left h821 h6jm1_pos
  have stepB : (6 * j + 1) * (speeds ⟨2, by omega⟩ : ℤ) ≤
                (6 * j + 1) * (3 * (speeds ⟨0, by omega⟩ : ℤ)) :=
    mul_le_mul_of_nonneg_left hlarge (le_of_lt h6jp1_pos)
  nlinarith [stepA, stepB, hjL, hjR, hv1, hj]

/-- **§8.2.1 `j`-derivation from BHK geometric inclusion.** From the BHK §8.2.1
    inclusion `[7/(6 v_4), 5/(6 v_3)] ⊆ unsafeOf speeds ⟨4⟩` (i.e. the
    sub-interval is covered by 5-blocks), together with `h82` and monotonicity,
    derive `∃ j ≥ 2` satisfying the BHK `j`-conditions.

    Uses `block_containment` to extract the integer (the interval must lie in
    a SINGLE 5-block). Then `h82 + hmono` force `j ≥ 2`. Combined with
    `bhk_case_8_2_1_kernel`, this reduces §8.2.1 to just the geometric
    inclusion — the only remaining structural step. -/
lemma bhk_case_8_2_1_find_j (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (h82 : 7 * speeds ⟨2, by omega⟩ ≤ 5 * speeds ⟨3, by omega⟩)
    (h_incl : Set.Icc (7 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
                       (5 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
              ⊆ unsafeOf speeds ⟨4, by omega⟩) :
    ∃ j : ℤ, 2 ≤ j ∧
      (6 * j - 1) * (speeds ⟨3, by omega⟩ : ℤ) <
        7 * (speeds ⟨4, by omega⟩ : ℤ) ∧
      5 * (speeds ⟨4, by omega⟩ : ℤ) <
        (6 * j + 1) * (speeds ⟨2, by omega⟩ : ℤ) := by
  have hv3 : 0 < speeds ⟨2, by omega⟩ := hpos _
  have hv4 : 0 < speeds ⟨3, by omega⟩ := hpos _
  have hv5 : 0 < speeds ⟨4, by omega⟩ := hpos _
  have hv3R : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hv3
  have hv4R : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hv4
  have h6v3R : (0 : ℝ) < 6 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  have h6v4R : (0 : ℝ) < 6 * (speeds ⟨3, by omega⟩ : ℝ) := by positivity
  -- Endpoint setup. a = 7/(6 v_4), b = 5/(6 v_3).
  set a : ℝ := 7 / (6 * (speeds ⟨3, by omega⟩ : ℝ)) with ha_def
  set b : ℝ := 5 / (6 * (speeds ⟨2, by omega⟩ : ℝ)) with hb_def
  -- a ≤ b ⟺ 7/(6 v_4) ≤ 5/(6 v_3) ⟺ 7 v_3 ≤ 5 v_4 (h82).
  have hab : a ≤ b := by
    rw [ha_def, hb_def, div_le_div_iff₀ h6v4R h6v3R]
    have h82R : 7 * (speeds ⟨2, by omega⟩ : ℝ) ≤ 5 * (speeds ⟨3, by omega⟩ : ℝ) := by
      exact_mod_cast h82
    linarith
  -- Apply block_containment.
  obtain ⟨k, hk_lo, hk_hi⟩ := block_containment speeds ⟨4, by omega⟩ hv5 a b hab h_incl
  -- Convert v_5 * a and v_5 * b to clean forms.
  have hva_eq : (speeds ⟨4, by omega⟩ : ℝ) * a =
                7 * (speeds ⟨4, by omega⟩ : ℝ) / (6 * (speeds ⟨3, by omega⟩ : ℝ)) := by
    rw [ha_def]; ring
  have hvb_eq : (speeds ⟨4, by omega⟩ : ℝ) * b =
                5 * (speeds ⟨4, by omega⟩ : ℝ) / (6 * (speeds ⟨2, by omega⟩ : ℝ)) := by
    rw [hb_def]; ring
  rw [hva_eq] at hk_lo
  rw [hvb_eq] at hk_hi
  -- hk_lo : (k : ℝ) - 1/6 < 7 v_5 / (6 v_4)
  -- hk_hi : 5 v_5 / (6 v_3) < (k : ℝ) + 1/6
  -- Convert to (6k - 1) v_4 < 7 v_5 in ℝ.
  have hjL_R : (6 * (k : ℝ) - 1) * (speeds ⟨3, by omega⟩ : ℝ) <
               7 * (speeds ⟨4, by omega⟩ : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hk_lo h6v4R
    have hclear : (7 * (speeds ⟨4, by omega⟩ : ℝ) / (6 * (speeds ⟨3, by omega⟩ : ℝ))) *
                  (6 * (speeds ⟨3, by omega⟩ : ℝ)) = 7 * (speeds ⟨4, by omega⟩ : ℝ) := by
      field_simp
    nlinarith [hmul, hclear]
  -- Convert to 5 v_5 < (6k + 1) v_3 in ℝ.
  have hjR_R : 5 * (speeds ⟨4, by omega⟩ : ℝ) <
               (6 * (k : ℝ) + 1) * (speeds ⟨2, by omega⟩ : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hk_hi h6v3R
    have hclear : (5 * (speeds ⟨4, by omega⟩ : ℝ) / (6 * (speeds ⟨2, by omega⟩ : ℝ))) *
                  (6 * (speeds ⟨2, by omega⟩ : ℝ)) = 5 * (speeds ⟨4, by omega⟩ : ℝ) := by
      field_simp
    nlinarith [hmul, hclear]
  -- Cast to ℤ.
  have hjL : (6 * k - 1) * (speeds ⟨3, by omega⟩ : ℤ) <
             7 * (speeds ⟨4, by omega⟩ : ℤ) := by exact_mod_cast hjL_R
  have hjR : 5 * (speeds ⟨4, by omega⟩ : ℤ) <
             (6 * k + 1) * (speeds ⟨2, by omega⟩ : ℤ) := by exact_mod_cast hjR_R
  -- Derive k ≥ 2 from h82, hmono, hjR.
  -- 7 v_3 ≤ 5 v_4 ≤ 5 v_5 < (6k+1) v_3, so 7 < 6k+1, k > 1.
  have hk_ge_2 : 2 ≤ k := by
    have hv34 : (speeds ⟨3, by omega⟩ : ℤ) ≤ (speeds ⟨4, by omega⟩ : ℤ) := by
      have hflt : (⟨3, by omega⟩ : Fin 5) < ⟨4, by omega⟩ :=
        Fin.mk_lt_mk.mpr (by omega)
      have h : speeds ⟨3, by omega⟩ < speeds ⟨4, by omega⟩ := hmono hflt
      exact_mod_cast Nat.le_of_lt h
    have h82_int : 7 * (speeds ⟨2, by omega⟩ : ℤ) ≤ 5 * (speeds ⟨3, by omega⟩ : ℤ) := by
      exact_mod_cast h82
    have hv3_pos_int : (0 : ℤ) < (speeds ⟨2, by omega⟩ : ℤ) := by exact_mod_cast hv3
    nlinarith [hjR, h82_int, hv34, hv3_pos_int]
  exact ⟨k, hk_ge_2, hjL, hjR⟩

set_option maxHeartbeats 1000000 in
/-- **BHK §8.2.1.** Sub-case of `x_1 ≤ 3` with `x_4 ≤ 5/7` (de-normalised:
    `7 * speeds ⟨2⟩ ≤ 5 * speeds ⟨3⟩`) AND `5 x_4 < x_1` (de-normalised:
    `5 * speeds ⟨0⟩ < speeds ⟨3⟩`). See BHK p47–48.

    Proof structure: assume for contradiction no lonely `t` exists. The
    123-gap `[x_1/6, 5/6]` (complement of `B_1 ∪ B_2 ∪ B_3` in this region)
    must be covered by `B_4 ∪ B_5`. Under §8.2.1's `5 x_4 < x_1`, the
    sub-interval `[7 x_4/6, 5/6]` is covered by `B_5` alone. `find_j` then
    extracts `j ≥ 2`, and `bhk_case_8_2_1_kernel` closes via arithmetic.

    The remaining structural step is the inclusion
    `[7/(6 v_4), 5/(6 v_3)] ⊆ unsafeOf speeds ⟨4⟩` — the BHK §8.2.1 geometric
    derivation that the sub-interval is in `B_5` alone. -/
theorem bhk_case_8_2_1 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hlarge : speeds ⟨2, by omega⟩ ≤ 3 * speeds ⟨0, by omega⟩)
    (h82 : 7 * speeds ⟨2, by omega⟩ ≤ 5 * speeds ⟨3, by omega⟩)
    (h821 : 5 * speeds ⟨0, by omega⟩ < speeds ⟨3, by omega⟩) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  by_contra h_no_lonely
  push_neg at h_no_lonely
  -- BHK §8.2.1 geometric inclusion [7/(6 v_4), 5/(6 v_3)] ⊆ unsafeOf 5.
  -- Strategy:
  --   (1) From h_no_lonely + monotonicity, establish 123-gap inclusion
  --       [1/(6 v_1), 5/(6 v_3)] ⊆ unsafeOf 3 ∪ unsafeOf 4.
  --   (2) Apply bhk_lemma_4 to get 5/(6 v_3) - 1/(6 v_1) < 2/(3 v_4), then
  --       derive v_4 < 2 v_3 (the structural fact BHK uses).
  --   (3) On the smaller interval [7/(6 v_4), 5/(6 v_3)], rule out runners
  --       0, 1, 2, 3 (using v_4 < 2 v_3 to handle runner 3 at k=1), forcing
  --       membership in unsafeOf 4.
  -- Abbreviations and basic facts.
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
  have hv1_le_v2 : v1 ≤ v2 := by
    rw [hv1_def, hv2_def]; exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr (by omega)))
  have hv1_le_v3 : v1 ≤ v3 := by
    rw [hv1_def, hv3_def]; exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr
      (show (0:ℕ) < 2 by omega)))
  have hv2_le_v3 : v2 ≤ v3 := by
    rw [hv2_def, hv3_def]; exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr
      (show (1:ℕ) < 2 by omega)))
  have hv3_le_v4 : v3 ≤ v4 := by
    rw [hv3_def, hv4_def]; exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr
      (show (2:ℕ) < 3 by omega)))
  have hv4_le_v5 : v4 ≤ v5 := by
    rw [hv4_def, hv5_def]; exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr
      (show (3:ℕ) < 4 by omega)))
  -- Real-cast versions of the case hypotheses.
  have hlargeR : v3 ≤ 3 * v1 := by
    rw [hv1_def, hv3_def]; exact_mod_cast hlarge
  have h82R : 7 * v3 ≤ 5 * v4 := by
    rw [hv3_def, hv4_def]; exact_mod_cast h82
  have h821R : 5 * v1 < v4 := by
    rw [hv1_def, hv4_def]; exact_mod_cast h821
  -- (1) Derive `v_4 < 2 v_3` via the reusable §8 helper (123-gap + bhk_lemma_4
  --     + arithmetic; see `bhk_8_v4_lt_2v3`).
  have hv4_lt_2v3 : v4 < 2 * v3 := by
    have h := bhk_8_v4_lt_2v3 speeds hmono hpos hlarge h_no_lonely
    rw [hv3_def, hv4_def]; exact h
  -- Precomputed bounds: v_4 < 6 v_i for i=1,2,3 to feed linarith chains below.
  have hv4_lt_6v1 : v4 < 6 * v1 := by linarith [hv4_lt_2v3, hlargeR]
  have hv4_lt_6v2 : v4 < 6 * v2 := by linarith [hv4_lt_6v1, hv1_le_v2]
  have hv4_lt_6v3 : v4 < 6 * v3 := by linarith [hv4_lt_2v3, hv3_pos]
  -- (3) Build target inclusion.
  have h_incl : Set.Icc (7 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
                         (5 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
                ⊆ unsafeOf speeds ⟨4, by omega⟩ := by
    intro t ht
    -- Rewrite to use v3, v4 abbreviations.
    rw [show (speeds ⟨3, by omega⟩ : ℝ) = v4 from hv4_def,
        show (speeds ⟨2, by omega⟩ : ℝ) = v3 from hv3_def] at ht
    obtain ⟨htL, htR⟩ := ht
    -- From h_no_lonely.
    obtain ⟨i, hi_unsafe⟩ := h_no_lonely t
    rw [← mem_unsafeOf_iff] at hi_unsafe
    -- Establish t ≤ 5/(6 v_3) and 7/(6 v_4) ≤ t for use below.
    -- Rule out runner 0 (k=0). Bounds: 7/(6 v_4) ≤ t ≤ 5/(6 v_3), and we
    -- need 1/(6 v_1) ≤ t ≤ 5/(6 v_1).
    have hnot0 : t ∉ unsafeOf speeds ⟨0, by omega⟩ := by
      apply not_mem_unsafeOf_of_in_gap speeds ⟨0, by omega⟩ (hpos _) 0 t
      · rw [show ((0:ℤ):ℝ) + 1/6 = 1/6 from by norm_num, div_div]
        calc (1 : ℝ) / (6 * (speeds ⟨0, by omega⟩ : ℝ))
            ≤ 7 / (6 * v4) := by
              rw [← hv1_def, div_le_div_iff₀ (by positivity) (by positivity)]
              linarith [hv4_lt_6v1, hv1_pos]
          _ ≤ t := htL
      · rw [show ((0:ℤ):ℝ) + 5/6 = 5/6 from by norm_num, div_div]
        calc t ≤ 5 / (6 * v3) := htR
          _ ≤ 5 / (6 * (speeds ⟨0, by omega⟩ : ℝ)) := by
              rw [← hv1_def]
              apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
              nlinarith [hv1_le_v3, hv1_pos, hv3_pos]
    -- Rule out runner 1 (k=0). Bounds need 1/(6 v_2) ≤ t ≤ 5/(6 v_2).
    have hnot1 : t ∉ unsafeOf speeds ⟨1, by omega⟩ := by
      apply not_mem_unsafeOf_of_in_gap speeds ⟨1, by omega⟩ (hpos _) 0 t
      · rw [show ((0:ℤ):ℝ) + 1/6 = 1/6 from by norm_num, div_div]
        calc (1 : ℝ) / (6 * (speeds ⟨1, by omega⟩ : ℝ))
            ≤ 7 / (6 * v4) := by
              rw [← hv2_def, div_le_div_iff₀ (by positivity) (by positivity)]
              linarith [hv4_lt_6v2, hv2_pos]
          _ ≤ t := htL
      · rw [show ((0:ℤ):ℝ) + 5/6 = 5/6 from by norm_num, div_div]
        calc t ≤ 5 / (6 * v3) := htR
          _ ≤ 5 / (6 * (speeds ⟨1, by omega⟩ : ℝ)) := by
              rw [← hv2_def]
              apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
              nlinarith [hv2_le_v3, hv2_pos, hv3_pos]
    -- Rule out runner 2 (k=0). Bounds need 1/(6 v_3) ≤ t ≤ 5/(6 v_3).
    have hnot2 : t ∉ unsafeOf speeds ⟨2, by omega⟩ := by
      apply not_mem_unsafeOf_of_in_gap speeds ⟨2, by omega⟩ (hpos _) 0 t
      · rw [show ((0:ℤ):ℝ) + 1/6 = 1/6 from by norm_num, div_div]
        calc (1 : ℝ) / (6 * (speeds ⟨2, by omega⟩ : ℝ))
            ≤ 7 / (6 * v4) := by
              rw [← hv3_def, div_le_div_iff₀ (by positivity) (by positivity)]
              linarith [hv4_lt_6v3, hv3_pos]
          _ ≤ t := htL
      · rw [show ((0:ℤ):ℝ) + 5/6 = 5/6 from by norm_num, div_div]
        rw [hv3_def] at htR; exact htR
    -- Rule out runner 3 (k=1). Bounds: 7/(6 v_4) ≤ t ≤ 11/(6 v_4).
    have hnot3 : t ∉ unsafeOf speeds ⟨3, by omega⟩ := by
      apply not_mem_unsafeOf_of_in_gap speeds ⟨3, by omega⟩ (hpos _) 1 t
      · rw [show ((1:ℤ):ℝ) + 1/6 = 7/6 from by norm_num, div_div]
        rw [hv4_def] at htL; exact htL
      · rw [show ((1:ℤ):ℝ) + 5/6 = 11/6 from by norm_num, div_div]
        calc t ≤ 5 / (6 * v3) := htR
          _ ≤ 11 / (6 * (speeds ⟨3, by omega⟩ : ℝ)) := by
              rw [← hv4_def, div_le_div_iff₀ (by positivity) (by positivity)]
              linarith [hv4_lt_2v3, hv3_pos, hv4_pos]
    -- So i = 4.
    fin_cases i
    · exact absurd hi_unsafe hnot0
    · exact absurd hi_unsafe hnot1
    · exact absurd hi_unsafe hnot2
    · exact absurd hi_unsafe hnot3
    · exact hi_unsafe
  obtain ⟨j, hj, hjL, hjR⟩ := bhk_case_8_2_1_find_j speeds hmono hpos h82 h_incl
  have hlarge_int : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ) := by
    exact_mod_cast hlarge
  have h821_int : 5 * (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨3, by omega⟩ : ℤ) := by
    exact_mod_cast h821
  exact bhk_case_8_2_1_kernel speeds hpos hlarge_int h821_int j hj hjL hjR

/-- **BHK §8.2.2.** Sub-case of `x_1 ≤ 3` with `x_4 ≤ 5/7` (de-normalised:
    `7 * speeds ⟨2⟩ ≤ 5 * speeds ⟨3⟩`) AND `x_1 ≤ 5 x_4` (de-normalised:
    `speeds ⟨3⟩ ≤ 5 * speeds ⟨0⟩`). See BHK p47–48. -/
theorem bhk_case_8_2_2 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hlarge : speeds ⟨2, by omega⟩ ≤ 3 * speeds ⟨0, by omega⟩)
    (h82 : 7 * speeds ⟨2, by omega⟩ ≤ 5 * speeds ⟨3, by omega⟩)
    (h822 : speeds ⟨3, by omega⟩ ≤ 5 * speeds ⟨0, by omega⟩) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  sorry

/-- **BHK §8.** Case `x_1 ≤ 3` (i.e. `v_3 ≤ 3 v_1`). Dispatcher onto the
    four sub-theorems `bhk_case_8_1_1` / `bhk_case_8_1_2` / `bhk_case_8_2_1`
    / `bhk_case_8_2_2`, partitioning on `x_4 > 5/7 ↔ 5 v_3 < 7 v_2` and
    secondary thresholds. See BHK p45–48. -/
theorem bhk_case_v1_large (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hlarge : speeds ⟨2, by omega⟩ ≤ 3 * speeds ⟨0, by omega⟩) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  by_cases h81 : 5 * speeds ⟨3, by omega⟩ < 7 * speeds ⟨2, by omega⟩
  · by_cases h811 : 13 * speeds ⟨1, by omega⟩ ≤ 7 * speeds ⟨3, by omega⟩
    · exact bhk_case_8_1_1 speeds hmono hpos hgcd hlarge h81 h811
    · push_neg at h811
      exact bhk_case_8_1_2 speeds hmono hpos hgcd hlarge h81 h811
  · push_neg at h81
    -- h81 : 7 * speeds ⟨2⟩ ≤ 5 * speeds ⟨3⟩
    by_cases h821 : 5 * speeds ⟨0, by omega⟩ < speeds ⟨3, by omega⟩
    · exact bhk_case_8_2_1 speeds hmono hpos hgcd hlarge h81 h821
    · push_neg at h821
      exact bhk_case_8_2_2 speeds hmono hpos hgcd hlarge h81 h821

/-- **BHK Theorem 2** (Six Lonely Runners), integer-speed five-mover form.
    Dispatches on the BHK case split:
    * `v_3 ≤ 3 v_1` → §8 (`bhk_case_v1_large`);
    * `3 v_1 < v_3` → §5 / §6 / §7 by zero/nonzero status of `{t_0}` and
      `{v_1 t_0}`. -/
theorem bhk_theorem_2 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  by_cases hlarge : speeds ⟨2, by omega⟩ ≤ 3 * speeds ⟨0, by omega⟩
  · exact bhk_case_v1_large speeds hmono hpos hgcd hlarge
  · push_neg at hlarge
    set t₀ : ℝ := 1 / ((speeds ⟨2, by omega⟩ : ℝ) - speeds ⟨1, by omega⟩) with ht₀_def
    by_cases hv1t0 : Int.fract ((speeds ⟨0, by omega⟩ : ℝ) * t₀) = 0
    · exact bhk_case_v1t0_zero speeds hmono hpos hgcd hlarge hv1t0
    · by_cases ht0 : Int.fract t₀ = 0
      · exact bhk_case_t0_zero speeds hmono hpos hgcd hlarge ht0
      · exact bhk_case_v1_small_generic speeds hmono hpos hgcd hlarge ht0 hv1t0

end BHK

/-- Exported alias: the integer-speed n=6 Hard Case theorem.
    Cited from `IntLRC_6.lean`. -/
theorem intLRC_six_hard (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 :=
  BHK.bhk_theorem_2 speeds hmono hpos hgcd
