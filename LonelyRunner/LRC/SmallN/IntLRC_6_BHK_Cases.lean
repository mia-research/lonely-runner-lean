import LonelyRunner.LRC.SmallN.IntLRC_6_BHK_Lemma4
import LonelyRunner.LRC.SmallN.IntLRC_6_BHK_MainLemma
import LonelyRunner.LRC.SmallN.IntLRC_6_BHK_Section5
import LonelyRunner.LRC.SmallN.IntLRC_6_BHK_Section7

/-!
# BHK §§5–8 — Case branches of the Six Lonely Runners proof

Four case branches dispatched by the main theorem (`bhk_theorem_2`):

* §5: `{v_1 t_0} = 0`                ⟶ `bhk_case_v1t0_zero`
* §6: `{v_3 t_0} = 0`, `{v_1 t_0} ≠ 0` ⟶ `bhk_case_t0_zero`
* §§2+7: both `≠ 0`                  ⟶ `bhk_case_v1_small_generic`
* §8: `x_1 ≤ 3` (i.e. `v_3 ≤ 3 v_1`) ⟶ `bhk_case_v1_large`

where `t_0 := 1 / (v_3 - v_2)` is the elementary period (runner 3 passing
runner 2) and `x_i := 1 / v_i`. BHK's normalised `{t_0}` (runner 3's
position at a meeting time) is `fract (v_3 · t_0)` for integer speeds.

The main theorem dispatches: `v_3 ≤ 3 v_1` → §8; else split on
`{v_3 t_0}`, `{v_1 t_0}` zero/nonzero.

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
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 :=
  bhk_s5_main speeds hmono hpos hgcd hsmall ht0

/-- **BHK §6.** Case `{v_3 t_0} = 0` under "small `v_1`" (`3 v_1 < v_3`).
    Applies the Main Lemma to a specific rectangle constructed from the
    23-gap geometry.

    NOTE on faithfulness: BHK's `{t_0}` is runner 3's position at the
    meeting time `t_0` in their `v_3 = 1` normalisation; with integer
    speeds and `t_0 = 1/(v_3 - v_2)` it is `fract (v_3 · t_0)` — runner 3
    (equivalently runner 2) sits at the origin whenever runners 2 and 3
    meet, i.e. `(v_3 - v_2) ∣ v_3`. The earlier statement used
    `fract t_0 = 0`, which forces `v_3 = v_2 + 1` and made this branch
    unreachable from the dispatcher. -/
theorem bhk_case_t0_zero (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (ht0 : Int.fract ((speeds ⟨2, by omega⟩ : ℝ) *
              (1 / ((speeds ⟨2, by omega⟩ : ℝ) - speeds ⟨1, by omega⟩))) = 0)
    (hv1t0 : Int.fract ((speeds ⟨0, by omega⟩ : ℝ) *
              (1 / ((speeds ⟨2, by omega⟩ : ℝ) - speeds ⟨1, by omega⟩))) ≠ 0) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  sorry

/-- **BHK §§2+7.** Generic case: `3 v_1 < v_3` with both `{v_3 t_0} ≠ 0` and
    `{v_1 t_0} ≠ 0` (the torus subgroup `G = ⟨({v_3 t_0}, {v_1 t_0})⟩` is not
    contained in either axis). Covers BHK §2 (`x_1 ≥ 4`) and §7
    (`3 ≤ x_1 < 4`) together: Corollary 6 applied to the `2/3 × 2/9`
    rectangle `[1/6, 5/6] × [7/18, 11/18] ⊆ P`, plus the exceptional pair
    cases (BHK §2 cases 2.1–2.3, Tables 9 and 10, and the two exceptional
    groups `G_4`, `G_7`).

    NOTE on faithfulness: `{t_0}` here means `fract (v_3 · t_0)` — see the
    docstring of `bhk_case_t0_zero`. -/
theorem bhk_case_v1_small_generic (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (ht0 : Int.fract ((speeds ⟨2, by omega⟩ : ℝ) *
              (1 / ((speeds ⟨2, by omega⟩ : ℝ) - speeds ⟨1, by omega⟩))) ≠ 0)
    (hv1t0 : Int.fract ((speeds ⟨0, by omega⟩ : ℝ) *
              (1 / ((speeds ⟨2, by omega⟩ : ℝ) - speeds ⟨1, by omega⟩))) ≠ 0) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 :=
  bhk_s7_main speeds hmono hpos hgcd hsmall ht0 hv1t0

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

/-- **1234-gap-B inclusion for §8.1 setup (post-(65), used for (68)).** Under
    the §8 + §8.1 setup hypotheses, the interval
    `[max{13/(6 v_4), 7/(6 v_2)}, 11/(6 v_3)]` lies in `unsafeOf ⟨4⟩` (runner 5
    is the unique unsafe runner). This is BHK p46-47.

    Geometry: under `hlarge` + `h81`, runners 1, 2, 3, 4 are each safe on this
    interval:
    * Runner 1 in k=0 gap (needs `11 v_1 < 5 v_3` from `h81 + (65) chain`).
    * Runner 2 in k=1 gap `[7/(6 v_2), 11/(6 v_2)]` (uses `v_2 ≤ v_3`).
    * Runner 3 in k=1 gap `[7/(6 v_3), 11/(6 v_3)]` (uses `h81`).
    * Runner 4 in k=2 gap `[13/(6 v_4), 17/(6 v_4)]` (uses `h81`).

    Note: the interval may be EMPTY (when `11 v_4 < 13 v_3`); the inclusion
    then holds vacuously. Downstream `find_68` handles the empty case
    separately. -/
lemma bhk_8_1_1234_gap_B_incl (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hlarge : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ))
    (h81 : 5 * (speeds ⟨3, by omega⟩ : ℤ) < 7 * (speeds ⟨2, by omega⟩ : ℤ))
    (h65 : 5 * (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ))
    (h5v5_lt_7v4 : 5 * (speeds ⟨4, by omega⟩ : ℤ) < 7 * (speeds ⟨3, by omega⟩ : ℤ))
    (h_no_lonely : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1/6) :
    Set.Icc (max (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
                 (7 / (6 * (speeds ⟨1, by omega⟩ : ℝ))))
            (11 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
    ⊆ unsafeOf speeds ⟨4, by omega⟩ := by
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
    rw [hv1_def, hv2_def]
    exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr (show (0:ℕ) < 1 by omega)))
  have hv2_le_v3 : v2 ≤ v3 := by
    rw [hv2_def, hv3_def]
    exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr (show (1:ℕ) < 2 by omega)))
  have hv3_le_v4 : v3 ≤ v4 := by
    rw [hv3_def, hv4_def]
    exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr (show (2:ℕ) < 3 by omega)))
  -- Cast hypotheses to ℝ
  have hlarge_R : v3 ≤ 3 * v1 := by rw [hv3_def, hv1_def]; exact_mod_cast hlarge
  have h81_R : 5 * v4 < 7 * v3 := by rw [hv4_def, hv3_def]; exact_mod_cast h81
  have h65_R : 5 * v1 < v5 := by rw [hv1_def, hv5_def]; exact_mod_cast h65
  have h5v5_lt_7v4_R : 5 * v5 < 7 * v4 := by
    rw [hv5_def, hv4_def]; exact_mod_cast h5v5_lt_7v4
  intro t ht
  obtain ⟨htL, htR⟩ := ht
  have htL4 : 13 / (6 * v4) ≤ t := le_trans (le_max_left _ _) htL
  have htL2 : 7 / (6 * v2) ≤ t := le_trans (le_max_right _ _) htL
  obtain ⟨i, hi_unsafe⟩ := h_no_lonely t
  rw [← mem_unsafeOf_iff] at hi_unsafe
  -- Runner 1 (speeds ⟨0⟩): k=0 gap [1/(6 v_1), 5/(6 v_1)].
  have hnot0 : t ∉ unsafeOf speeds ⟨0, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨0, by omega⟩ (hpos _) 0 t
    · rw [show ((0:ℤ):ℝ) + 1/6 = 1/6 from by norm_num, div_div]
      -- 1/(6 v_1) ≤ 7/(6 v_2) (uses v_2 ≤ v_3 ≤ 3 v_1, so v_2 ≤ 3 v_1 < 7 v_1).
      have hbound : 1 / (6 * v1) ≤ 7 / (6 * v2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hv2_le_v3, hlarge_R, hv1_pos]
      linarith [htL2, hbound]
    · rw [show ((0:ℤ):ℝ) + 5/6 = 5/6 from by norm_num, div_div]
      -- t ≤ 11/(6 v_3) ≤ 5/(6 v_1) ⟺ 11 v_1 ≤ 5 v_3.
      -- From h65 (5 v_1 < v_5), h5v5_lt_7v4 (5 v_5 < 7 v_4), h81 (5 v_4 < 7 v_3):
      -- 25 v_1 < 5 v_5 < 7 v_4 ⟹ 125 v_1 < 35 v_4 < 49 v_3 ⟹ 11 v_1 ≤ 49 v_1/... hmm
      -- Better: 25 v_1 < 7 v_4 (chain); 5 v_4 < 7 v_3 (h81). So 25 v_1 < 7 v_4 and
      -- 5 v_4 < 7 v_3 ⟹ 125 v_1 < 35 v_4 < 49 v_3 ⟹ 125 v_1 < 49 v_3.
      -- Then 11·49 v_1 = 539 v_1 < 11·49/125 · 125 v_1 ... want 11 v_1 ≤ 5 v_3.
      -- 11 v_1 ≤ 5 v_3 ⟺ 11·49 v_1 ≤ 49·5 v_3 = 245 v_3. 11·49 = 539 v_1.
      -- And 125 v_1 < 49 v_3 ⟹ v_1 < 49 v_3/125 ⟹ 539 v_1 < 539·49 v_3/125 ≈ 211 v_3 < 245 v_3 ✓.
      have hbound : 11 / (6 * v3) ≤ 5 / (6 * v1) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h65_R, h5v5_lt_7v4_R, h81_R, hv1_pos, hv3_pos, hv4_pos, hv5_pos]
      linarith [htR, hbound]
  -- Runner 2 (speeds ⟨1⟩): k=1 gap [7/(6 v_2), 11/(6 v_2)].
  have hnot1 : t ∉ unsafeOf speeds ⟨1, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨1, by omega⟩ (hpos _) 1 t
    · rw [show ((1:ℤ):ℝ) + 1/6 = 7/6 from by norm_num, div_div]
      exact htL2
    · rw [show ((1:ℤ):ℝ) + 5/6 = 11/6 from by norm_num, div_div]
      -- t ≤ 11/(6 v_3) ≤ 11/(6 v_2) (v_2 ≤ v_3)
      have hbound : 11 / (6 * v3) ≤ 11 / (6 * v2) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        nlinarith [hv2_le_v3, hv2_pos]
      linarith [htR, hbound]
  -- Runner 3 (speeds ⟨2⟩): k=1 gap [7/(6 v_3), 11/(6 v_3)].
  have hnot2 : t ∉ unsafeOf speeds ⟨2, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨2, by omega⟩ (hpos _) 1 t
    · rw [show ((1:ℤ):ℝ) + 1/6 = 7/6 from by norm_num, div_div]
      -- 7/(6 v_3) ≤ max{13/(6 v_4), 7/(6 v_2)} ≤ t.
      -- 13/(6 v_4) ≥ 7/(6 v_3) ⟺ 13 v_3 ≥ 7 v_4. From h81 5 v_4 < 7 v_3 ⟹ 7 v_4 < 49 v_3/5 < 13 v_3 ✓.
      have hbound : 7 / (6 * v3) ≤ 13 / (6 * v4) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h81_R, hv3_pos, hv4_pos]
      linarith [htL4, hbound]
    · rw [show ((1:ℤ):ℝ) + 5/6 = 11/6 from by norm_num, div_div]
      exact htR
  -- Runner 4 (speeds ⟨3⟩): k=2 gap [13/(6 v_4), 17/(6 v_4)].
  have hnot3 : t ∉ unsafeOf speeds ⟨3, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨3, by omega⟩ (hpos _) 2 t
    · rw [show ((2:ℤ):ℝ) + 1/6 = 13/6 from by norm_num, div_div]
      exact htL4
    · rw [show ((2:ℤ):ℝ) + 5/6 = 17/6 from by norm_num, div_div]
      -- t ≤ 11/(6 v_3) ≤ 17/(6 v_4) ⟺ 11 v_4 ≤ 17 v_3. From h81: 11 v_4 < 77 v_3/5 < 17 v_3 ✓.
      have hbound : 11 / (6 * v3) ≤ 17 / (6 * v4) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h81_R, hv3_pos, hv4_pos]
      linarith [htR, hbound]
  fin_cases i
  · exact absurd hi_unsafe hnot0
  · exact absurd hi_unsafe hnot1
  · exact absurd hi_unsafe hnot2
  · exact absurd hi_unsafe hnot3
  · exact hi_unsafe

set_option maxHeartbeats 1200000 in
/-- **§8.1 step 3 derivation of BHK (68) from 1234-gap-B inclusion.** From the
    inclusion `[max{13/(6 v_4), 7/(6 v_2)}, 11/(6 v_3)] ⊆ unsafeOf ⟨4⟩` (runner
    5 is the unique unsafe runner), together with (65), (66), (67), derive
    BHK's (68):

    * **(68)** `11 v_5 < 19 v_3`   (equivalent to BHK's `11 < 19 x_5`)

    Strategy: case split on whether the interval is empty.

    * **Empty case** `11 v_4 < 13 v_3`: direct from `h5v5_lt_7v4` chain:
      `55 v_5 < 77 v_4 < 91 v_3 < 95 v_3 = 19·5 v_3 ⟹ 11 v_5 < 19 v_3`.
    * **Non-empty case** `13 v_3 ≤ 11 v_4`: `block_containment` for runner 5
      gives integer `k` with `(6k-1)/6 < v_5 · max` and `v_5 · 11/(6 v_3)
      < (6k+1)/6`. Force `k = 3`:
      * `k ≥ 3`: if `k ≤ 2`, then `11 v_5 < 13 v_3 ≤ 39 v_1` (hlarge) and
        `11 v_5 > 55 v_1` (h65) give `55 v_1 < 39 v_1`, false.
      * `k ≤ 3`: if `k ≥ 4`, `23 < max{13 v_5/v_4, 7 v_5/v_2}`. Case 1 is
        impossible (h5v5_lt_7v4: `v_5 < 1.4 v_4 < 23 v_4/13`). Case 2:
        `7 v_5 > 23 v_2 ≥ 23·25 v_1/13 = 575 v_1/13 > 41.16 v_1` —
        but `7 v_5 < 49 v_3/5 ≤ 49·3 v_1/5 = 29.4 v_1 < 41.16 v_1`, false. -/
lemma bhk_8_1_step3_find_68 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hlarge : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ))
    (h81 : 5 * (speeds ⟨3, by omega⟩ : ℤ) < 7 * (speeds ⟨2, by omega⟩ : ℤ))
    (h65 : 5 * (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ))
    (h5v5_lt_7v4 : 5 * (speeds ⟨4, by omega⟩ : ℤ) < 7 * (speeds ⟨3, by omega⟩ : ℤ))
    (h66 : 25 * (speeds ⟨2, by omega⟩ : ℤ) < 39 * (speeds ⟨1, by omega⟩ : ℤ))
    (h67 : 11 * (speeds ⟨1, by omega⟩ : ℤ) < 7 * (speeds ⟨3, by omega⟩ : ℤ))
    (h_incl : Set.Icc (max (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
                            (7 / (6 * (speeds ⟨1, by omega⟩ : ℝ))))
                       (11 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
              ⊆ unsafeOf speeds ⟨4, by omega⟩) :
    11 * (speeds ⟨4, by omega⟩ : ℤ) < 19 * (speeds ⟨2, by omega⟩ : ℤ) := by
  by_cases h_empty : 11 * (speeds ⟨3, by omega⟩ : ℤ) < 13 * (speeds ⟨2, by omega⟩ : ℤ)
  · -- Empty case: 11 v_4 < 13 v_3. (68) follows from h5v5_lt_7v4 + h_empty.
    linarith [h5v5_lt_7v4, h_empty]
  · push_neg at h_empty -- 13 v_3 ≤ 11 v_4
    have hv1_int : (0 : ℤ) < (speeds ⟨0, by omega⟩ : ℤ) := by exact_mod_cast hpos _
    have hv2_int : (0 : ℤ) < (speeds ⟨1, by omega⟩ : ℤ) := by exact_mod_cast hpos _
    have hv3_int : (0 : ℤ) < (speeds ⟨2, by omega⟩ : ℤ) := by exact_mod_cast hpos _
    have hv4_int : (0 : ℤ) < (speeds ⟨3, by omega⟩ : ℤ) := by exact_mod_cast hpos _
    have hv5_int : (0 : ℤ) < (speeds ⟨4, by omega⟩ : ℤ) := by exact_mod_cast hpos _
    have hv1_pos_R : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hv1_int
    have hv2_pos_R : (0 : ℝ) < (speeds ⟨1, by omega⟩ : ℝ) := by exact_mod_cast hv2_int
    have hv3_pos_R : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hv3_int
    have hv4_pos_R : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hv4_int
    have hv5_pos_R : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hv5_int
    have h_empty_R : 13 * (speeds ⟨2, by omega⟩ : ℝ) ≤ 11 * (speeds ⟨3, by omega⟩ : ℝ) := by
      exact_mod_cast h_empty
    have h66_R : 25 * (speeds ⟨2, by omega⟩ : ℝ) < 39 * (speeds ⟨1, by omega⟩ : ℝ) := by
      exact_mod_cast h66
    have h67_R : 11 * (speeds ⟨1, by omega⟩ : ℝ) < 7 * (speeds ⟨3, by omega⟩ : ℝ) := by
      exact_mod_cast h67
    have h65_R : 5 * (speeds ⟨0, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
      exact_mod_cast h65
    have h5v5_lt_7v4_R : 5 * (speeds ⟨4, by omega⟩ : ℝ) < 7 * (speeds ⟨3, by omega⟩ : ℝ) := by
      exact_mod_cast h5v5_lt_7v4
    have hlarge_R : (speeds ⟨2, by omega⟩ : ℝ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℝ) := by
      exact_mod_cast hlarge
    have h81_R : 5 * (speeds ⟨3, by omega⟩ : ℝ) < 7 * (speeds ⟨2, by omega⟩ : ℝ) := by
      exact_mod_cast h81
    -- Non-emptiness: max ≤ 11/(6 v_3).
    have hab1 : 13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)) ≤
                11 / (6 * (speeds ⟨2, by omega⟩ : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h_empty_R, hv2_pos_R, hv3_pos_R]
    have hab2 : 7 / (6 * (speeds ⟨1, by omega⟩ : ℝ)) ≤
                11 / (6 * (speeds ⟨2, by omega⟩ : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h66_R, hv1_pos_R, hv2_pos_R]
    have hab : max (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
                   (7 / (6 * (speeds ⟨1, by omega⟩ : ℝ))) ≤
               11 / (6 * (speeds ⟨2, by omega⟩ : ℝ)) := max_le hab1 hab2
    -- block_containment on runner 5 (= speeds ⟨4⟩).
    obtain ⟨k, hk_lo, hk_hi⟩ :=
      block_containment speeds ⟨4, by omega⟩ (hpos _) _ _ hab h_incl
    -- Convert hk_hi: 11 v_5 < (6k+1) v_3.
    have h6v3R : (0 : ℝ) < 6 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
    have hk_hi' : 11 * (speeds ⟨4, by omega⟩ : ℝ) <
                  (6 * (k : ℝ) + 1) * (speeds ⟨2, by omega⟩ : ℝ) := by
      have hmul := mul_lt_mul_of_pos_right hk_hi h6v3R
      have hclear : ((speeds ⟨4, by omega⟩ : ℝ) * (11 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))) *
                    (6 * (speeds ⟨2, by omega⟩ : ℝ)) =
                    11 * (speeds ⟨4, by omega⟩ : ℝ) := by field_simp
      nlinarith [hmul, hclear]
    have hk_hi_int : 11 * (speeds ⟨4, by omega⟩ : ℤ) <
                     (6 * k + 1) * (speeds ⟨2, by omega⟩ : ℤ) := by exact_mod_cast hk_hi'
    -- Force k ≥ 3: if k ≤ 2, 11 v_5 < 13 v_3 ≤ 39 v_1 (hlarge); h65 ⟹ 55 v_1 < 11 v_5;
    -- so 55 v_1 < 39 v_1, false.
    have hk_ge_3 : 3 ≤ k := by
      by_contra hk_lt
      push_neg at hk_lt
      have hk_le_2 : k ≤ 2 := by omega
      have h6kp1_le : 6 * k + 1 ≤ 13 := by linarith
      have h11v5_lt_13v3 : 11 * (speeds ⟨4, by omega⟩ : ℤ) <
                            13 * (speeds ⟨2, by omega⟩ : ℤ) := by
        calc 11 * (speeds ⟨4, by omega⟩ : ℤ)
            < (6 * k + 1) * (speeds ⟨2, by omega⟩ : ℤ) := hk_hi_int
          _ ≤ 13 * (speeds ⟨2, by omega⟩ : ℤ) := by
              apply mul_le_mul_of_nonneg_right h6kp1_le (le_of_lt hv3_int)
      linarith [h65, hlarge, h11v5_lt_13v3, hv1_int]
    -- Force k ≤ 3: if k ≥ 4, lower bound forces max{13 v_5/v_4, 7 v_5/v_2} > 23.
    -- Case 1: 23 v_4 < 13 v_5; combined with 5 v_5 < 7 v_4: 23 v_4 < 13 v_5 < 91 v_4/5,
    -- so 23·5 = 115 < 91, false.
    -- Case 2: 23 v_2 < 7 v_5. From h66 + hlarge: 25 v_3 < 39 v_2 ⟹ v_2 > 25 v_3/39;
    -- so 23 v_2 > 23·25 v_3/39 = 575 v_3/39 (rough). And 7 v_5 < 49 v_3/5 (h5v5_lt_7v4).
    -- Need: 575 v_3/39 ≥ 49 v_3/5? 575·5 = 2875, 49·39 = 1911. So 575/39 > 49/5 ⟹
    -- 23 v_2 > 49 v_3/5 > 7 v_5 (chain), so 23 v_2 > 7 v_5 contradicts 23 v_2 < 7 v_5.
    have hk_le_3 : k ≤ 3 := by
      by_contra hk_gt
      push_neg at hk_gt
      have hk_ge_4 : 4 ≤ k := hk_gt
      -- 23 < v_5 · max{13/v_4, 7/v_2}.
      have h23_lt : (23 : ℝ) < 6 * ((speeds ⟨4, by omega⟩ : ℝ) *
                     max (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
                         (7 / (6 * (speeds ⟨1, by omega⟩ : ℝ)))) := by
        have h6mul : 6 * ((k : ℝ) - 1/6) < 6 *
                     ((speeds ⟨4, by omega⟩ : ℝ) *
                       max (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
                           (7 / (6 * (speeds ⟨1, by omega⟩ : ℝ)))) :=
          mul_lt_mul_of_pos_left hk_lo (by norm_num)
        have h6km1_simp : 6 * ((k : ℝ) - 1/6) = 6 * (k : ℝ) - 1 := by ring
        rw [h6km1_simp] at h6mul
        have h6km1_ge : (23 : ℝ) ≤ 6 * (k : ℝ) - 1 := by
          exact_mod_cast (by linarith : (23 : ℤ) ≤ 6 * k - 1)
        linarith
      have hmax_eq : 6 * ((speeds ⟨4, by omega⟩ : ℝ) *
                   max (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
                       (7 / (6 * (speeds ⟨1, by omega⟩ : ℝ)))) =
                   max (13 * (speeds ⟨4, by omega⟩ : ℝ) / (speeds ⟨3, by omega⟩ : ℝ))
                       (7 * (speeds ⟨4, by omega⟩ : ℝ) / (speeds ⟨1, by omega⟩ : ℝ)) := by
        rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ (speeds ⟨4, by omega⟩ : ℝ))]
        rw [mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 6)]
        congr 1
        · field_simp
        · field_simp
      rw [hmax_eq] at h23_lt
      rcases lt_max_iff.mp h23_lt with hcase1 | hcase2
      · -- 23 < 13 v_5/v_4 ⟹ 23 v_4 < 13 v_5. Combined with 5 v_5 < 7 v_4:
        -- 23 v_4 < 13 v_5 ⟹ 115 v_4 < 65 v_5 ⟹ 115 v_4 < 65 · 7 v_4/5 = 91 v_4. So 115 < 91, FALSE.
        have h23v4_lt_13v5 : 23 * (speeds ⟨3, by omega⟩ : ℝ) <
                              13 * (speeds ⟨4, by omega⟩ : ℝ) := by
          rw [lt_div_iff₀ hv4_pos_R] at hcase1; linarith
        nlinarith [h23v4_lt_13v5, h5v5_lt_7v4_R, hv4_pos_R, hv5_pos_R]
      · -- 23 < 7 v_5/v_2 ⟹ 23 v_2 < 7 v_5. From (66) + hlarge: 25 v_3 < 39 v_2 and v_3 ≤ 3 v_1
        -- ⟹ 25·3 v_1 ≥ 25 v_3 — wait: 25 v_3 < 39 v_2 ⟹ v_2 > 25 v_3/39. Combined with
        -- v_3 ≤ 3 v_1 ⟹ v_2 > 25·v_3/39 (no immediate v_1 bound). But from (66): 39 v_2 > 25 v_3;
        -- multiply 7 v_5 < 7 v_4·7/5 = 49 v_4/5 ... use h5v5_lt_7v4 directly: 7 v_5 < 49 v_3/5.
        -- We need: 23 v_2 > 49 v_3/5. From (66) 39 v_2 > 25 v_3 ⟹ 195 v_2 > 125 v_3.
        -- 23 v_2 ≥ 49 v_3/5 ⟺ 115 v_2 ≥ 49 v_3 ⟺ 195 v_2 ≥ 195·49/115 v_3 = 9555/115 v_3 ≈ 83 v_3.
        -- 195 v_2 > 125 v_3 ≥ 83 v_3 (since 125 > 83). ✓
        -- So 23 v_2 > 49 v_3/5 (from (66)) > 7 v_5 (from h5v5_lt_7v4×7/5).
        have h23v2_lt_7v5 : 23 * (speeds ⟨1, by omega⟩ : ℝ) <
                             7 * (speeds ⟨4, by omega⟩ : ℝ) := by
          rw [lt_div_iff₀ hv2_pos_R] at hcase2; linarith
        -- 23 v_2 < 7 v_5; want contradiction.
        -- 5 v_5 < 7 v_4 ⟹ 25 v_5 < 35 v_4.
        -- 5 v_4 < 7 v_3 ⟹ 25 v_4 < 35 v_3, hence 35 v_4 < 49 v_3 ⟹ 25 v_5 < 49 v_3.
        -- So 7 v_5 = (7/25) · 25 v_5 < (7/25) · 49 v_3 = 343 v_3/25.
        -- 23 v_2 > (23·25/39) v_3 = 575 v_3/39 (from (66)).
        -- Need 575/39 > 343/25? 575·25 = 14375, 343·39 = 13377. 14375 > 13377 ✓.
        -- So 23 v_2 > 575 v_3/39 > 343 v_3/25 > 7 v_5, contradicting 23 v_2 < 7 v_5.
        nlinarith [h23v2_lt_7v5, h66_R, h5v5_lt_7v4_R, h81_R,
                   hv2_pos_R, hv3_pos_R, hv4_pos_R, hv5_pos_R]
    have hk_eq_3 : k = 3 := le_antisymm hk_le_3 hk_ge_3
    subst hk_eq_3
    -- Substitute k = 3: 11 v_5 < (6·3 + 1) v_3 = 19 v_3.
    linarith [hk_hi_int]

/-- **§8.1.1 left sub-interval inclusion.** The interval
    `[13/(6 v_3), 23/(6 v_5)]` (left piece of the 123-gap, before runner 5's
    k=4 unsafe block) is contained in `unsafeOf ⟨3⟩` (runner 4 must be unsafe).

    Geometry: runners 1, 2, 3, 5 safe on the interval (runner 1 in k=0,
    runner 2 in k=1, runner 3 in k=2, runner 5 in k=3 safe gaps). Bounds:
    * Runner 1: hlarge + h65 (5 v_1 + 1 ≤ v_5 forces 23 v_1 < 5 v_5).
    * Runner 2: (66) gives 7 v_3 < 13 v_2; h65 + mono gives 11 v_5 > 23 v_2.
    * Runner 3: needs 17 v_5 ≥ 23 v_3, from h65 + hlarge chain
      (5 v_5 > 25 v_1 ≥ 25 v_3/3).
    * Runner 5: needs 19 v_3 ≤ 13 v_5, also from same chain. -/
lemma bhk_8_1_1_left_sub_incl (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hlarge : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ))
    (h81 : 5 * (speeds ⟨3, by omega⟩ : ℤ) < 7 * (speeds ⟨2, by omega⟩ : ℤ))
    (h811 : 13 * (speeds ⟨1, by omega⟩ : ℤ) ≤ 7 * (speeds ⟨3, by omega⟩ : ℤ))
    (h65 : 5 * (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ))
    (h5v5_lt_7v4 : 5 * (speeds ⟨4, by omega⟩ : ℤ) < 7 * (speeds ⟨3, by omega⟩ : ℤ))
    (h66 : 25 * (speeds ⟨2, by omega⟩ : ℤ) < 39 * (speeds ⟨1, by omega⟩ : ℤ))
    (h_no_lonely : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1/6) :
    Set.Icc (13 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
            (23 / (6 * (speeds ⟨4, by omega⟩ : ℝ)))
    ⊆ unsafeOf speeds ⟨3, by omega⟩ := by
  set v1 : ℝ := (speeds ⟨0, by omega⟩ : ℝ) with hv1_def
  set v2 : ℝ := (speeds ⟨1, by omega⟩ : ℝ) with hv2_def
  set v3 : ℝ := (speeds ⟨2, by omega⟩ : ℝ) with hv3_def
  set v5 : ℝ := (speeds ⟨4, by omega⟩ : ℝ) with hv5_def
  have hv1_pos : 0 < v1 := by rw [hv1_def]; exact_mod_cast hpos _
  have hv2_pos : 0 < v2 := by rw [hv2_def]; exact_mod_cast hpos _
  have hv3_pos : 0 < v3 := by rw [hv3_def]; exact_mod_cast hpos _
  have hv5_pos : 0 < v5 := by rw [hv5_def]; exact_mod_cast hpos _
  have hv1_lt_v2 : v1 < v2 := by
    rw [hv1_def, hv2_def]
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (0:ℕ) < 1 by omega))
  have hv1_le_v3 : v1 ≤ v3 := by
    rw [hv1_def, hv3_def]
    exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr (show (0:ℕ) < 2 by omega)))
  have hv2_le_v3 : v2 ≤ v3 := by
    rw [hv2_def, hv3_def]
    exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr (show (1:ℕ) < 2 by omega)))
  have hlarge_R : v3 ≤ 3 * v1 := by rw [hv3_def, hv1_def]; exact_mod_cast hlarge
  have h65_R : 5 * v1 < v5 := by rw [hv1_def, hv5_def]; exact_mod_cast h65
  have h66_R : 25 * v3 < 39 * v2 := by rw [hv3_def, hv2_def]; exact_mod_cast h66
  have h81_R : 5 * (speeds ⟨3, by omega⟩ : ℝ) < 7 * v3 := by
    rw [hv3_def]; exact_mod_cast h81
  have h811_R : 13 * v2 ≤ 7 * (speeds ⟨3, by omega⟩ : ℝ) := by
    rw [hv2_def]; exact_mod_cast h811
  have h5v5_lt_7v4_R : 5 * v5 < 7 * (speeds ⟨3, by omega⟩ : ℝ) := by
    rw [hv5_def]; exact_mod_cast h5v5_lt_7v4
  -- Integer constraints (for tight bounds via 5 v_1 + 1 ≤ v_5, v_1 + 1 ≤ v_2).
  have h65_int : 5 * (speeds ⟨0, by omega⟩ : ℤ) + 1 ≤ (speeds ⟨4, by omega⟩ : ℤ) := by
    linarith
  have hv1_v2_int : (speeds ⟨0, by omega⟩ : ℤ) + 1 ≤ (speeds ⟨1, by omega⟩ : ℤ) := by
    have : (speeds ⟨0, by omega⟩ : ℕ) < speeds ⟨1, by omega⟩ :=
      hmono (Fin.mk_lt_mk.mpr (show (0:ℕ) < 1 by omega))
    exact_mod_cast this
  have h5v1p1_le_v5_R : 5 * v1 + 1 ≤ v5 := by
    rw [hv1_def, hv5_def]; exact_mod_cast h65_int
  have hv1p1_le_v2_R : v1 + 1 ≤ v2 := by
    rw [hv1_def, hv2_def]; exact_mod_cast hv1_v2_int
  -- v_1 ≥ 1 from positive integer
  have hv1_ge_1 : (1 : ℝ) ≤ v1 := by
    have : 1 ≤ speeds ⟨0, by omega⟩ := hpos _
    rw [hv1_def]; exact_mod_cast this
  intro t ht
  obtain ⟨htL, htR⟩ := ht
  obtain ⟨i, hi_unsafe⟩ := h_no_lonely t
  rw [← mem_unsafeOf_iff] at hi_unsafe
  -- Runner 1: k=0 gap [1/(6 v_1), 5/(6 v_1)].
  have hnot0 : t ∉ unsafeOf speeds ⟨0, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨0, by omega⟩ (hpos _) 0 t
    · rw [show ((0:ℤ):ℝ) + 1/6 = 1/6 from by norm_num, div_div]
      -- 1/(6 v_1) ≤ 13/(6 v_3): need v_3 ≤ 13 v_1, follows from hlarge ≤ 3 v_1 < 13 v_1.
      have hbound : 1 / (6 * v1) ≤ 13 / (6 * v3) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hlarge_R, hv1_pos]
      linarith [htL, hbound]
    · rw [show ((0:ℤ):ℝ) + 5/6 = 5/6 from by norm_num, div_div]
      -- 23/(6 v_5) ≤ 5/(6 v_1): need 23 v_1 ≤ 5 v_5, from 5 v_1 + 1 ≤ v_5 ⟹ 25 v_1 + 5 ≤ 5 v_5.
      have hbound : 23 / (6 * v5) ≤ 5 / (6 * v1) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h5v1p1_le_v5_R, hv1_pos, hv5_pos]
      linarith [htR, hbound]
  -- Runner 2: k=1 gap [7/(6 v_2), 11/(6 v_2)].
  have hnot1 : t ∉ unsafeOf speeds ⟨1, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨1, by omega⟩ (hpos _) 1 t
    · rw [show ((1:ℤ):ℝ) + 1/6 = 7/6 from by norm_num, div_div]
      -- 7/(6 v_2) ≤ 13/(6 v_3): need 7 v_3 ≤ 13 v_2. From (66) 25 v_3 < 39 v_2: 175 v_3 < 273 v_2 < 325 v_2 ⟹ 7 v_3 < 13 v_2.
      have hbound : 7 / (6 * v2) ≤ 13 / (6 * v3) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h66_R, hv2_pos, hv3_pos]
      linarith [htL, hbound]
    · rw [show ((1:ℤ):ℝ) + 5/6 = 11/6 from by norm_num, div_div]
      -- 23/(6 v_5) ≤ 11/(6 v_2): need 23 v_2 ≤ 11 v_5.
      -- From 5 v_1 + 1 ≤ v_5 and v_1 + 1 ≤ v_2:
      --   v_1 ≤ v_2 - 1, so v_5 ≥ 5 v_1 + 1 ≥ 5(v_2 - 1) + 1 = 5 v_2 - 4.
      --   11 v_5 ≥ 55 v_2 - 44 ≥ 23 v_2 (when 32 v_2 ≥ 44 ⟺ v_2 ≥ 2 ✓ from v_1 ≥ 1).
      have hbound : 23 / (6 * v5) ≤ 11 / (6 * v2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        -- Goal: 138 v_2 ≤ 66 v_5 (i.e., 23 v_2 ≤ 11 v_5).
        -- Chain: h_811 (13 v_2 ≤ 7 v_4) + h81 (5 v_4 < 7 v_3) gives 65 v_2 < 49 v_3.
        -- hlarge (v_3 ≤ 3 v_1) + h65 (5 v_1 + 1 ≤ v_5) gives 3 v_5 ≥ 5 v_3 + 3.
        -- Multiply: 1617 v_5 ≥ 3575 v_2 + something > 3381 v_2 ⟹ 11 v_5 > 23 v_2.
        nlinarith [h811_R, h81_R, hlarge_R, h5v1p1_le_v5_R, hv1_ge_1,
                   hv1_pos, hv2_pos, hv5_pos]
      linarith [htR, hbound]
  -- Runner 3: k=2 gap [13/(6 v_3), 17/(6 v_3)].
  have hnot2 : t ∉ unsafeOf speeds ⟨2, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨2, by omega⟩ (hpos _) 2 t
    · rw [show ((2:ℤ):ℝ) + 1/6 = 13/6 from by norm_num, div_div]
      exact htL
    · rw [show ((2:ℤ):ℝ) + 5/6 = 17/6 from by norm_num, div_div]
      -- 23/(6 v_5) ≤ 17/(6 v_3): need 23 v_3 ≤ 17 v_5.
      -- From h65: 5 v_5 > 25 v_1 ≥ 25 v_3/3 (hlarge) ⟹ 15 v_5 > 25 v_3 ⟹
      -- 17 v_5 > 25·17/15 v_3 = 28.33 v_3 > 23 v_3. Multiply by 3:
      -- 51 v_5 > 25·17 v_3/... Actually: 5 v_5 > 25 v_1 ⟹ v_5 > 5 v_1 ⟹ 3 v_5 > 15 v_1 ≥ 5 v_3.
      -- So 3 v_5 > 5 v_3 (with strict via integer +1). Multiply by 17: 51 v_5 > 85 v_3 ≥ 69 v_3.
      have hbound : 23 / (6 * v5) ≤ 17 / (6 * v3) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h65_R, hlarge_R, hv1_pos, hv3_pos, hv5_pos]
      linarith [htR, hbound]
  -- Runner 5: k=3 gap [19/(6 v_5), 23/(6 v_5)].
  have hnot4 : t ∉ unsafeOf speeds ⟨4, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨4, by omega⟩ (hpos _) 3 t
    · rw [show ((3:ℤ):ℝ) + 1/6 = 19/6 from by norm_num, div_div]
      -- 19/(6 v_5) ≤ 13/(6 v_3): need 19 v_3 ≤ 13 v_5.
      -- From h65 + hlarge: 5 v_5 > 25 v_1 ≥ 25 v_3/3 ⟹ 15 v_5 > 25 v_3.
      -- 39 v_5 > 65 v_3 ≥ 57 v_3 ⟹ 13 v_5 > 65 v_3/3 ≈ 21.67 v_3 ≥ 19 v_3.
      have hbound : 19 / (6 * v5) ≤ 13 / (6 * v3) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h65_R, hlarge_R, hv1_pos, hv3_pos, hv5_pos]
      linarith [htL, hbound]
    · rw [show ((3:ℤ):ℝ) + 5/6 = 23/6 from by norm_num, div_div]
      exact htR
  fin_cases i
  · exact absurd hi_unsafe hnot0
  · exact absurd hi_unsafe hnot1
  · exact absurd hi_unsafe hnot2
  · exact hi_unsafe
  · exact absurd hi_unsafe hnot4

set_option maxHeartbeats 1200000 in
/-- **§8.1.1 derivation of BHK (69) `17 v_2 < 7 v_5` from 1234-gap-B + h811.**

    Mirrors `bhk_8_1_step3_find_68` but concludes (69) instead of (68b).
    (69) is the §8.1.1-specific lower bound from BHK p46: under h811's
    `13 v_2 ≤ 7 v_4`, the (68) LHS disjunction
    `17 v_4 < 13 v_5 ∨ 17 v_2 < 7 v_5` always entails (69).

    Strategy:

    * **Empty case** `11 v_4 < 13 v_3`: direct chain `h_empty + h811 + h65 +
      hlarge ⟹ 17 v_2 < 7 v_5` via 187 v_2 < 133 v_3 (from h811 + h_empty)
      and 3 v_5 > 5 v_3 (from h65 + hlarge): yields 5005·17 v_2 < 4641·7 v_5.

    * **Non-empty case** `13 v_3 ≤ 11 v_4`: block_containment on runner 5
      forces k = 3 (same as `find_68`). At k = 3, the lower bound is
      `17 v_4 < 13 v_5 ∨ 17 v_2 < 7 v_5`. Dispatch on h811:
      - Case A `17 v_4 < 13 v_5`: combined with h811 `13 v_2 ≤ 7 v_4`,
        221 v_2 ≤ 119 v_4 < 119·13/17 v_5 = 91 v_5 ⟹ 17 v_2 < 7 v_5.
      - Case B `17 v_2 < 7 v_5`: direct. -/
lemma bhk_8_1_1_find_69 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hlarge : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ))
    (h81 : 5 * (speeds ⟨3, by omega⟩ : ℤ) < 7 * (speeds ⟨2, by omega⟩ : ℤ))
    (h65 : 5 * (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ))
    (h5v5_lt_7v4 : 5 * (speeds ⟨4, by omega⟩ : ℤ) < 7 * (speeds ⟨3, by omega⟩ : ℤ))
    (h66 : 25 * (speeds ⟨2, by omega⟩ : ℤ) < 39 * (speeds ⟨1, by omega⟩ : ℤ))
    (h67 : 11 * (speeds ⟨1, by omega⟩ : ℤ) < 7 * (speeds ⟨3, by omega⟩ : ℤ))
    (h811 : 13 * (speeds ⟨1, by omega⟩ : ℤ) ≤ 7 * (speeds ⟨3, by omega⟩ : ℤ))
    (h_incl : Set.Icc (max (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
                            (7 / (6 * (speeds ⟨1, by omega⟩ : ℝ))))
                       (11 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
              ⊆ unsafeOf speeds ⟨4, by omega⟩) :
    17 * (speeds ⟨1, by omega⟩ : ℤ) < 7 * (speeds ⟨4, by omega⟩ : ℤ) := by
  have hv1_int : (0 : ℤ) < (speeds ⟨0, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  have hv2_int : (0 : ℤ) < (speeds ⟨1, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  have hv3_int : (0 : ℤ) < (speeds ⟨2, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  have hv4_int : (0 : ℤ) < (speeds ⟨3, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  have hv5_int : (0 : ℤ) < (speeds ⟨4, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  by_cases h_empty : 11 * (speeds ⟨3, by omega⟩ : ℤ) < 13 * (speeds ⟨2, by omega⟩ : ℤ)
  · -- Empty case: 11 v_4 < 13 v_3 ⟹ (with h811) 11·13 v_2 ≤ 7·11 v_4 < 7·13 v_3 ⟹ 11 v_2 < 7 v_3
    -- (factoring 13). Combined with 5 v_3 ≤ 15 v_1 < 3 v_5 (h65 + hlarge): 7·5·11 v_2 < 7·5·7 v_3
    -- = 245 v_3 (loose) — actually nlinarith does the polynomial dance directly.
    nlinarith [h_empty, h811, h65, hlarge, hv1_int, hv2_int, hv3_int, hv4_int, hv5_int]
  · push_neg at h_empty -- 13 v_3 ≤ 11 v_4
    have hv1_pos_R : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hv1_int
    have hv2_pos_R : (0 : ℝ) < (speeds ⟨1, by omega⟩ : ℝ) := by exact_mod_cast hv2_int
    have hv3_pos_R : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hv3_int
    have hv4_pos_R : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hv4_int
    have hv5_pos_R : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hv5_int
    have h_empty_R : 13 * (speeds ⟨2, by omega⟩ : ℝ) ≤ 11 * (speeds ⟨3, by omega⟩ : ℝ) := by
      exact_mod_cast h_empty
    have h66_R : 25 * (speeds ⟨2, by omega⟩ : ℝ) < 39 * (speeds ⟨1, by omega⟩ : ℝ) := by
      exact_mod_cast h66
    have h65_R : 5 * (speeds ⟨0, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
      exact_mod_cast h65
    have h5v5_lt_7v4_R : 5 * (speeds ⟨4, by omega⟩ : ℝ) < 7 * (speeds ⟨3, by omega⟩ : ℝ) := by
      exact_mod_cast h5v5_lt_7v4
    have hlarge_R : (speeds ⟨2, by omega⟩ : ℝ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℝ) := by
      exact_mod_cast hlarge
    have h81_R : 5 * (speeds ⟨3, by omega⟩ : ℝ) < 7 * (speeds ⟨2, by omega⟩ : ℝ) := by
      exact_mod_cast h81
    -- Non-emptiness: max ≤ 11/(6 v_3).
    have hab1 : 13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)) ≤
                11 / (6 * (speeds ⟨2, by omega⟩ : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h_empty_R, hv2_pos_R, hv3_pos_R]
    have hab2 : 7 / (6 * (speeds ⟨1, by omega⟩ : ℝ)) ≤
                11 / (6 * (speeds ⟨2, by omega⟩ : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h66_R, hv1_pos_R, hv2_pos_R]
    have hab : max (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
                   (7 / (6 * (speeds ⟨1, by omega⟩ : ℝ))) ≤
               11 / (6 * (speeds ⟨2, by omega⟩ : ℝ)) := max_le hab1 hab2
    obtain ⟨k, hk_lo, hk_hi⟩ :=
      block_containment speeds ⟨4, by omega⟩ (hpos _) _ _ hab h_incl
    -- Upper bound: 11 v_5 < (6k+1) v_3.
    have h6v3R : (0 : ℝ) < 6 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
    have hk_hi' : 11 * (speeds ⟨4, by omega⟩ : ℝ) <
                  (6 * (k : ℝ) + 1) * (speeds ⟨2, by omega⟩ : ℝ) := by
      have hmul := mul_lt_mul_of_pos_right hk_hi h6v3R
      have hclear : ((speeds ⟨4, by omega⟩ : ℝ) * (11 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))) *
                    (6 * (speeds ⟨2, by omega⟩ : ℝ)) =
                    11 * (speeds ⟨4, by omega⟩ : ℝ) := by field_simp
      nlinarith [hmul, hclear]
    have hk_hi_int : 11 * (speeds ⟨4, by omega⟩ : ℤ) <
                     (6 * k + 1) * (speeds ⟨2, by omega⟩ : ℤ) := by exact_mod_cast hk_hi'
    -- Force k ≥ 3 (same as find_68).
    have hk_ge_3 : 3 ≤ k := by
      by_contra hk_lt
      push_neg at hk_lt
      have hk_le_2 : k ≤ 2 := by omega
      have h6kp1_le : 6 * k + 1 ≤ 13 := by linarith
      have h11v5_lt_13v3 : 11 * (speeds ⟨4, by omega⟩ : ℤ) <
                            13 * (speeds ⟨2, by omega⟩ : ℤ) := by
        calc 11 * (speeds ⟨4, by omega⟩ : ℤ)
            < (6 * k + 1) * (speeds ⟨2, by omega⟩ : ℤ) := hk_hi_int
          _ ≤ 13 * (speeds ⟨2, by omega⟩ : ℤ) := by
              apply mul_le_mul_of_nonneg_right h6kp1_le (le_of_lt hv3_int)
      linarith [h65, hlarge, h11v5_lt_13v3, hv1_int]
    -- Force k ≤ 3 (same as find_68).
    have hk_le_3 : k ≤ 3 := by
      by_contra hk_gt
      push_neg at hk_gt
      have hk_ge_4 : 4 ≤ k := hk_gt
      have h23_lt : (23 : ℝ) < 6 * ((speeds ⟨4, by omega⟩ : ℝ) *
                     max (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
                         (7 / (6 * (speeds ⟨1, by omega⟩ : ℝ)))) := by
        have h6mul : 6 * ((k : ℝ) - 1/6) < 6 *
                     ((speeds ⟨4, by omega⟩ : ℝ) *
                       max (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
                           (7 / (6 * (speeds ⟨1, by omega⟩ : ℝ)))) :=
          mul_lt_mul_of_pos_left hk_lo (by norm_num)
        have h6km1_simp : 6 * ((k : ℝ) - 1/6) = 6 * (k : ℝ) - 1 := by ring
        rw [h6km1_simp] at h6mul
        have h6km1_ge : (23 : ℝ) ≤ 6 * (k : ℝ) - 1 := by
          exact_mod_cast (by linarith : (23 : ℤ) ≤ 6 * k - 1)
        linarith
      have hmax_eq : 6 * ((speeds ⟨4, by omega⟩ : ℝ) *
                   max (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
                       (7 / (6 * (speeds ⟨1, by omega⟩ : ℝ)))) =
                   max (13 * (speeds ⟨4, by omega⟩ : ℝ) / (speeds ⟨3, by omega⟩ : ℝ))
                       (7 * (speeds ⟨4, by omega⟩ : ℝ) / (speeds ⟨1, by omega⟩ : ℝ)) := by
        rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ (speeds ⟨4, by omega⟩ : ℝ))]
        rw [mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 6)]
        congr 1
        · field_simp
        · field_simp
      rw [hmax_eq] at h23_lt
      rcases lt_max_iff.mp h23_lt with hcase1 | hcase2
      · have h23v4_lt_13v5 : 23 * (speeds ⟨3, by omega⟩ : ℝ) <
                              13 * (speeds ⟨4, by omega⟩ : ℝ) := by
          rw [lt_div_iff₀ hv4_pos_R] at hcase1; linarith
        nlinarith [h23v4_lt_13v5, h5v5_lt_7v4_R, hv4_pos_R, hv5_pos_R]
      · have h23v2_lt_7v5 : 23 * (speeds ⟨1, by omega⟩ : ℝ) <
                             7 * (speeds ⟨4, by omega⟩ : ℝ) := by
          rw [lt_div_iff₀ hv2_pos_R] at hcase2; linarith
        nlinarith [h23v2_lt_7v5, h66_R, h5v5_lt_7v4_R, h81_R,
                   hv2_pos_R, hv3_pos_R, hv4_pos_R, hv5_pos_R]
    have hk_eq_3 : k = 3 := le_antisymm hk_le_3 hk_ge_3
    subst hk_eq_3
    -- At k = 3, derive lower bound disjunction `17 v_4 < 13 v_5 ∨ 17 v_2 < 7 v_5`.
    have h17_lt : (17 : ℝ) < 6 * ((speeds ⟨4, by omega⟩ : ℝ) *
                   max (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
                       (7 / (6 * (speeds ⟨1, by omega⟩ : ℝ)))) := by
      have h6mul := mul_lt_mul_of_pos_left hk_lo (by norm_num : (0 : ℝ) < 6)
      have hkm16 : 6 * ((3 : ℤ) - 1/6 : ℝ) = 17 := by norm_num
      have : 6 * (((3 : ℤ) : ℝ) - 1/6) = 17 := by push_cast; norm_num
      linarith [h6mul, this]
    have hmax_eq : 6 * ((speeds ⟨4, by omega⟩ : ℝ) *
                 max (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
                     (7 / (6 * (speeds ⟨1, by omega⟩ : ℝ)))) =
                 max (13 * (speeds ⟨4, by omega⟩ : ℝ) / (speeds ⟨3, by omega⟩ : ℝ))
                     (7 * (speeds ⟨4, by omega⟩ : ℝ) / (speeds ⟨1, by omega⟩ : ℝ)) := by
      rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ (speeds ⟨4, by omega⟩ : ℝ))]
      rw [mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 6)]
      congr 1
      · field_simp
      · field_simp
    rw [hmax_eq] at h17_lt
    rcases lt_max_iff.mp h17_lt with hA | hB
    · -- Case A: 17 v_4 < 13 v_5. Combine with h811: 17 v_2 < 7 v_5.
      have h17v4_lt_13v5_R : 17 * (speeds ⟨3, by omega⟩ : ℝ) <
                             13 * (speeds ⟨4, by omega⟩ : ℝ) := by
        rw [lt_div_iff₀ hv4_pos_R] at hA; linarith
      have h17v4_lt_13v5 : 17 * (speeds ⟨3, by omega⟩ : ℤ) <
                           13 * (speeds ⟨4, by omega⟩ : ℤ) := by exact_mod_cast h17v4_lt_13v5_R
      -- 17·13 v_2 ≤ 17·7 v_4 = 119 v_4. And 7·17 v_4 < 7·13 v_5 = 91 v_5.
      -- So 7·17·13 v_2 ≤ 7·119 v_4 = 833 v_4 < 7·13·17 v_5/17 ... actually:
      -- 17 v_4 < 13 v_5 ⟹ 7·17 v_4 < 91 v_5. h811 × 17: 17·13 v_2 ≤ 119 v_4 < 91 v_5 · 17/7 ...
      -- Cleanest: 91 v_5 > 7·17 v_4 ≥ 7·(13 v_2)·17/(7·17) ... wait. 13 v_2 ≤ 7 v_4 ⟹ 13·17 v_2 ≤ 7·17 v_4 < 13·17·13/17 v_5 = 13·13 v_5 ... no.
      -- Direct: 17 v_4 < 13 v_5 and 13 v_2 ≤ 7 v_4 ⟹ multiply by 7 and 13 respectively:
      --   7·17 v_4 < 7·13 v_5 = 91 v_5; 13·17 v_2 ≤ 13·7 v_4 = 91 v_4. Hmm doesn't directly compose.
      -- Try: 13 v_2 ≤ 7 v_4. Multiply by 13: 169 v_2 ≤ 91 v_4. And 17 v_4 < 13 v_5 ⟹ 91·17 v_4 < 91·13 v_5 = 1183 v_5 ⟹ 91 v_4 < 1183 v_5/17 = 69.6 v_5. Hmm.
      -- Simpler: 17 v_2 < 7 v_5 ⟺ 17·13 v_2 < 7·13 v_5 = 91 v_5. From 13 v_2 ≤ 7 v_4: 17·13 v_2 ≤ 17·7 v_4 = 119 v_4. Want 119 v_4 < 91 v_5 ⟺ 17 v_4 < 13 v_5. ✓ exactly hA.
      -- So 17·13 v_2 ≤ 119 v_4 < 91 v_5 (using 17 v_4 < 13 v_5 ⟹ 7·17 v_4 < 7·13 v_5 = 91 v_5 ⟹ 119 v_4 < 91 v_5).
      -- Thus 13·(17 v_2) < 13·(7 v_5), divide by 13: 17 v_2 < 7 v_5.
      nlinarith [h811, h17v4_lt_13v5, hv5_int]
    · -- Case B: 17 v_2 < 7 v_5. Directly.
      have h17v2_lt_7v5_R : 17 * (speeds ⟨1, by omega⟩ : ℝ) <
                            7 * (speeds ⟨4, by omega⟩ : ℝ) := by
        rw [lt_div_iff₀ hv2_pos_R] at hB; linarith
      exact_mod_cast h17v2_lt_7v5_R

set_option maxHeartbeats 1200000 in
/-- **§8.1.2 derivation of BHK (72) `17 v_4 < 13 v_5` from 1234-gap-B + h812.**

    Mirrors `bhk_8_1_1_find_69` but for §8.1.2's case condition
    `h812 : 7 v_4 < 13 v_2`. The (68) lower-bound disjunction
    `17 v_4 < 13 v_5 ∨ 17 v_2 < 7 v_5` always entails (72) under h812.

    Strategy:

    * **Empty case** `11 v_4 < 13 v_3`: 55 v_4 < 65 v_3 (h_empty × 5), and
      h65 + hlarge give 5 v_3 < 3 v_5 ⟹ 65 v_3 < 39 v_5 ⟹ 55 v_4 < 39 v_5.
      Multiply by 17: 935 v_4 < 663 v_5 < 715 v_5 = 55·13 v_5, hence
      17 v_4 < 13 v_5.

    * **Non-empty case** `13 v_3 ≤ 11 v_4`: block_containment on runner 5
      forces k = 3. At k = 3, lower bound gives the disjunction
      `17 v_4 < 13 v_5 ∨ 17 v_2 < 7 v_5`. Dispatch on h812:
      - Case A `17 v_4 < 13 v_5`: direct.
      - Case B `17 v_2 < 7 v_5`: combined with h812 `7 v_4 < 13 v_2`,
        7·17 v_4 < 7·13 v_2 = 91 v_2 (wait: 7 v_4 < 13 v_2 ⟹ 17·7 v_4 < 17·13 v_2 = 221 v_2),
        and 13·17 v_2 < 13·7 v_5 = 91 v_5, so 221 v_2 < 91 v_5;
        thus 119 v_4 < 221 v_2 < 91 v_5 ⟹ 17 v_4 < 13 v_5 (divide by 7). -/
lemma bhk_8_1_2_find_72 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hlarge : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ))
    (h81 : 5 * (speeds ⟨3, by omega⟩ : ℤ) < 7 * (speeds ⟨2, by omega⟩ : ℤ))
    (h65 : 5 * (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ))
    (h5v5_lt_7v4 : 5 * (speeds ⟨4, by omega⟩ : ℤ) < 7 * (speeds ⟨3, by omega⟩ : ℤ))
    (h66 : 25 * (speeds ⟨2, by omega⟩ : ℤ) < 39 * (speeds ⟨1, by omega⟩ : ℤ))
    (h67 : 11 * (speeds ⟨1, by omega⟩ : ℤ) < 7 * (speeds ⟨3, by omega⟩ : ℤ))
    (h812 : 7 * (speeds ⟨3, by omega⟩ : ℤ) < 13 * (speeds ⟨1, by omega⟩ : ℤ))
    (h_incl : Set.Icc (max (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
                            (7 / (6 * (speeds ⟨1, by omega⟩ : ℝ))))
                       (11 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
              ⊆ unsafeOf speeds ⟨4, by omega⟩) :
    17 * (speeds ⟨3, by omega⟩ : ℤ) < 13 * (speeds ⟨4, by omega⟩ : ℤ) := by
  have hv1_int : (0 : ℤ) < (speeds ⟨0, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  have hv2_int : (0 : ℤ) < (speeds ⟨1, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  have hv3_int : (0 : ℤ) < (speeds ⟨2, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  have hv4_int : (0 : ℤ) < (speeds ⟨3, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  have hv5_int : (0 : ℤ) < (speeds ⟨4, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  by_cases h_empty : 11 * (speeds ⟨3, by omega⟩ : ℤ) < 13 * (speeds ⟨2, by omega⟩ : ℤ)
  · -- Empty case: 11 v_4 < 13 v_3 + h65 + hlarge ⟹ 17 v_4 < 13 v_5.
    -- 55 v_4 < 65 v_3; 65 v_3 < 39 v_5 (from 5 v_3 < 3 v_5 via h65+hlarge ×13); hence
    -- 55 v_4 < 39 v_5 ⟹ 935 v_4 < 663 v_5 < 715 v_5 = 55·13 v_5 ⟹ 17 v_4 < 13 v_5.
    nlinarith [h_empty, h65, hlarge, hv1_int, hv3_int, hv4_int, hv5_int]
  · push_neg at h_empty -- 13 v_3 ≤ 11 v_4
    have hv1_pos_R : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hv1_int
    have hv2_pos_R : (0 : ℝ) < (speeds ⟨1, by omega⟩ : ℝ) := by exact_mod_cast hv2_int
    have hv3_pos_R : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hv3_int
    have hv4_pos_R : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hv4_int
    have hv5_pos_R : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hv5_int
    have h_empty_R : 13 * (speeds ⟨2, by omega⟩ : ℝ) ≤ 11 * (speeds ⟨3, by omega⟩ : ℝ) := by
      exact_mod_cast h_empty
    have h66_R : 25 * (speeds ⟨2, by omega⟩ : ℝ) < 39 * (speeds ⟨1, by omega⟩ : ℝ) := by
      exact_mod_cast h66
    have h65_R : 5 * (speeds ⟨0, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
      exact_mod_cast h65
    have h5v5_lt_7v4_R : 5 * (speeds ⟨4, by omega⟩ : ℝ) < 7 * (speeds ⟨3, by omega⟩ : ℝ) := by
      exact_mod_cast h5v5_lt_7v4
    have hlarge_R : (speeds ⟨2, by omega⟩ : ℝ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℝ) := by
      exact_mod_cast hlarge
    have h81_R : 5 * (speeds ⟨3, by omega⟩ : ℝ) < 7 * (speeds ⟨2, by omega⟩ : ℝ) := by
      exact_mod_cast h81
    -- Non-emptiness: max ≤ 11/(6 v_3).
    have hab1 : 13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)) ≤
                11 / (6 * (speeds ⟨2, by omega⟩ : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h_empty_R, hv2_pos_R, hv3_pos_R]
    have hab2 : 7 / (6 * (speeds ⟨1, by omega⟩ : ℝ)) ≤
                11 / (6 * (speeds ⟨2, by omega⟩ : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h66_R, hv1_pos_R, hv2_pos_R]
    have hab : max (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
                   (7 / (6 * (speeds ⟨1, by omega⟩ : ℝ))) ≤
               11 / (6 * (speeds ⟨2, by omega⟩ : ℝ)) := max_le hab1 hab2
    obtain ⟨k, hk_lo, hk_hi⟩ :=
      block_containment speeds ⟨4, by omega⟩ (hpos _) _ _ hab h_incl
    -- Upper bound: 11 v_5 < (6k+1) v_3.
    have h6v3R : (0 : ℝ) < 6 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
    have hk_hi' : 11 * (speeds ⟨4, by omega⟩ : ℝ) <
                  (6 * (k : ℝ) + 1) * (speeds ⟨2, by omega⟩ : ℝ) := by
      have hmul := mul_lt_mul_of_pos_right hk_hi h6v3R
      have hclear : ((speeds ⟨4, by omega⟩ : ℝ) * (11 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))) *
                    (6 * (speeds ⟨2, by omega⟩ : ℝ)) =
                    11 * (speeds ⟨4, by omega⟩ : ℝ) := by field_simp
      nlinarith [hmul, hclear]
    have hk_hi_int : 11 * (speeds ⟨4, by omega⟩ : ℤ) <
                     (6 * k + 1) * (speeds ⟨2, by omega⟩ : ℤ) := by exact_mod_cast hk_hi'
    -- Force k ≥ 3 (same as find_68).
    have hk_ge_3 : 3 ≤ k := by
      by_contra hk_lt
      push_neg at hk_lt
      have hk_le_2 : k ≤ 2 := by omega
      have h6kp1_le : 6 * k + 1 ≤ 13 := by linarith
      have h11v5_lt_13v3 : 11 * (speeds ⟨4, by omega⟩ : ℤ) <
                            13 * (speeds ⟨2, by omega⟩ : ℤ) := by
        calc 11 * (speeds ⟨4, by omega⟩ : ℤ)
            < (6 * k + 1) * (speeds ⟨2, by omega⟩ : ℤ) := hk_hi_int
          _ ≤ 13 * (speeds ⟨2, by omega⟩ : ℤ) := by
              apply mul_le_mul_of_nonneg_right h6kp1_le (le_of_lt hv3_int)
      linarith [h65, hlarge, h11v5_lt_13v3, hv1_int]
    -- Force k ≤ 3 (same as find_68).
    have hk_le_3 : k ≤ 3 := by
      by_contra hk_gt
      push_neg at hk_gt
      have hk_ge_4 : 4 ≤ k := hk_gt
      have h23_lt : (23 : ℝ) < 6 * ((speeds ⟨4, by omega⟩ : ℝ) *
                     max (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
                         (7 / (6 * (speeds ⟨1, by omega⟩ : ℝ)))) := by
        have h6mul : 6 * ((k : ℝ) - 1/6) < 6 *
                     ((speeds ⟨4, by omega⟩ : ℝ) *
                       max (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
                           (7 / (6 * (speeds ⟨1, by omega⟩ : ℝ)))) :=
          mul_lt_mul_of_pos_left hk_lo (by norm_num)
        have h6km1_simp : 6 * ((k : ℝ) - 1/6) = 6 * (k : ℝ) - 1 := by ring
        rw [h6km1_simp] at h6mul
        have h6km1_ge : (23 : ℝ) ≤ 6 * (k : ℝ) - 1 := by
          exact_mod_cast (by linarith : (23 : ℤ) ≤ 6 * k - 1)
        linarith
      have hmax_eq : 6 * ((speeds ⟨4, by omega⟩ : ℝ) *
                   max (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
                       (7 / (6 * (speeds ⟨1, by omega⟩ : ℝ)))) =
                   max (13 * (speeds ⟨4, by omega⟩ : ℝ) / (speeds ⟨3, by omega⟩ : ℝ))
                       (7 * (speeds ⟨4, by omega⟩ : ℝ) / (speeds ⟨1, by omega⟩ : ℝ)) := by
        rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ (speeds ⟨4, by omega⟩ : ℝ))]
        rw [mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 6)]
        congr 1
        · field_simp
        · field_simp
      rw [hmax_eq] at h23_lt
      rcases lt_max_iff.mp h23_lt with hcase1 | hcase2
      · have h23v4_lt_13v5 : 23 * (speeds ⟨3, by omega⟩ : ℝ) <
                              13 * (speeds ⟨4, by omega⟩ : ℝ) := by
          rw [lt_div_iff₀ hv4_pos_R] at hcase1; linarith
        nlinarith [h23v4_lt_13v5, h5v5_lt_7v4_R, hv4_pos_R, hv5_pos_R]
      · have h23v2_lt_7v5 : 23 * (speeds ⟨1, by omega⟩ : ℝ) <
                             7 * (speeds ⟨4, by omega⟩ : ℝ) := by
          rw [lt_div_iff₀ hv2_pos_R] at hcase2; linarith
        nlinarith [h23v2_lt_7v5, h66_R, h5v5_lt_7v4_R, h81_R,
                   hv2_pos_R, hv3_pos_R, hv4_pos_R, hv5_pos_R]
    have hk_eq_3 : k = 3 := le_antisymm hk_le_3 hk_ge_3
    subst hk_eq_3
    -- At k = 3, derive lower bound disjunction `17 v_4 < 13 v_5 ∨ 17 v_2 < 7 v_5`.
    have h17_lt : (17 : ℝ) < 6 * ((speeds ⟨4, by omega⟩ : ℝ) *
                   max (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
                       (7 / (6 * (speeds ⟨1, by omega⟩ : ℝ)))) := by
      have h6mul := mul_lt_mul_of_pos_left hk_lo (by norm_num : (0 : ℝ) < 6)
      have : 6 * (((3 : ℤ) : ℝ) - 1/6) = 17 := by push_cast; norm_num
      linarith [h6mul, this]
    have hmax_eq : 6 * ((speeds ⟨4, by omega⟩ : ℝ) *
                 max (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
                     (7 / (6 * (speeds ⟨1, by omega⟩ : ℝ)))) =
                 max (13 * (speeds ⟨4, by omega⟩ : ℝ) / (speeds ⟨3, by omega⟩ : ℝ))
                     (7 * (speeds ⟨4, by omega⟩ : ℝ) / (speeds ⟨1, by omega⟩ : ℝ)) := by
      rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ (speeds ⟨4, by omega⟩ : ℝ))]
      rw [mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 6)]
      congr 1
      · field_simp
      · field_simp
    rw [hmax_eq] at h17_lt
    rcases lt_max_iff.mp h17_lt with hA | hB
    · -- Case A: 17 v_4 < 13 v_5. Directly the goal.
      have h17v4_lt_13v5_R : 17 * (speeds ⟨3, by omega⟩ : ℝ) <
                             13 * (speeds ⟨4, by omega⟩ : ℝ) := by
        rw [lt_div_iff₀ hv4_pos_R] at hA; linarith
      exact_mod_cast h17v4_lt_13v5_R
    · -- Case B: 17 v_2 < 7 v_5. Combine with h812 (7 v_4 < 13 v_2) to get 17 v_4 < 13 v_5.
      -- 17·7 v_4 < 17·13 v_2 = 221 v_2 (from h812 × 17).
      -- 13·17 v_2 < 13·7 v_5 = 91 v_5 (from Case B × 13), so 221 v_2 < 91 v_5.
      -- Chain: 119 v_4 < 221 v_2 < 91 v_5 ⟹ 17 v_4 < 13 v_5 (divide by 7).
      have h17v2_lt_7v5_R : 17 * (speeds ⟨1, by omega⟩ : ℝ) <
                            7 * (speeds ⟨4, by omega⟩ : ℝ) := by
        rw [lt_div_iff₀ hv2_pos_R] at hB; linarith
      have h17v2_lt_7v5 : 17 * (speeds ⟨1, by omega⟩ : ℤ) <
                          7 * (speeds ⟨4, by omega⟩ : ℤ) := by exact_mod_cast h17v2_lt_7v5_R
      nlinarith [h812, h17v2_lt_7v5, hv5_int]

/-- **§8.1.2 structural fact `2057 v_2 < 1729 v_3`.** From h66 + h67 + (72) + h68
    via the chain `187 v_2 < 119 v_4 < 91 v_5` (h67 × 17, then (72) × 7),
    and `1001 v_5 < 1729 v_3` (h68 × 91):

    * h67 × 17: 187 v_2 < 119 v_4
    * (72) × 7: 119 v_4 < 91 v_5
    * combine + × 11: 2057 v_2 < 1001 v_5
    * h68 × 91: 1001 v_5 < 1729 v_3
    * chain: 2057 v_2 < 1729 v_3.

    Used downstream to derive `13 v_2 < 11 v_3` (runner 2 safety at t = 13/(6 v_3))
    and `21 v_2 < 20 v_3` (the 2-gap distance contradiction). -/
lemma bhk_8_1_2_2057v2_lt_1729v3 (speeds : Fin 5 → ℕ)
    (hpos : ∀ i, 0 < speeds i)
    (h67 : 11 * (speeds ⟨1, by omega⟩ : ℤ) < 7 * (speeds ⟨3, by omega⟩ : ℤ))
    (h68 : 11 * (speeds ⟨4, by omega⟩ : ℤ) < 19 * (speeds ⟨2, by omega⟩ : ℤ))
    (h72 : 17 * (speeds ⟨3, by omega⟩ : ℤ) < 13 * (speeds ⟨4, by omega⟩ : ℤ)) :
    2057 * (speeds ⟨1, by omega⟩ : ℤ) < 1729 * (speeds ⟨2, by omega⟩ : ℤ) := by
  have hv4_int : (0 : ℤ) < (speeds ⟨3, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  have hv5_int : (0 : ℤ) < (speeds ⟨4, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  nlinarith [h67, h68, h72, hv4_int, hv5_int]

/-- **§8.1.2 corollary: `13 v_2 < 11 v_3`.** Follows from
    `bhk_8_1_2_2057v2_lt_1729v3` via 13·2057 v_2 < 13·1729 v_3 = 22477 v_3 <
    22627 v_3 = 11·2057 v_3. Required for runner 2 safety at t = 13/(6 v_3). -/
lemma bhk_8_1_2_13v2_lt_11v3 (speeds : Fin 5 → ℕ)
    (hpos : ∀ i, 0 < speeds i)
    (h67 : 11 * (speeds ⟨1, by omega⟩ : ℤ) < 7 * (speeds ⟨3, by omega⟩ : ℤ))
    (h68 : 11 * (speeds ⟨4, by omega⟩ : ℤ) < 19 * (speeds ⟨2, by omega⟩ : ℤ))
    (h72 : 17 * (speeds ⟨3, by omega⟩ : ℤ) < 13 * (speeds ⟨4, by omega⟩ : ℤ)) :
    13 * (speeds ⟨1, by omega⟩ : ℤ) < 11 * (speeds ⟨2, by omega⟩ : ℤ) := by
  have hv3_int : (0 : ℤ) < (speeds ⟨2, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  have h2057 := bhk_8_1_2_2057v2_lt_1729v3 speeds hpos h67 h68 h72
  linarith

set_option maxHeartbeats 1200000 in
/-- **§8.1.2 derivation of BHK (73) `17 v_3 < 13 v_4` via t = 13/(6 v_3) point.**

    BHK p47: at t = 13/(6 v_3), runners 1, 2, 3, 5 are all safe. Hence
    runner 4 must be unsafe (h_no_lonely), forcing 13 v_4/v_3 within 1/6
    of an integer. With h81 ruling out k ≥ 4 and monotonicity ruling out
    k ≤ 2, the integer is forced to k = 3, yielding (73).

    Runner safety at t = 13/(6 v_3):
    * Runner 1 in k=0 gap [1/(6 v_1), 5/(6 v_1)]: left from hlarge
      (v_3 ≤ 3 v_1 ⟹ v_3 < 13 v_1); right from h65 + h68
      (55 v_1 < 11 v_5 < 19 v_3 ⟹ 13 v_1 < 5 v_3).
    * Runner 2 in k=1 gap [7/(6 v_2), 11/(6 v_2)]: left from h66
      (7·39 v_3 = 273 v_3 < 325 v_3 < 507 v_2 = 13·39 v_2 ⟹ 7 v_3 < 13 v_2);
      right from `bhk_8_1_2_13v2_lt_11v3` (h66 + h67 + h68 + h72).
    * Runner 3 in k=2 gap [13/(6 v_3), 17/(6 v_3)]: t = 13/(6 v_3) is the
      LEFT boundary; safe since unsafe is strict `< 1/6` (closed gap).
    * Runner 5 in k=3 gap [19/(6 v_5), 23/(6 v_5)]: left from h65 + hlarge
      (5 v_3 < 3 v_5 ⟹ 19 v_3 < 13 v_5); right from h68 (13 v_5 < 23 v_3).

    Then `mem_unsafeOf_iff_bhkB` gives k_0 with |k_0 - 13 v_4/(6 v_3)| < 1/6.
    Rule out k_0 ≤ 2: forces v_4 < v_3, contradicts hmono.
    Rule out k_0 ≥ 4: 13 v_4 > 23 v_3; from h81 (5 v_4 < 7 v_3): 13 v_4 < 91 v_3/5 < 23 v_3.
    So k_0 = 3 ⟹ (73). -/
lemma bhk_8_1_2_find_73 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hlarge : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ))
    (h81 : 5 * (speeds ⟨3, by omega⟩ : ℤ) < 7 * (speeds ⟨2, by omega⟩ : ℤ))
    (h65 : 5 * (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ))
    (h66 : 25 * (speeds ⟨2, by omega⟩ : ℤ) < 39 * (speeds ⟨1, by omega⟩ : ℤ))
    (h67 : 11 * (speeds ⟨1, by omega⟩ : ℤ) < 7 * (speeds ⟨3, by omega⟩ : ℤ))
    (h68 : 11 * (speeds ⟨4, by omega⟩ : ℤ) < 19 * (speeds ⟨2, by omega⟩ : ℤ))
    (h72 : 17 * (speeds ⟨3, by omega⟩ : ℤ) < 13 * (speeds ⟨4, by omega⟩ : ℤ))
    (h_no_lonely : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1/6) :
    17 * (speeds ⟨2, by omega⟩ : ℤ) < 13 * (speeds ⟨3, by omega⟩ : ℤ) := by
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
  have hlarge_R : v3 ≤ 3 * v1 := by rw [hv3_def, hv1_def]; exact_mod_cast hlarge
  have h81_R : 5 * v4 < 7 * v3 := by rw [hv4_def, hv3_def]; exact_mod_cast h81
  have h65_R : 5 * v1 < v5 := by rw [hv1_def, hv5_def]; exact_mod_cast h65
  have h66_R : 25 * v3 < 39 * v2 := by rw [hv3_def, hv2_def]; exact_mod_cast h66
  have h68_R : 11 * v5 < 19 * v3 := by rw [hv5_def, hv3_def]; exact_mod_cast h68
  have h_13v2_lt_11v3 := bhk_8_1_2_13v2_lt_11v3 speeds hpos h67 h68 h72
  have h_13v2_lt_11v3_R : 13 * v2 < 11 * v3 := by
    rw [hv2_def, hv3_def]; exact_mod_cast h_13v2_lt_11v3
  -- The point t = 13/(6 v_3).
  set t : ℝ := 13 / (6 * v3) with ht_def
  have ht_pos : 0 < t := by rw [ht_def]; positivity
  obtain ⟨i, hi_unsafe⟩ := h_no_lonely t
  rw [← mem_unsafeOf_iff] at hi_unsafe
  -- Runner 1: k=0 gap [1/(6 v_1), 5/(6 v_1)].
  have hnot0 : t ∉ unsafeOf speeds ⟨0, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨0, by omega⟩ (hpos _) 0 t
    · rw [show ((0:ℤ):ℝ) + 1/6 = 1/6 from by norm_num, div_div]
      -- 1/(6 v_1) ≤ 13/(6 v_3): needs v_3 ≤ 13 v_1.
      rw [ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hlarge_R, hv1_pos]
    · rw [show ((0:ℤ):ℝ) + 5/6 = 5/6 from by norm_num, div_div]
      -- 13/(6 v_3) ≤ 5/(6 v_1): needs 13 v_1 ≤ 5 v_3.
      rw [ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h65_R, h68_R, hv1_pos, hv3_pos, hv5_pos]
  -- Runner 2: k=1 gap [7/(6 v_2), 11/(6 v_2)].
  have hnot1 : t ∉ unsafeOf speeds ⟨1, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨1, by omega⟩ (hpos _) 1 t
    · rw [show ((1:ℤ):ℝ) + 1/6 = 7/6 from by norm_num, div_div]
      -- 7/(6 v_2) ≤ 13/(6 v_3): needs 7 v_3 ≤ 13 v_2, from h66.
      rw [ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h66_R, hv2_pos, hv3_pos]
    · rw [show ((1:ℤ):ℝ) + 5/6 = 11/6 from by norm_num, div_div]
      -- 13/(6 v_3) ≤ 11/(6 v_2): needs 13 v_2 ≤ 11 v_3.
      rw [ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h_13v2_lt_11v3_R, hv2_pos, hv3_pos]
  -- Runner 3: k=2 gap [13/(6 v_3), 17/(6 v_3)]. t = 13/(6 v_3) is left boundary.
  have hnot2 : t ∉ unsafeOf speeds ⟨2, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨2, by omega⟩ (hpos _) 2 t
    · rw [show ((2:ℤ):ℝ) + 1/6 = 13/6 from by norm_num, div_div, ht_def]
    · rw [show ((2:ℤ):ℝ) + 5/6 = 17/6 from by norm_num, div_div, ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith [hv3_pos]
  -- Runner 5: k=3 gap [19/(6 v_5), 23/(6 v_5)].
  have hnot4 : t ∉ unsafeOf speeds ⟨4, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨4, by omega⟩ (hpos _) 3 t
    · rw [show ((3:ℤ):ℝ) + 1/6 = 19/6 from by norm_num, div_div]
      -- 19/(6 v_5) ≤ 13/(6 v_3): needs 19 v_3 ≤ 13 v_5, from h65 + hlarge.
      rw [ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h65_R, hlarge_R, hv1_pos, hv3_pos, hv5_pos]
    · rw [show ((3:ℤ):ℝ) + 5/6 = 23/6 from by norm_num, div_div]
      -- 13/(6 v_3) ≤ 23/(6 v_5): needs 13 v_5 ≤ 23 v_3, from h68.
      rw [ht_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h68_R, hv3_pos, hv5_pos]
  -- Hence runner 4 (= i = 3) must be unsafe at t.
  have hi_eq_3 : i = ⟨3, by omega⟩ := by
    fin_cases i
    · exact absurd hi_unsafe hnot0
    · exact absurd hi_unsafe hnot1
    · exact absurd hi_unsafe hnot2
    · rfl
    · exact absurd hi_unsafe hnot4
  rw [hi_eq_3] at hi_unsafe
  rw [mem_unsafeOf_iff_bhkB] at hi_unsafe
  obtain ⟨k, hk⟩ := hi_unsafe
  -- hk : |v_4 · t - k| < 1/6 where t = 13/(6 v_3).
  -- Extract: (6k - 1) v_3 < 13 v_4 and 13 v_4 < (6k + 1) v_3.
  have hk_lo_R : ((k : ℝ) - 1/6) < v4 * t := by
    have := neg_lt_of_abs_lt hk; linarith
  have hk_hi_R : v4 * t < ((k : ℝ) + 1/6) := by
    have := lt_of_abs_lt hk; linarith
  have hv4t_eq : v4 * t = 13 * v4 / (6 * v3) := by rw [ht_def]; ring
  rw [hv4t_eq] at hk_lo_R hk_hi_R
  have h6v3_pos : (0 : ℝ) < 6 * v3 := by positivity
  -- Convert to (6k - 1) v_3 < 13 v_4 in ℝ.
  have hkL_R : (6 * (k : ℝ) - 1) * v3 < 13 * v4 := by
    have hmul := mul_lt_mul_of_pos_right hk_lo_R h6v3_pos
    have hclear : (13 * v4 / (6 * v3)) * (6 * v3) = 13 * v4 := by field_simp
    nlinarith [hmul, hclear]
  -- Convert to 13 v_4 < (6k + 1) v_3 in ℝ.
  have hkR_R : 13 * v4 < (6 * (k : ℝ) + 1) * v3 := by
    have hmul := mul_lt_mul_of_pos_right hk_hi_R h6v3_pos
    have hclear : (13 * v4 / (6 * v3)) * (6 * v3) = 13 * v4 := by field_simp
    nlinarith [hmul, hclear]
  -- Cast to ℤ.
  have hkL : (6 * k - 1) * (speeds ⟨2, by omega⟩ : ℤ) <
             13 * (speeds ⟨3, by omega⟩ : ℤ) := by
    have := hkL_R; rw [hv3_def, hv4_def] at this; exact_mod_cast this
  have hkR : 13 * (speeds ⟨3, by omega⟩ : ℤ) <
             (6 * k + 1) * (speeds ⟨2, by omega⟩ : ℤ) := by
    have := hkR_R; rw [hv3_def, hv4_def] at this; exact_mod_cast this
  have hv3_int : (0 : ℤ) < (speeds ⟨2, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  have hv4_int : (0 : ℤ) < (speeds ⟨3, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  have hv34 : (speeds ⟨2, by omega⟩ : ℤ) < (speeds ⟨3, by omega⟩ : ℤ) := by
    have hflt : (⟨2, by omega⟩ : Fin 5) < ⟨3, by omega⟩ :=
      Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast hmono hflt
  -- Force k ≥ 3: if k ≤ 2 then 13 v_4 < 13 v_3 ⟹ v_4 < v_3, contradicts hv34.
  have hk_ge_3 : 3 ≤ k := by
    by_contra hk_lt
    push_neg at hk_lt
    have hk_le_2 : k ≤ 2 := by omega
    have h6kp1_le : 6 * k + 1 ≤ 13 := by linarith
    have h_13v4_lt_13v3 : 13 * (speeds ⟨3, by omega⟩ : ℤ) <
                          13 * (speeds ⟨2, by omega⟩ : ℤ) := by
      calc 13 * (speeds ⟨3, by omega⟩ : ℤ)
          < (6 * k + 1) * (speeds ⟨2, by omega⟩ : ℤ) := hkR
        _ ≤ 13 * (speeds ⟨2, by omega⟩ : ℤ) :=
            mul_le_mul_of_nonneg_right h6kp1_le (le_of_lt hv3_int)
    linarith [hv34, h_13v4_lt_13v3, hv3_int]
  -- Force k ≤ 3: if k ≥ 4 then 23 v_3 < 13 v_4; with h81 (5 v_4 < 7 v_3): 13 v_4 < 91 v_3/5 < 23 v_3.
  have hk_le_3 : k ≤ 3 := by
    by_contra hk_gt
    push_neg at hk_gt
    have hk_ge_4 : 4 ≤ k := hk_gt
    have h6km1_ge : 23 ≤ 6 * k - 1 := by linarith
    have h_23v3_lt_13v4 : 23 * (speeds ⟨2, by omega⟩ : ℤ) <
                          13 * (speeds ⟨3, by omega⟩ : ℤ) := by
      calc 23 * (speeds ⟨2, by omega⟩ : ℤ)
          ≤ (6 * k - 1) * (speeds ⟨2, by omega⟩ : ℤ) :=
            mul_le_mul_of_nonneg_right h6km1_ge (le_of_lt hv3_int)
        _ < 13 * (speeds ⟨3, by omega⟩ : ℤ) := hkL
    -- h81: 5 v_4 < 7 v_3 ⟹ 13 v_4 < 13·7/5 v_3 = 91/5 v_3. Multiply by 5:
    -- 5·13 v_4 < 5·91/5 v_3 = 91 v_3. So 65 v_4 < 91 v_3.
    -- Want: 23 v_3 < 13 v_4 ⟹ 23·5 v_3 < 13·5 v_4 = 65 v_4 < 91 v_3 ⟹ 115 v_3 < 91 v_3, false.
    linarith [h81, h_23v3_lt_13v4, hv3_int]
  have hk_eq_3 : k = 3 := le_antisymm hk_le_3 hk_ge_3
  subst hk_eq_3
  -- At k = 3: (6·3 - 1) v_3 = 17 v_3 < 13 v_4.
  linarith [hkL]

set_option maxHeartbeats 1200000 in
/-- **§8.1.2 two-point coverage: runner 2 is unsafe at both `t_a = 109/(30 v_3)`
    and `t_b = 26/(6 v_3)`.** BHK p47: at each point, runners 1, 3, 4, 5
    are in safe gaps; h_no_lonely forces runner 2 unsafe.

    Runner k-assignments:

    | Runner | t_a = 109/(30 v_3) | t_b = 26/(6 v_3) |
    |--------|-------------------|------------------|
    | 1      | k=1 [7..11]/(6v_1) | k=1 [7..11]/(6v_1) |
    | 3      | k=3 [19..23]/(6v_3) | k=4 [25..29]/(6v_3) |
    | 4      | k=4 [25..29]/(6v_4) | k=5 [31..35]/(6v_4) |
    | 5      | k=6 [37..41]/(6v_5) | k=7 [43..47]/(6v_5) |

    All bounds are simple algebraic chains over `hlarge, h65, h66, h68, h72,
    h73` (full §8.1.2 cascade). -/
lemma bhk_8_1_2_two_point_unsafe_2 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hlarge : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ))
    (h65 : 5 * (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ))
    (h66 : 25 * (speeds ⟨2, by omega⟩ : ℤ) < 39 * (speeds ⟨1, by omega⟩ : ℤ))
    (h68 : 11 * (speeds ⟨4, by omega⟩ : ℤ) < 19 * (speeds ⟨2, by omega⟩ : ℤ))
    (h72 : 17 * (speeds ⟨3, by omega⟩ : ℤ) < 13 * (speeds ⟨4, by omega⟩ : ℤ))
    (h73 : 17 * (speeds ⟨2, by omega⟩ : ℤ) < 13 * (speeds ⟨3, by omega⟩ : ℤ))
    (h_no_lonely : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1/6) :
    (109 / (30 * (speeds ⟨2, by omega⟩ : ℝ)) ∈ unsafeOf speeds ⟨1, by omega⟩) ∧
    (26 / (6 * (speeds ⟨2, by omega⟩ : ℝ)) ∈ unsafeOf speeds ⟨1, by omega⟩) := by
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
  have hlarge_R : v3 ≤ 3 * v1 := by rw [hv3_def, hv1_def]; exact_mod_cast hlarge
  have h65_R : 5 * v1 < v5 := by rw [hv1_def, hv5_def]; exact_mod_cast h65
  have h66_R : 25 * v3 < 39 * v2 := by rw [hv3_def, hv2_def]; exact_mod_cast h66
  have h68_R : 11 * v5 < 19 * v3 := by rw [hv5_def, hv3_def]; exact_mod_cast h68
  have h72_R : 17 * v4 < 13 * v5 := by rw [hv4_def, hv5_def]; exact_mod_cast h72
  have h73_R : 17 * v3 < 13 * v4 := by rw [hv3_def, hv4_def]; exact_mod_cast h73
  -- Helper: derive `187 v_4 < 247 v_3` (from h68 + h72).
  have h187v4_lt_247v3 : 187 * v4 < 247 * v3 := by
    nlinarith [h68_R, h72_R, hv3_pos, hv4_pos, hv5_pos]
  refine ⟨?_, ?_⟩
  · -- t_a = 109/(30 v_3): runner 2 unsafe.
    set ta : ℝ := 109 / (30 * v3) with hta_def
    obtain ⟨i, hi_unsafe⟩ := h_no_lonely ta
    rw [← mem_unsafeOf_iff] at hi_unsafe
    -- Runner 1: k=1 gap.
    have hnot0 : ta ∉ unsafeOf speeds ⟨0, by omega⟩ := by
      apply not_mem_unsafeOf_of_in_gap speeds ⟨0, by omega⟩ (hpos _) 1 ta
      · rw [show ((1:ℤ):ℝ) + 1/6 = 7/6 from by norm_num, div_div, hta_def]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hlarge_R, hv1_pos]
      · rw [show ((1:ℤ):ℝ) + 5/6 = 11/6 from by norm_num, div_div, hta_def]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h65_R, h68_R, hv1_pos, hv3_pos, hv5_pos]
    -- Runner 3: k=3 gap (trivial, since v_3 cancels).
    have hnot2 : ta ∉ unsafeOf speeds ⟨2, by omega⟩ := by
      apply not_mem_unsafeOf_of_in_gap speeds ⟨2, by omega⟩ (hpos _) 3 ta
      · rw [show ((3:ℤ):ℝ) + 1/6 = 19/6 from by norm_num, div_div, hta_def]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith [hv3_pos]
      · rw [show ((3:ℤ):ℝ) + 5/6 = 23/6 from by norm_num, div_div, hta_def]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith [hv3_pos]
    -- Runner 4: k=4 gap [25/(6 v_4), 29/(6 v_4)].
    have hnot3 : ta ∉ unsafeOf speeds ⟨3, by omega⟩ := by
      apply not_mem_unsafeOf_of_in_gap speeds ⟨3, by omega⟩ (hpos _) 4 ta
      · rw [show ((4:ℤ):ℝ) + 1/6 = 25/6 from by norm_num, div_div, hta_def]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        -- 25·30 v_3 ≤ 109·6 v_4 ⟺ 125 v_3 ≤ 109 v_4; from h73.
        nlinarith [h73_R, hv3_pos, hv4_pos]
      · rw [show ((4:ℤ):ℝ) + 5/6 = 29/6 from by norm_num, div_div, hta_def]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        -- 109 v_4 ≤ 145 v_3; from 187 v_4 < 247 v_3.
        nlinarith [h187v4_lt_247v3, hv3_pos, hv4_pos]
    -- Runner 5: k=6 gap [37/(6 v_5), 41/(6 v_5)].
    have hnot4 : ta ∉ unsafeOf speeds ⟨4, by omega⟩ := by
      apply not_mem_unsafeOf_of_in_gap speeds ⟨4, by omega⟩ (hpos _) 6 ta
      · rw [show ((6:ℤ):ℝ) + 1/6 = 37/6 from by norm_num, div_div, hta_def]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        -- 185 v_3 ≤ 109 v_5; from h65 + hlarge.
        nlinarith [h65_R, hlarge_R, hv1_pos, hv3_pos, hv5_pos]
      · rw [show ((6:ℤ):ℝ) + 5/6 = 41/6 from by norm_num, div_div, hta_def]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        -- 109 v_5 ≤ 205 v_3; from h68.
        nlinarith [h68_R, hv3_pos, hv5_pos]
    -- Force i = 1 (runner 2).
    fin_cases i
    · exact absurd hi_unsafe hnot0
    · exact hi_unsafe
    · exact absurd hi_unsafe hnot2
    · exact absurd hi_unsafe hnot3
    · exact absurd hi_unsafe hnot4
  · -- t_b = 26/(6 v_3): runner 2 unsafe.
    set tb : ℝ := 26 / (6 * v3) with htb_def
    obtain ⟨i, hi_unsafe⟩ := h_no_lonely tb
    rw [← mem_unsafeOf_iff] at hi_unsafe
    -- Runner 1: k=1 gap [7/(6 v_1), 11/(6 v_1)].
    have hnot0 : tb ∉ unsafeOf speeds ⟨0, by omega⟩ := by
      apply not_mem_unsafeOf_of_in_gap speeds ⟨0, by omega⟩ (hpos _) 1 tb
      · rw [show ((1:ℤ):ℝ) + 1/6 = 7/6 from by norm_num, div_div, htb_def]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        -- 7 v_3 ≤ 26 v_1; from hlarge (v_3 ≤ 3 v_1 ⟹ 7 v_3 ≤ 21 v_1 < 26 v_1).
        nlinarith [hlarge_R, hv1_pos]
      · rw [show ((1:ℤ):ℝ) + 5/6 = 11/6 from by norm_num, div_div, htb_def]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        -- 26 v_1 ≤ 11 v_3; from h65 + h68.
        nlinarith [h65_R, h68_R, hv1_pos, hv3_pos, hv5_pos]
    -- Runner 3: k=4 gap (trivial).
    have hnot2 : tb ∉ unsafeOf speeds ⟨2, by omega⟩ := by
      apply not_mem_unsafeOf_of_in_gap speeds ⟨2, by omega⟩ (hpos _) 4 tb
      · rw [show ((4:ℤ):ℝ) + 1/6 = 25/6 from by norm_num, div_div, htb_def]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith [hv3_pos]
      · rw [show ((4:ℤ):ℝ) + 5/6 = 29/6 from by norm_num, div_div, htb_def]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith [hv3_pos]
    -- Runner 4: k=5 gap [31/(6 v_4), 35/(6 v_4)].
    have hnot3 : tb ∉ unsafeOf speeds ⟨3, by omega⟩ := by
      apply not_mem_unsafeOf_of_in_gap speeds ⟨3, by omega⟩ (hpos _) 5 tb
      · rw [show ((5:ℤ):ℝ) + 1/6 = 31/6 from by norm_num, div_div, htb_def]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        -- 31 v_3 ≤ 26 v_4; from h73.
        nlinarith [h73_R, hv3_pos, hv4_pos]
      · rw [show ((5:ℤ):ℝ) + 5/6 = 35/6 from by norm_num, div_div, htb_def]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        -- 26 v_4 ≤ 35 v_3; from 187 v_4 < 247 v_3.
        nlinarith [h187v4_lt_247v3, hv3_pos, hv4_pos]
    -- Runner 5: k=7 gap [43/(6 v_5), 47/(6 v_5)].
    have hnot4 : tb ∉ unsafeOf speeds ⟨4, by omega⟩ := by
      apply not_mem_unsafeOf_of_in_gap speeds ⟨4, by omega⟩ (hpos _) 7 tb
      · rw [show ((7:ℤ):ℝ) + 1/6 = 43/6 from by norm_num, div_div, htb_def]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        -- 43 v_3 ≤ 26 v_5; from h65 + hlarge.
        nlinarith [h65_R, hlarge_R, hv1_pos, hv3_pos, hv5_pos]
      · rw [show ((7:ℤ):ℝ) + 5/6 = 47/6 from by norm_num, div_div, htb_def]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        -- 26 v_5 ≤ 47 v_3; from h68.
        nlinarith [h68_R, hv3_pos, hv5_pos]
    fin_cases i
    · exact absurd hi_unsafe hnot0
    · exact hi_unsafe
    · exact absurd hi_unsafe hnot2
    · exact absurd hi_unsafe hnot3
    · exact absurd hi_unsafe hnot4

/-- **§8.1.1 right sub-interval inclusion.** The interval
    `[25/(6 v_5), 5/(6 v_1)]` (right piece of the 123-gap, after runner 5's
    k=4 unsafe block) is contained in `unsafeOf ⟨3⟩` (runner 4 must be unsafe).

    Geometry: runners 1, 2, 3, 5 safe on the interval (runner 1 in k=0,
    runner 2 in k=1, runner 3 in k=2, runner 5 in k=4 safe gaps). Bounds:
    * Runner 1: `1/(6v_1) ≤ 25/(6v_5)` ⟺ `v_5 ≤ 25 v_1`, from
      `h68 + hlarge` chain (`11 v_5 < 19 v_3 ≤ 57 v_1`).
    * Runner 2 left edge: `7/(6v_2) ≤ 25/(6v_5)` ⟺ `7 v_5 ≤ 25 v_2`,
      from `h68 + h66` chain.
    * Runner 2 right edge: `5/(6v_1) ≤ 11/(6v_2)` ⟺ `5 v_2 < 11 v_1`,
      from BHK (69) `17 v_2 < 7 v_5` + `h68 + hlarge` chain
      (yields `187 v_2 < 133 v_3 ≤ 399 v_1`, hence `5 v_2 < 11 v_1`).
      This bound is NOT derivable without (69) (h66+h67+h81+hlarge gives
      only the loose `5 v_2 < 13.36 v_1`).
    * Runner 3: needs `13 v_5 ≤ 25 v_3` (left, from h68) and
      `5 v_3 ≤ 17 v_1` (right, from hlarge).
    * Runner 5: needs `5 v_5 ≤ 29 v_1` (right edge of k=4 safe gap),
      from `h68 + hlarge` chain (`5·11 v_5 < 5·19 v_3 ≤ 5·57 v_1`). -/
lemma bhk_8_1_1_right_sub_incl (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hlarge : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ))
    (h65 : 5 * (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ))
    (h66 : 25 * (speeds ⟨2, by omega⟩ : ℤ) < 39 * (speeds ⟨1, by omega⟩ : ℤ))
    (h68 : 11 * (speeds ⟨4, by omega⟩ : ℤ) < 19 * (speeds ⟨2, by omega⟩ : ℤ))
    (h69 : 17 * (speeds ⟨1, by omega⟩ : ℤ) < 7 * (speeds ⟨4, by omega⟩ : ℤ))
    (h_no_lonely : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1/6) :
    Set.Icc (25 / (6 * (speeds ⟨4, by omega⟩ : ℝ)))
            (5 / (6 * (speeds ⟨0, by omega⟩ : ℝ)))
    ⊆ unsafeOf speeds ⟨3, by omega⟩ := by
  set v1 : ℝ := (speeds ⟨0, by omega⟩ : ℝ) with hv1_def
  set v2 : ℝ := (speeds ⟨1, by omega⟩ : ℝ) with hv2_def
  set v3 : ℝ := (speeds ⟨2, by omega⟩ : ℝ) with hv3_def
  set v5 : ℝ := (speeds ⟨4, by omega⟩ : ℝ) with hv5_def
  have hv1_pos : 0 < v1 := by rw [hv1_def]; exact_mod_cast hpos _
  have hv2_pos : 0 < v2 := by rw [hv2_def]; exact_mod_cast hpos _
  have hv3_pos : 0 < v3 := by rw [hv3_def]; exact_mod_cast hpos _
  have hv5_pos : 0 < v5 := by rw [hv5_def]; exact_mod_cast hpos _
  have hlarge_R : v3 ≤ 3 * v1 := by rw [hv3_def, hv1_def]; exact_mod_cast hlarge
  have h65_R : 5 * v1 < v5 := by rw [hv1_def, hv5_def]; exact_mod_cast h65
  have h66_R : 25 * v3 < 39 * v2 := by rw [hv3_def, hv2_def]; exact_mod_cast h66
  have h68_R : 11 * v5 < 19 * v3 := by rw [hv5_def, hv3_def]; exact_mod_cast h68
  have h69_R : 17 * v2 < 7 * v5 := by rw [hv2_def, hv5_def]; exact_mod_cast h69
  intro t ht
  obtain ⟨htL, htR⟩ := ht
  obtain ⟨i, hi_unsafe⟩ := h_no_lonely t
  rw [← mem_unsafeOf_iff] at hi_unsafe
  -- Runner 1: k=0 safe gap [1/(6 v_1), 5/(6 v_1)].
  have hnot0 : t ∉ unsafeOf speeds ⟨0, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨0, by omega⟩ (hpos _) 0 t
    · rw [show ((0:ℤ):ℝ) + 1/6 = 1/6 from by norm_num, div_div]
      -- 1/(6 v_1) ≤ 25/(6 v_5): need v_5 ≤ 25 v_1.
      -- From h68 (11 v_5 < 19 v_3) + hlarge (v_3 ≤ 3 v_1): 11 v_5 < 57 v_1 < 275 v_1.
      have hbound : 1 / (6 * v1) ≤ 25 / (6 * v5) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h68_R, hlarge_R, hv1_pos, hv5_pos]
      linarith [htL, hbound]
    · rw [show ((0:ℤ):ℝ) + 5/6 = 5/6 from by norm_num, div_div]
      exact htR
  -- Runner 2: k=1 safe gap [7/(6 v_2), 11/(6 v_2)].
  have hnot1 : t ∉ unsafeOf speeds ⟨1, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨1, by omega⟩ (hpos _) 1 t
    · rw [show ((1:ℤ):ℝ) + 1/6 = 7/6 from by norm_num, div_div]
      -- 7/(6 v_2) ≤ 25/(6 v_5): need 7 v_5 ≤ 25 v_2.
      -- From h68 (11 v_5 < 19 v_3) + h66 (25 v_3 < 39 v_2):
      --   275 v_5 < 19·25 v_3 < 19·39 v_2 = 741 v_2 ⟹ 7·275 v_5 < 7·741 v_2,
      --   i.e. 1925 v_5 < 5187 v_2. Want 175 v_5 ≤ 625 v_2, i.e. 1925 v_5 ≤ 6875 v_2.
      have hbound : 7 / (6 * v2) ≤ 25 / (6 * v5) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h68_R, h66_R, hv2_pos, hv3_pos, hv5_pos]
      linarith [htL, hbound]
    · rw [show ((1:ℤ):ℝ) + 5/6 = 11/6 from by norm_num, div_div]
      -- 5/(6 v_1) ≤ 11/(6 v_2): need 5 v_2 < 11 v_1.
      -- From h69 (17 v_2 < 7 v_5) + h68 (11 v_5 < 19 v_3) + hlarge (v_3 ≤ 3 v_1):
      --   11·17 v_2 < 11·7 v_5 < 7·19 v_3 ⟹ 187 v_2 < 133 v_3 ≤ 399 v_1.
      --   So 5·187 v_2 < 5·399 v_1 = 1995 v_1 < 2057 v_1 = 11·187 v_1.
      --   Hence 5 v_2 < 11 v_1.
      have hbound : 5 / (6 * v1) ≤ 11 / (6 * v2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h69_R, h68_R, hlarge_R, hv1_pos, hv2_pos, hv3_pos, hv5_pos]
      linarith [htR, hbound]
  -- Runner 3: k=2 safe gap [13/(6 v_3), 17/(6 v_3)].
  have hnot2 : t ∉ unsafeOf speeds ⟨2, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨2, by omega⟩ (hpos _) 2 t
    · rw [show ((2:ℤ):ℝ) + 1/6 = 13/6 from by norm_num, div_div]
      -- 13/(6 v_3) ≤ 25/(6 v_5): need 13 v_5 ≤ 25 v_3.
      -- From h68 (11 v_5 < 19 v_3): 11·13 v_5 < 11·25 v_3 ⟹ 143 v_5 < 275 v_3
      --   ⟸ 13·11 v_5 < 13·19 v_3 = 247 v_3 < 275 v_3 (clean from h68).
      have hbound : 13 / (6 * v3) ≤ 25 / (6 * v5) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h68_R, hv3_pos, hv5_pos]
      linarith [htL, hbound]
    · rw [show ((2:ℤ):ℝ) + 5/6 = 17/6 from by norm_num, div_div]
      -- 5/(6 v_1) ≤ 17/(6 v_3): need 5 v_3 ≤ 17 v_1.
      -- From hlarge: v_3 ≤ 3 v_1 ⟹ 5 v_3 ≤ 15 v_1 < 17 v_1.
      have hbound : 5 / (6 * v1) ≤ 17 / (6 * v3) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hlarge_R, hv1_pos, hv3_pos]
      linarith [htR, hbound]
  -- Runner 5: k=4 safe gap [25/(6 v_5), 29/(6 v_5)].
  have hnot4 : t ∉ unsafeOf speeds ⟨4, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨4, by omega⟩ (hpos _) 4 t
    · rw [show ((4:ℤ):ℝ) + 1/6 = 25/6 from by norm_num, div_div]
      exact htL
    · rw [show ((4:ℤ):ℝ) + 5/6 = 29/6 from by norm_num, div_div]
      -- 5/(6 v_1) ≤ 29/(6 v_5): need 5 v_5 ≤ 29 v_1.
      -- From h68 (11 v_5 < 19 v_3) + hlarge (v_3 ≤ 3 v_1):
      --   11 v_5 < 19·3 v_1 = 57 v_1 ⟹ 5·11 v_5 < 5·57 v_1 = 285 v_1 < 319 v_1 = 11·29 v_1.
      have hbound : 5 / (6 * v1) ≤ 29 / (6 * v5) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h68_R, hlarge_R, hv1_pos, hv3_pos, hv5_pos]
      linarith [htR, hbound]
  fin_cases i
  · exact absurd hi_unsafe hnot0
  · exact absurd hi_unsafe hnot1
  · exact absurd hi_unsafe hnot2
  · exact hi_unsafe
  · exact absurd hi_unsafe hnot4

/-- **§8.1.1 derivation of BHK (70b) `5 v_4 < 19 v_1` from right sub-interval.**

    From `bhk_8_1_1_right_sub_incl` (`[25/(6 v_5), 5/(6 v_1)] ⊆ unsafeOf ⟨3⟩`)
    plus the cascade (`h65`, `h5v5_lt_7v4`, `h81`, `hlarge`), derive (70b).

    Strategy: `block_containment` for runner 4 gives `k ∈ ℤ` with
    `(6k-1) v_5 < 25 v_4` and `5 v_4 < (6k+1) v_1`. Force `k = 3`:

    * **`k ≥ 3`**: if `k ≤ 2`, `5 v_4 < 13 v_1`. But `h65 + h5v5_lt_7v4`
      give `25 v_1 < 5 v_5 < 7 v_4 ⟹ 125 v_1 < 35 v_4`, hence
      `5 v_4 > 125 v_1/7 > 17 v_1 > 13 v_1`. Contradiction.

    * **`k ≤ 3`**: if `k ≥ 4`, `23 v_5 < 25 v_4`. With `h81` (`5 v_4 < 7 v_3`):
      `23 v_5 < 25 v_4 < 35 v_3`. With `hlarge` (`v_3 ≤ 3 v_1`):
      `23 v_5 < 105 v_1`. But `h65` × 23 gives `115 v_1 < 23 v_5`.
      Chain: `115 v_1 < 105 v_1`, contradiction.

    Then `k = 3` substituted into upper bound gives `5 v_4 < 19 v_1` = (70b). -/
lemma bhk_8_1_1_find_70b (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hlarge : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ))
    (h81 : 5 * (speeds ⟨3, by omega⟩ : ℤ) < 7 * (speeds ⟨2, by omega⟩ : ℤ))
    (h65 : 5 * (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ))
    (h5v5_lt_7v4 : 5 * (speeds ⟨4, by omega⟩ : ℤ) < 7 * (speeds ⟨3, by omega⟩ : ℤ))
    (h_incl : Set.Icc (25 / (6 * (speeds ⟨4, by omega⟩ : ℝ)))
                      (5 / (6 * (speeds ⟨0, by omega⟩ : ℝ)))
              ⊆ unsafeOf speeds ⟨3, by omega⟩) :
    5 * (speeds ⟨3, by omega⟩ : ℤ) < 19 * (speeds ⟨0, by omega⟩ : ℤ) := by
  have hv1_int : (0 : ℤ) < (speeds ⟨0, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  have hv3_int : (0 : ℤ) < (speeds ⟨2, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  have hv4_int : (0 : ℤ) < (speeds ⟨3, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  have hv5_int : (0 : ℤ) < (speeds ⟨4, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  have hv1_pos_R : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hv1_int
  have hv5_pos_R : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hv5_int
  have h6v1R : (0 : ℝ) < 6 * (speeds ⟨0, by omega⟩ : ℝ) := by positivity
  have h6v5R : (0 : ℝ) < 6 * (speeds ⟨4, by omega⟩ : ℝ) := by positivity
  set a : ℝ := 25 / (6 * (speeds ⟨4, by omega⟩ : ℝ)) with ha_def
  set b : ℝ := 5 / (6 * (speeds ⟨0, by omega⟩ : ℝ)) with hb_def
  -- a ≤ b ⟺ 25/(6 v_5) ≤ 5/(6 v_1) ⟺ 5 v_1 ≤ v_5 (from h65).
  have hab : a ≤ b := by
    rw [ha_def, hb_def, div_le_div_iff₀ h6v5R h6v1R]
    have h65_R : 5 * (speeds ⟨0, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
      exact_mod_cast h65
    nlinarith [h65_R, hv1_pos_R, hv5_pos_R]
  -- Apply block_containment on runner 4.
  obtain ⟨k, hk_lo, hk_hi⟩ := block_containment speeds ⟨3, by omega⟩ (hpos _) a b hab h_incl
  -- Convert v_4 · a, v_4 · b to clean forms.
  have hva_eq : (speeds ⟨3, by omega⟩ : ℝ) * a =
                25 * (speeds ⟨3, by omega⟩ : ℝ) / (6 * (speeds ⟨4, by omega⟩ : ℝ)) := by
    rw [ha_def]; ring
  have hvb_eq : (speeds ⟨3, by omega⟩ : ℝ) * b =
                5 * (speeds ⟨3, by omega⟩ : ℝ) / (6 * (speeds ⟨0, by omega⟩ : ℝ)) := by
    rw [hb_def]; ring
  rw [hva_eq] at hk_lo
  rw [hvb_eq] at hk_hi
  -- Convert to (6k - 1) v_5 < 25 v_4 in ℝ.
  have hkL_R : (6 * (k : ℝ) - 1) * (speeds ⟨4, by omega⟩ : ℝ) <
               25 * (speeds ⟨3, by omega⟩ : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hk_lo h6v5R
    have hclear : (25 * (speeds ⟨3, by omega⟩ : ℝ) / (6 * (speeds ⟨4, by omega⟩ : ℝ))) *
                  (6 * (speeds ⟨4, by omega⟩ : ℝ)) = 25 * (speeds ⟨3, by omega⟩ : ℝ) := by
      field_simp
    nlinarith [hmul, hclear]
  -- Convert to 5 v_4 < (6k + 1) v_1 in ℝ.
  have hkR_R : 5 * (speeds ⟨3, by omega⟩ : ℝ) <
               (6 * (k : ℝ) + 1) * (speeds ⟨0, by omega⟩ : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hk_hi h6v1R
    have hclear : (5 * (speeds ⟨3, by omega⟩ : ℝ) / (6 * (speeds ⟨0, by omega⟩ : ℝ))) *
                  (6 * (speeds ⟨0, by omega⟩ : ℝ)) = 5 * (speeds ⟨3, by omega⟩ : ℝ) := by
      field_simp
    nlinarith [hmul, hclear]
  -- Cast to ℤ.
  have hkL : (6 * k - 1) * (speeds ⟨4, by omega⟩ : ℤ) < 25 * (speeds ⟨3, by omega⟩ : ℤ) := by
    exact_mod_cast hkL_R
  have hkR : 5 * (speeds ⟨3, by omega⟩ : ℤ) < (6 * k + 1) * (speeds ⟨0, by omega⟩ : ℤ) := by
    exact_mod_cast hkR_R
  -- Force k ≥ 3: rule out k ≤ 2 via h65 + h5v5_lt_7v4.
  have hk_ge_3 : 3 ≤ k := by
    by_contra hk_lt
    push_neg at hk_lt
    have hk_le_2 : k ≤ 2 := by omega
    have h6kp1_le : 6 * k + 1 ≤ 13 := by linarith
    have h5v4_lt_13v1 : 5 * (speeds ⟨3, by omega⟩ : ℤ) < 13 * (speeds ⟨0, by omega⟩ : ℤ) := by
      calc 5 * (speeds ⟨3, by omega⟩ : ℤ)
          < (6 * k + 1) * (speeds ⟨0, by omega⟩ : ℤ) := hkR
        _ ≤ 13 * (speeds ⟨0, by omega⟩ : ℤ) :=
            mul_le_mul_of_nonneg_right h6kp1_le (le_of_lt hv1_int)
    -- Chain: h65 (5 v_1 < v_5) + h5v5_lt_7v4 (5 v_5 < 7 v_4):
    -- 25 v_1 < 5 v_5 < 7 v_4 ⟹ 175 v_1 < 5·7 v_4 = 35 v_4 ⟹ 5 v_4 > 175 v_1/7 = 25 v_1.
    -- Combined with 5 v_4 < 13 v_1: 25 v_1 < 13 v_1 (since v_1 > 0), false.
    nlinarith [h65, h5v5_lt_7v4, h5v4_lt_13v1, hv1_int]
  -- Force k ≤ 3: rule out k ≥ 4 via h81 + hlarge + h65 chain.
  have hk_le_3 : k ≤ 3 := by
    by_contra hk_gt
    push_neg at hk_gt
    have hk_ge_4 : 4 ≤ k := hk_gt
    have h6km1_ge : 23 ≤ 6 * k - 1 := by linarith
    have h23v5_lt_25v4 : 23 * (speeds ⟨4, by omega⟩ : ℤ) < 25 * (speeds ⟨3, by omega⟩ : ℤ) := by
      calc 23 * (speeds ⟨4, by omega⟩ : ℤ)
          ≤ (6 * k - 1) * (speeds ⟨4, by omega⟩ : ℤ) :=
            mul_le_mul_of_nonneg_right h6km1_ge (le_of_lt hv5_int)
        _ < 25 * (speeds ⟨3, by omega⟩ : ℤ) := hkL
    -- 23 v_5 < 25 v_4 < 35 v_3 (h81 × 5) ≤ 105 v_1 (hlarge × 35).
    -- h65 × 23: 115 v_1 < 23 v_5. So 115 v_1 < 105 v_1, false.
    nlinarith [h81, hlarge, h65, h23v5_lt_25v4, hv1_int]
  have hk_eq_3 : k = 3 := le_antisymm hk_le_3 hk_ge_3
  subst hk_eq_3
  -- At k = 3: 5 v_4 < (6·3 + 1) v_1 = 19 v_1.
  linarith [hkR]

set_option maxHeartbeats 1200000 in
/-- **§8.1.1 1235-gap inclusion (BHK p47).** Under (65) `5 v_1 < v_5`,
    (66) `25 v_3 < 39 v_2`, (68) `11 v_5 < 19 v_3`, (69) `17 v_2 < 7 v_5`
    plus `hlarge : v_3 ≤ 3 v_1`, the interval `[37/(6 v_5), 23/(6 v_3)]`
    is contained in `unsafeOf speeds ⟨3⟩` (i.e. covered by runner 4 alone).

    Geometry — each of runners 1, 2, 3, 5 lies in a single safe k-gap on
    the interval:

    * Runner 1 in k=1 gap `[7/(6 v_1), 11/(6 v_1)]`.
      - Left `7 v_5 < 37 v_1` via `h68 + hlarge`
        (`77 v_5 < 133 v_3 ≤ 399 v_1 < 407 v_1 = 11·37 v_1`).
      - Right `23 v_1 < 11 v_3` via `h65 + h68`
        (`437 v_1 < 605 v_1 < 11·19 v_3 / 11 ·11 = 209 v_3`).
    * Runner 2 in k=2 gap `[13/(6 v_2), 17/(6 v_2)]`.
      - Left `13 v_5 < 37 v_2` via `h68 + h66`
        (`275 v_5 < 475 v_3 < 741 v_2`).
      - Right `23 v_2 < 17 v_3` via `h69 + h68`
        (`187 v_2 < 77 v_5 < 133 v_3`; then `23·187 v_2 < 3059 v_3 < 3179 v_3 = 17·187 v_3`).
    * Runner 3 in k=3 gap `[19/(6 v_3), 23/(6 v_3)]` (right end trivial).
      - Left `19 v_5 < 37 v_3` via `h68`
        (`209 v_5 < 361 v_3 < 407 v_3 = 11·37 v_3`).
    * Runner 5 in k=6 gap `[37/(6 v_5), 41/(6 v_5)]` (left end trivial).
      - Right `23 v_5 < 41 v_3` via `h68`
        (`253 v_5 < 437 v_3 < 451 v_3 = 11·41 v_3`).

    The same hypothesis bundle as `bhk_8_1_1_right_sub_incl`; no fresh
    structural fact is required (in particular (70a)/(70b)/h81 are not
    needed for the inclusion — they only enter the kernel via `find_71b`). -/
lemma bhk_8_1_1_1235_gap_incl (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hlarge : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ))
    (h65 : 5 * (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ))
    (h66 : 25 * (speeds ⟨2, by omega⟩ : ℤ) < 39 * (speeds ⟨1, by omega⟩ : ℤ))
    (h68 : 11 * (speeds ⟨4, by omega⟩ : ℤ) < 19 * (speeds ⟨2, by omega⟩ : ℤ))
    (h69 : 17 * (speeds ⟨1, by omega⟩ : ℤ) < 7 * (speeds ⟨4, by omega⟩ : ℤ))
    (h_no_lonely : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1/6) :
    Set.Icc (37 / (6 * (speeds ⟨4, by omega⟩ : ℝ)))
            (23 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
    ⊆ unsafeOf speeds ⟨3, by omega⟩ := by
  set v1 : ℝ := (speeds ⟨0, by omega⟩ : ℝ) with hv1_def
  set v2 : ℝ := (speeds ⟨1, by omega⟩ : ℝ) with hv2_def
  set v3 : ℝ := (speeds ⟨2, by omega⟩ : ℝ) with hv3_def
  set v5 : ℝ := (speeds ⟨4, by omega⟩ : ℝ) with hv5_def
  have hv1_pos : 0 < v1 := by rw [hv1_def]; exact_mod_cast hpos _
  have hv2_pos : 0 < v2 := by rw [hv2_def]; exact_mod_cast hpos _
  have hv3_pos : 0 < v3 := by rw [hv3_def]; exact_mod_cast hpos _
  have hv5_pos : 0 < v5 := by rw [hv5_def]; exact_mod_cast hpos _
  have hlarge_R : v3 ≤ 3 * v1 := by rw [hv3_def, hv1_def]; exact_mod_cast hlarge
  have h65_R : 5 * v1 < v5 := by rw [hv1_def, hv5_def]; exact_mod_cast h65
  have h66_R : 25 * v3 < 39 * v2 := by rw [hv3_def, hv2_def]; exact_mod_cast h66
  have h68_R : 11 * v5 < 19 * v3 := by rw [hv5_def, hv3_def]; exact_mod_cast h68
  have h69_R : 17 * v2 < 7 * v5 := by rw [hv2_def, hv5_def]; exact_mod_cast h69
  intro t ht
  obtain ⟨htL, htR⟩ := ht
  obtain ⟨i, hi_unsafe⟩ := h_no_lonely t
  rw [← mem_unsafeOf_iff] at hi_unsafe
  -- Runner 1 (speeds ⟨0⟩): k=1 gap [7/(6 v_1), 11/(6 v_1)].
  have hnot0 : t ∉ unsafeOf speeds ⟨0, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨0, by omega⟩ (hpos _) 1 t
    · rw [show ((1:ℤ):ℝ) + 1/6 = 7/6 from by norm_num, div_div]
      -- 7/(6 v_1) ≤ 37/(6 v_5): needs 7 v_5 ≤ 37 v_1.
      have hbound : 7 / (6 * v1) ≤ 37 / (6 * v5) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h68_R, hlarge_R, hv1_pos, hv3_pos, hv5_pos]
      linarith [htL, hbound]
    · rw [show ((1:ℤ):ℝ) + 5/6 = 11/6 from by norm_num, div_div]
      -- 23/(6 v_3) ≤ 11/(6 v_1): needs 23 v_1 ≤ 11 v_3.
      have hbound : 23 / (6 * v3) ≤ 11 / (6 * v1) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h65_R, h68_R, hv1_pos, hv3_pos, hv5_pos]
      linarith [htR, hbound]
  -- Runner 2 (speeds ⟨1⟩): k=2 gap [13/(6 v_2), 17/(6 v_2)].
  have hnot1 : t ∉ unsafeOf speeds ⟨1, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨1, by omega⟩ (hpos _) 2 t
    · rw [show ((2:ℤ):ℝ) + 1/6 = 13/6 from by norm_num, div_div]
      -- 13/(6 v_2) ≤ 37/(6 v_5): needs 13 v_5 ≤ 37 v_2.
      have hbound : 13 / (6 * v2) ≤ 37 / (6 * v5) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h66_R, h68_R, hv2_pos, hv3_pos, hv5_pos]
      linarith [htL, hbound]
    · rw [show ((2:ℤ):ℝ) + 5/6 = 17/6 from by norm_num, div_div]
      -- 23/(6 v_3) ≤ 17/(6 v_2): needs 23 v_2 ≤ 17 v_3.
      have hbound : 23 / (6 * v3) ≤ 17 / (6 * v2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h68_R, h69_R, hv2_pos, hv3_pos, hv5_pos]
      linarith [htR, hbound]
  -- Runner 3 (speeds ⟨2⟩): k=3 gap [19/(6 v_3), 23/(6 v_3)].
  have hnot2 : t ∉ unsafeOf speeds ⟨2, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨2, by omega⟩ (hpos _) 3 t
    · rw [show ((3:ℤ):ℝ) + 1/6 = 19/6 from by norm_num, div_div]
      -- 19/(6 v_3) ≤ 37/(6 v_5): needs 19 v_5 ≤ 37 v_3.
      have hbound : 19 / (6 * v3) ≤ 37 / (6 * v5) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h68_R, hv3_pos, hv5_pos]
      linarith [htL, hbound]
    · rw [show ((3:ℤ):ℝ) + 5/6 = 23/6 from by norm_num, div_div]
      exact htR
  -- Runner 5 (speeds ⟨4⟩): k=6 gap [37/(6 v_5), 41/(6 v_5)].
  have hnot4 : t ∉ unsafeOf speeds ⟨4, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨4, by omega⟩ (hpos _) 6 t
    · rw [show ((6:ℤ):ℝ) + 1/6 = 37/6 from by norm_num, div_div]
      exact htL
    · rw [show ((6:ℤ):ℝ) + 5/6 = 41/6 from by norm_num, div_div]
      -- 23/(6 v_3) ≤ 41/(6 v_5): needs 23 v_5 ≤ 41 v_3.
      have hbound : 23 / (6 * v3) ≤ 41 / (6 * v5) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [h68_R, hv3_pos, hv5_pos]
      linarith [htR, hbound]
  fin_cases i
  · exact absurd hi_unsafe hnot0
  · exact absurd hi_unsafe hnot1
  · exact absurd hi_unsafe hnot2
  · exact hi_unsafe
  · exact absurd hi_unsafe hnot4

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

    These three contradict via `bhk_case_8_1_1_kernel`. (70b) is now closed
    via the §8.1 cascade (h66, h67, h68, h69) + the 123-gap RIGHT sub-interval
    inclusion + `bhk_8_1_1_find_70b`. The residual sorry now contains exactly
    one atomic piece: the 1235-gap inclusion
    `[37/(6 v_5), 23/(6 v_3)] ⊆ unsafeOf speeds ⟨3⟩`. -/
theorem bhk_case_8_1_1 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hlarge : speeds ⟨2, by omega⟩ ≤ 3 * speeds ⟨0, by omega⟩)
    (h81 : 5 * speeds ⟨3, by omega⟩ < 7 * speeds ⟨2, by omega⟩)
    (h811 : 13 * speeds ⟨1, by omega⟩ ≤ 7 * speeds ⟨3, by omega⟩) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  by_contra h_no_lonely
  push_neg at h_no_lonely
  -- Cast hypotheses to ℤ.
  have hlarge_int : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ) := by
    exact_mod_cast hlarge
  have h81_int : 5 * (speeds ⟨3, by omega⟩ : ℤ) < 7 * (speeds ⟨2, by omega⟩ : ℤ) := by
    exact_mod_cast h81
  have h811_int : 13 * (speeds ⟨1, by omega⟩ : ℤ) ≤ 7 * (speeds ⟨3, by omega⟩ : ℤ) := by
    exact_mod_cast h811
  -- 1234-gap inclusion via the common helper (depends only on monotonicity).
  have h_1234_incl := bhk_8_1_1234_gap_incl speeds hmono hpos h_no_lonely
  -- Apply find_65 to extract (65) `5 v_1 < v_5` and `5 v_5 < 7 v_4`.
  obtain ⟨h65, h5v5_lt_7v4⟩ :=
    bhk_8_1_step1_find_65 speeds hmono hpos hlarge_int h81_int h_1234_incl
  -- Structural fact: `v_4 < 2 v_3` via the §8 helper (123-gap + bhk_lemma_4).
  have _hv4_lt_2v3 : (speeds ⟨3, by omega⟩ : ℝ) < 2 * (speeds ⟨2, by omega⟩ : ℝ) :=
    bhk_8_v4_lt_2v3 speeds hmono hpos hlarge h_no_lonely
  -- §8.1 cascade: 1345-gap → (66), (67); 1234-gap-B → (68); + h811 → (69).
  have h_1345_incl :=
    bhk_8_1_1345_gap_incl speeds hmono hpos hlarge_int h65 h5v5_lt_7v4 h_no_lonely
  obtain ⟨h66, h67⟩ :=
    bhk_8_1_step2_find_66_67 speeds hmono hpos hlarge_int h81_int h65 h5v5_lt_7v4 h_1345_incl
  have h_1234B_incl :=
    bhk_8_1_1234_gap_B_incl speeds hmono hpos hlarge_int h81_int h65 h5v5_lt_7v4 h_no_lonely
  have h68 := bhk_8_1_step3_find_68 speeds hmono hpos hlarge_int h81_int h65 h5v5_lt_7v4
                                     h66 h67 h_1234B_incl
  have h69 := bhk_8_1_1_find_69 speeds hmono hpos hlarge_int h81_int h65 h5v5_lt_7v4
                                 h66 h67 h811_int h_1234B_incl
  -- (70b) via 123-gap RIGHT sub-interval + find_70b.
  have h_right_incl :=
    bhk_8_1_1_right_sub_incl speeds hmono hpos hlarge_int h65 h66 h68 h69 h_no_lonely
  have h70b := bhk_8_1_1_find_70b speeds hmono hpos hlarge_int h81_int h65 h5v5_lt_7v4
                                   h_right_incl
  -- 1235-gap inclusion (closed via `bhk_8_1_1_1235_gap_incl`): same
  -- hypothesis bundle as `bhk_8_1_1_right_sub_incl` — only (65), (66),
  -- (68), (69), `hlarge` are needed.
  have h_1235_incl :=
    bhk_8_1_1_1235_gap_incl speeds hmono hpos hlarge_int h65 h66 h68 h69 h_no_lonely
  -- Apply find_71b to derive (71b) `29 v_5 < 37 v_4` from the inclusion.
  have h71b := bhk_8_1_step3_find_71b speeds hmono hpos hlarge_int h65
                                       h5v5_lt_7v4 h_1235_incl
  exact bhk_case_8_1_1_kernel speeds hpos h65 h70b h71b

/-- **Arithmetic kernel for BHK §8.1.2 (two-point block-width contradiction).**

    From the §8.1.2 cascade bounds (`h66`, `h2057`) and the two-point
    runner-2 unsafe pair at `t_a = 109/(30 v_3)` and `t_b = 26/(6 v_3) =
    130/(30 v_3)`, derive a contradiction via the 2-block-width vs
    2-gap-length argument.

    Arithmetic chain (BHK p47):

    * `t_b - t_a = 21/(30 v_3) = 7/(10 v_3)`.
    * `v_2 (t_b - t_a) = 7 v_2/(10 v_3)`.
    * From `h66` (`25 v_3 < 39 v_2`): `21·25 v_3 < 21·39 v_2 ⟹
      525 v_3 < 819 v_2`. Hence `390 v_3 < 525 v_3 < 819 v_2`, so
      `10 v_3 < 21 v_2`, i.e. `7 v_2/(10 v_3) > 1/3`.
    * From `h2057` (`2057 v_2 < 1729 v_3`, =`bhk_8_1_2_2057v2_lt_1729v3`):
      `21·2057 v_2 < 21·1729 v_3 ⟹ 43197 v_2 < 36309 v_3 < 41140 v_3
      = 2057·20 v_3`, so `21 v_2 < 20 v_3`, i.e. `7 v_2/(10 v_3) < 2/3`.
    * Each unsafe gives integer `k_a, k_b` with `|v_2 t_a - k_a| < 1/6` and
      `|v_2 t_b - k_b| < 1/6`. Triangle inequality:
      `|(k_b - k_a) - 7 v_2/(10 v_3)| < 1/3`. Hence
      `0 < k_b - k_a < 1` strictly, contradicting integer arithmetic. -/
lemma bhk_case_8_1_2_kernel (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (h66 : 25 * (speeds ⟨2, by omega⟩ : ℤ) < 39 * (speeds ⟨1, by omega⟩ : ℤ))
    (h2057 : 2057 * (speeds ⟨1, by omega⟩ : ℤ) < 1729 * (speeds ⟨2, by omega⟩ : ℤ))
    (h_two_points :
      (109 / (30 * (speeds ⟨2, by omega⟩ : ℝ)) ∈ unsafeOf speeds ⟨1, by omega⟩) ∧
      (26 / (6 * (speeds ⟨2, by omega⟩ : ℝ)) ∈ unsafeOf speeds ⟨1, by omega⟩)) :
    False := by
  obtain ⟨ha, hb⟩ := h_two_points
  rw [mem_unsafeOf_iff_bhkB] at ha hb
  obtain ⟨k_a, hka⟩ := ha
  obtain ⟨k_b, hkb⟩ := hb
  have hv2_pos : (0 : ℝ) < (speeds ⟨1, by omega⟩ : ℝ) := by
    exact_mod_cast hpos ⟨1, by omega⟩
  have hv3_pos : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hpos ⟨2, by omega⟩
  have h66_R : 25 * (speeds ⟨2, by omega⟩ : ℝ) < 39 * (speeds ⟨1, by omega⟩ : ℝ) := by
    exact_mod_cast h66
  have h2057_R : 2057 * (speeds ⟨1, by omega⟩ : ℝ) < 1729 * (speeds ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast h2057
  -- Bounds on `7 v_2/(10 v_3)`.
  have h_lower : (1 : ℝ)/3 < 7 * (speeds ⟨1, by omega⟩ : ℝ) / (10 * (speeds ⟨2, by omega⟩ : ℝ)) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [h66_R, hv2_pos, hv3_pos]
  have h_upper : 7 * (speeds ⟨1, by omega⟩ : ℝ) / (10 * (speeds ⟨2, by omega⟩ : ℝ)) < 2/3 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [h2057_R, hv2_pos, hv3_pos]
  -- Algebraic identity: v_2 · (26/(6 v_3) - 109/(30 v_3)) = 7 v_2/(10 v_3).
  have h_diff_eq :
      (speeds ⟨1, by omega⟩ : ℝ) * (26 / (6 * (speeds ⟨2, by omega⟩ : ℝ))) -
      (speeds ⟨1, by omega⟩ : ℝ) * (109 / (30 * (speeds ⟨2, by omega⟩ : ℝ))) =
      7 * (speeds ⟨1, by omega⟩ : ℝ) / (10 * (speeds ⟨2, by omega⟩ : ℝ)) := by
    have hv3_ne : (speeds ⟨2, by omega⟩ : ℝ) ≠ 0 := ne_of_gt hv3_pos
    field_simp
    ring
  -- Triangle inequality: |(k_b - k_a) - 7 v_2/(10 v_3)| < 1/3.
  have h_triangle :
      |((k_b : ℝ) - k_a) -
       7 * (speeds ⟨1, by omega⟩ : ℝ) / (10 * (speeds ⟨2, by omega⟩ : ℝ))| < 1/3 := by
    have h_rearr :
        ((k_b : ℝ) - k_a) -
          7 * (speeds ⟨1, by omega⟩ : ℝ) / (10 * (speeds ⟨2, by omega⟩ : ℝ)) =
        -((speeds ⟨1, by omega⟩ : ℝ) * (26 / (6 * (speeds ⟨2, by omega⟩ : ℝ))) - k_b) +
        ((speeds ⟨1, by omega⟩ : ℝ) * (109 / (30 * (speeds ⟨2, by omega⟩ : ℝ))) - k_a) := by
      rw [← h_diff_eq]; ring
    rw [h_rearr]
    calc |-((speeds ⟨1, by omega⟩ : ℝ) * (26 / (6 * (speeds ⟨2, by omega⟩ : ℝ))) - k_b) +
          ((speeds ⟨1, by omega⟩ : ℝ) * (109 / (30 * (speeds ⟨2, by omega⟩ : ℝ))) - k_a)|
        ≤ |-((speeds ⟨1, by omega⟩ : ℝ) * (26 / (6 * (speeds ⟨2, by omega⟩ : ℝ))) - k_b)| +
          |((speeds ⟨1, by omega⟩ : ℝ) * (109 / (30 * (speeds ⟨2, by omega⟩ : ℝ))) - k_a)| :=
          abs_add_le _ _
      _ = |(speeds ⟨1, by omega⟩ : ℝ) * (26 / (6 * (speeds ⟨2, by omega⟩ : ℝ))) - k_b| +
          |(speeds ⟨1, by omega⟩ : ℝ) * (109 / (30 * (speeds ⟨2, by omega⟩ : ℝ))) - k_a| := by
          rw [abs_neg]
      _ < 1/6 + 1/6 := by linarith [hka, hkb]
      _ = 1/3 := by norm_num
  -- Extract k_b - k_a bounds.
  rcases abs_lt.mp h_triangle with ⟨h_diff_lb, h_diff_ub⟩
  -- 7 v_2/(10 v_3) > 1/3 ⟹ k_b - k_a > 0.
  have hdiff_pos : (0 : ℝ) < (k_b : ℝ) - k_a := by linarith
  -- 7 v_2/(10 v_3) < 2/3 ⟹ k_b - k_a < 1.
  have hdiff_lt_1 : (k_b : ℝ) - k_a < 1 := by linarith
  -- Integer impossibility: 0 < k_b - k_a < 1.
  have hkb_gt_ka : k_a < k_b := by
    have h_int : (0 : ℤ) < k_b - k_a := by exact_mod_cast hdiff_pos
    omega
  have hkb_lt_ka_plus_1 : k_b < k_a + 1 := by
    have : (k_b : ℝ) < (k_a : ℝ) + 1 := by linarith
    exact_mod_cast this
  omega

/-- **BHK §8.1.2.** Sub-case of `x_1 ≤ 3` with `x_4 > 5/7` (de-normalised:
    `5 * speeds ⟨3⟩ < 7 * speeds ⟨2⟩`) AND `7 x_2 < 13 x_4` (de-normalised:
    `7 * speeds ⟨3⟩ < 13 * speeds ⟨1⟩`). See BHK p46–47.

    Proof structure: assume for contradiction no lonely `t` exists. BHK p47:

    1. §8.1 cascade: 1234-gap → (65); 1345-gap → (66), (67); 1234-gap-B → (68).
    2. §8.1.2-specific: 1234-gap-B + h812 → (72) `17 v_4 < 13 v_5`;
       t = 13/(6 v_3) point → (73) `17 v_3 < 13 v_4`.
    3. Two-point argument: t_a = 109/(30 v_3) and t_b = 26/(6 v_3) both
       in 1345-gaps, hence runner 2 covers both. But the distance
       7/(10 v_3) is > runner-2 2-block width 13/25 and < runner-2 2-gap
       length 4114/5187 — contradiction via `bhk_case_8_1_2_kernel`. -/
theorem bhk_case_8_1_2 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hlarge : speeds ⟨2, by omega⟩ ≤ 3 * speeds ⟨0, by omega⟩)
    (h81 : 5 * speeds ⟨3, by omega⟩ < 7 * speeds ⟨2, by omega⟩)
    (h812 : 7 * speeds ⟨3, by omega⟩ < 13 * speeds ⟨1, by omega⟩) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  by_contra h_no_lonely
  push_neg at h_no_lonely
  -- Cast hypotheses to ℤ.
  have hlarge_int : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ) := by
    exact_mod_cast hlarge
  have h81_int : 5 * (speeds ⟨3, by omega⟩ : ℤ) < 7 * (speeds ⟨2, by omega⟩ : ℤ) := by
    exact_mod_cast h81
  have h812_int : 7 * (speeds ⟨3, by omega⟩ : ℤ) < 13 * (speeds ⟨1, by omega⟩ : ℤ) := by
    exact_mod_cast h812
  -- §8.1 cascade.
  have h_1234_incl := bhk_8_1_1234_gap_incl speeds hmono hpos h_no_lonely
  obtain ⟨h65, h5v5_lt_7v4⟩ :=
    bhk_8_1_step1_find_65 speeds hmono hpos hlarge_int h81_int h_1234_incl
  have h_1345_incl :=
    bhk_8_1_1345_gap_incl speeds hmono hpos hlarge_int h65 h5v5_lt_7v4 h_no_lonely
  obtain ⟨h66, h67⟩ :=
    bhk_8_1_step2_find_66_67 speeds hmono hpos hlarge_int h81_int h65 h5v5_lt_7v4 h_1345_incl
  have h_1234B_incl :=
    bhk_8_1_1234_gap_B_incl speeds hmono hpos hlarge_int h81_int h65 h5v5_lt_7v4 h_no_lonely
  have h68 := bhk_8_1_step3_find_68 speeds hmono hpos hlarge_int h81_int h65 h5v5_lt_7v4
                                     h66 h67 h_1234B_incl
  -- §8.1.2: (72) via find_72 + h812.
  have h72 := bhk_8_1_2_find_72 speeds hmono hpos hlarge_int h81_int h65 h5v5_lt_7v4
                                 h66 h67 h812_int h_1234B_incl
  -- (73) via t = 13/(6 v_3) point analysis.
  have h73 := bhk_8_1_2_find_73 speeds hmono hpos hlarge_int h81_int h65
                                 h66 h67 h68 h72 h_no_lonely
  -- Two-point unsafe at t_a = 109/(30 v_3), t_b = 26/(6 v_3).
  have h_two_points := bhk_8_1_2_two_point_unsafe_2 speeds hmono hpos hlarge_int h65
                                                     h66 h68 h72 h73 h_no_lonely
  -- 2057 v_2 < 1729 v_3 (from h67 + h68 + h72).
  have h2057 := bhk_8_1_2_2057v2_lt_1729v3 speeds hpos h67 h68 h72
  -- Apply kernel.
  exact bhk_case_8_1_2_kernel speeds hpos h66 h2057 h_two_points

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

/-! ## §8.2.2 helpers (BHK p47–48) -/

/-- **BHK §8.2.2 final kernel (2-line algebraic contradiction).**
    From the two-point runner-2 bounds `5 v_3 < 7 v_2` (from `t = 7/(6 v_3)`
    forcing into `B_2`) and `3 v_2 < 2 v_3` (from `t = 7/(4 v_3)` forcing
    into `B_2`), derive a contradiction.

    Chain: `15 v_3 < 21 v_2 < 14 v_3`, so `v_3 < 0`, contradicting `v_3 > 0`. -/
lemma bhk_case_8_2_2_kernel (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (h_lo : 5 * (speeds ⟨2, by omega⟩ : ℤ) < 7 * (speeds ⟨1, by omega⟩ : ℤ))
    (h_up : 3 * (speeds ⟨1, by omega⟩ : ℤ) < 2 * (speeds ⟨2, by omega⟩ : ℤ)) :
    False := by
  have hv3 : (0 : ℤ) < (speeds ⟨2, by omega⟩ : ℤ) := by exact_mod_cast hpos ⟨2, by omega⟩
  linarith

/-- **§8.2.2 LEFT-strip inclusion** `[1/(6 v_1), 5/(6 v_4)] ⊆ unsafeOf 5`.
    Rules out runners 0, 1, 2, 3 — all in their k=0 gaps. Requires only
    monotonicity + `h822 : v_4 ≤ 5 v_1` (to make the interval non-empty). -/
lemma bhk_8_2_2_left_strip_incl (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (h_no_lonely : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1/6) :
    Set.Icc (1 / (6 * (speeds ⟨0, by omega⟩ : ℝ)))
            (5 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
    ⊆ unsafeOf speeds ⟨4, by omega⟩ := by
  intro t ht
  obtain ⟨htL, htR⟩ := ht
  obtain ⟨i, hi_unsafe⟩ := h_no_lonely t
  rw [← mem_unsafeOf_iff] at hi_unsafe
  -- Pre-cast monotonicity facts.
  have hv1_pos : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv2_pos : (0 : ℝ) < (speeds ⟨1, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv3_pos : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4_pos : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv1_le_v2 : (speeds ⟨0, by omega⟩ : ℝ) ≤ (speeds ⟨1, by omega⟩ : ℝ) :=
    by exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr (show (0:ℕ) < 1 by omega)))
  have hv1_le_v3 : (speeds ⟨0, by omega⟩ : ℝ) ≤ (speeds ⟨2, by omega⟩ : ℝ) :=
    by exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr (show (0:ℕ) < 2 by omega)))
  have hv1_le_v4 : (speeds ⟨0, by omega⟩ : ℝ) ≤ (speeds ⟨3, by omega⟩ : ℝ) :=
    by exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr (show (0:ℕ) < 3 by omega)))
  have hv2_le_v4 : (speeds ⟨1, by omega⟩ : ℝ) ≤ (speeds ⟨3, by omega⟩ : ℝ) :=
    by exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr (show (1:ℕ) < 3 by omega)))
  have hv3_le_v4 : (speeds ⟨2, by omega⟩ : ℝ) ≤ (speeds ⟨3, by omega⟩ : ℝ) :=
    by exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr (show (2:ℕ) < 3 by omega)))
  -- Rule out runner 0 (k=0).
  have hnot0 : t ∉ unsafeOf speeds ⟨0, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨0, by omega⟩ (hpos _) 0 t
    · rw [show ((0:ℤ):ℝ) + 1/6 = 1/6 from by norm_num, div_div]
      exact htL
    · rw [show ((0:ℤ):ℝ) + 5/6 = 5/6 from by norm_num, div_div]
      calc t ≤ 5 / (6 * (speeds ⟨3, by omega⟩ : ℝ)) := htR
        _ ≤ 5 / (6 * (speeds ⟨0, by omega⟩ : ℝ)) := by
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            nlinarith [hv1_le_v4, hv1_pos, hv4_pos]
  -- Rule out runner 1 (k=0).
  have hnot1 : t ∉ unsafeOf speeds ⟨1, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨1, by omega⟩ (hpos _) 0 t
    · rw [show ((0:ℤ):ℝ) + 1/6 = 1/6 from by norm_num, div_div]
      calc (1 : ℝ) / (6 * (speeds ⟨1, by omega⟩ : ℝ))
          ≤ 1 / (6 * (speeds ⟨0, by omega⟩ : ℝ)) := by
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            nlinarith [hv1_le_v2, hv1_pos, hv2_pos]
        _ ≤ t := htL
    · rw [show ((0:ℤ):ℝ) + 5/6 = 5/6 from by norm_num, div_div]
      calc t ≤ 5 / (6 * (speeds ⟨3, by omega⟩ : ℝ)) := htR
        _ ≤ 5 / (6 * (speeds ⟨1, by omega⟩ : ℝ)) := by
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            nlinarith [hv2_le_v4, hv2_pos, hv4_pos]
  -- Rule out runner 2 (k=0).
  have hnot2 : t ∉ unsafeOf speeds ⟨2, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨2, by omega⟩ (hpos _) 0 t
    · rw [show ((0:ℤ):ℝ) + 1/6 = 1/6 from by norm_num, div_div]
      calc (1 : ℝ) / (6 * (speeds ⟨2, by omega⟩ : ℝ))
          ≤ 1 / (6 * (speeds ⟨0, by omega⟩ : ℝ)) := by
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            nlinarith [hv1_le_v3, hv1_pos, hv3_pos]
        _ ≤ t := htL
    · rw [show ((0:ℤ):ℝ) + 5/6 = 5/6 from by norm_num, div_div]
      calc t ≤ 5 / (6 * (speeds ⟨3, by omega⟩ : ℝ)) := htR
        _ ≤ 5 / (6 * (speeds ⟨2, by omega⟩ : ℝ)) := by
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            nlinarith [hv3_le_v4, hv3_pos, hv4_pos]
  -- Rule out runner 3 (k=0). Note runner 3 = v_4 is in its ORIGIN gap.
  have hnot3 : t ∉ unsafeOf speeds ⟨3, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨3, by omega⟩ (hpos _) 0 t
    · rw [show ((0:ℤ):ℝ) + 1/6 = 1/6 from by norm_num, div_div]
      calc (1 : ℝ) / (6 * (speeds ⟨3, by omega⟩ : ℝ))
          ≤ 1 / (6 * (speeds ⟨0, by omega⟩ : ℝ)) := by
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            nlinarith [hv1_le_v4, hv1_pos, hv4_pos]
        _ ≤ t := htL
    · rw [show ((0:ℤ):ℝ) + 5/6 = 5/6 from by norm_num, div_div]
      exact htR
  -- So i = 4.
  fin_cases i
  · exact absurd hi_unsafe hnot0
  · exact absurd hi_unsafe hnot1
  · exact absurd hi_unsafe hnot2
  · exact absurd hi_unsafe hnot3
  · exact hi_unsafe

/-- **§8.2 RIGHT-strip inclusion** `[7/(6 v_4), 5/(6 v_3)] ⊆ unsafeOf 5`.
    The §8.2.1 inclusion, repackaged as a standalone helper. Requires
    `hlarge` (for `v_4 < 6 v_1`) and `v_4 < 2 v_3` (derived via
    `bhk_8_v4_lt_2v3` from `hlarge + h_no_lonely`). Does NOT depend on
    `h821` (`5 v_1 < v_4`), so reusable for §8.2.2. -/
lemma bhk_8_2_right_strip_incl (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hlarge : speeds ⟨2, by omega⟩ ≤ 3 * speeds ⟨0, by omega⟩)
    (h_no_lonely : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1/6) :
    Set.Icc (7 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
            (5 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
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
    rw [hv1_def, hv2_def]; exact_mod_cast Nat.le_of_lt
      (hmono (Fin.mk_lt_mk.mpr (show (0:ℕ) < 1 by omega)))
  have hv1_le_v3 : v1 ≤ v3 := by
    rw [hv1_def, hv3_def]; exact_mod_cast Nat.le_of_lt
      (hmono (Fin.mk_lt_mk.mpr (show (0:ℕ) < 2 by omega)))
  have hv2_le_v3 : v2 ≤ v3 := by
    rw [hv2_def, hv3_def]; exact_mod_cast Nat.le_of_lt
      (hmono (Fin.mk_lt_mk.mpr (show (1:ℕ) < 2 by omega)))
  have hlargeR : v3 ≤ 3 * v1 := by
    rw [hv1_def, hv3_def]; exact_mod_cast hlarge
  -- Derive `v_4 < 2 v_3` via the §8 helper.
  have hv4_lt_2v3 : v4 < 2 * v3 := by
    have h := bhk_8_v4_lt_2v3 speeds hmono hpos hlarge h_no_lonely
    rw [hv3_def, hv4_def]; exact h
  have hv4_lt_6v1 : v4 < 6 * v1 := by linarith [hv4_lt_2v3, hlargeR]
  have hv4_lt_6v2 : v4 < 6 * v2 := by linarith [hv4_lt_6v1, hv1_le_v2]
  have hv4_lt_6v3 : v4 < 6 * v3 := by linarith [hv4_lt_2v3, hv3_pos]
  -- Build inclusion: rule out runners 0,1,2,3.
  intro t ht
  obtain ⟨htL, htR⟩ := ht
  obtain ⟨i, hi_unsafe⟩ := h_no_lonely t
  rw [← mem_unsafeOf_iff] at hi_unsafe
  -- Runner 0 (k=0 gap).
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
  -- Runner 1 (k=0 gap).
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
  -- Runner 2 (k=0 gap).
  have hnot2 : t ∉ unsafeOf speeds ⟨2, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨2, by omega⟩ (hpos _) 0 t
    · rw [show ((0:ℤ):ℝ) + 1/6 = 1/6 from by norm_num, div_div]
      calc (1 : ℝ) / (6 * (speeds ⟨2, by omega⟩ : ℝ))
          ≤ 7 / (6 * v4) := by
            rw [← hv3_def, div_le_div_iff₀ (by positivity) (by positivity)]
            linarith [hv4_lt_6v3, hv3_pos]
        _ ≤ t := htL
    · rw [show ((0:ℤ):ℝ) + 5/6 = 5/6 from by norm_num, div_div]
      exact htR
  -- Runner 3 (k=1 gap).
  have hnot3 : t ∉ unsafeOf speeds ⟨3, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨3, by omega⟩ (hpos _) 1 t
    · rw [show ((1:ℤ):ℝ) + 1/6 = 7/6 from by norm_num, div_div]
      exact htL
    · rw [show ((1:ℤ):ℝ) + 5/6 = 11/6 from by norm_num, div_div]
      calc t ≤ 5 / (6 * v3) := htR
        _ ≤ 11 / (6 * (speeds ⟨3, by omega⟩ : ℝ)) := by
            rw [← hv4_def, div_le_div_iff₀ (by positivity) (by positivity)]
            linarith [hv4_lt_2v3, hv3_pos, hv4_pos]
  fin_cases i
  · exact absurd hi_unsafe hnot0
  · exact absurd hi_unsafe hnot1
  · exact absurd hi_unsafe hnot2
  · exact absurd hi_unsafe hnot3
  · exact hi_unsafe

/-- **§8.2.2 LEFT-strip `j`-extraction.** From the LEFT-strip inclusion
    `[1/(6 v_1), 5/(6 v_4)] ⊆ unsafeOf 5`, extract the 5-block index `j`
    satisfying `(6j-1) v_1 < v_5` and `5 v_5 < (6j+1) v_4`. Requires
    `h822 : v_4 ≤ 5 v_1` (so the strip is non-empty). -/
lemma bhk_case_8_2_2_find_j (speeds : Fin 5 → ℕ)
    (hpos : ∀ i, 0 < speeds i)
    (h822 : speeds ⟨3, by omega⟩ ≤ 5 * speeds ⟨0, by omega⟩)
    (h_incl : Set.Icc (1 / (6 * (speeds ⟨0, by omega⟩ : ℝ)))
                       (5 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
              ⊆ unsafeOf speeds ⟨4, by omega⟩) :
    ∃ j : ℤ,
      (6 * j - 1) * (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ) ∧
      5 * (speeds ⟨4, by omega⟩ : ℤ) < (6 * j + 1) * (speeds ⟨3, by omega⟩ : ℤ) := by
  have hv1 : 0 < speeds ⟨0, by omega⟩ := hpos _
  have hv4 : 0 < speeds ⟨3, by omega⟩ := hpos _
  have hv5 : 0 < speeds ⟨4, by omega⟩ := hpos _
  have hv1R : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hv1
  have hv4R : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hv4
  have h6v1R : (0 : ℝ) < 6 * (speeds ⟨0, by omega⟩ : ℝ) := by positivity
  have h6v4R : (0 : ℝ) < 6 * (speeds ⟨3, by omega⟩ : ℝ) := by positivity
  -- Endpoints a = 1/(6 v_1), b = 5/(6 v_4).
  set a : ℝ := 1 / (6 * (speeds ⟨0, by omega⟩ : ℝ)) with ha_def
  set b : ℝ := 5 / (6 * (speeds ⟨3, by omega⟩ : ℝ)) with hb_def
  -- a ≤ b ⟺ 1/(6 v_1) ≤ 5/(6 v_4) ⟺ v_4 ≤ 5 v_1 (h822).
  have hab : a ≤ b := by
    rw [ha_def, hb_def, div_le_div_iff₀ h6v1R h6v4R]
    have h822R : (speeds ⟨3, by omega⟩ : ℝ) ≤ 5 * (speeds ⟨0, by omega⟩ : ℝ) := by
      exact_mod_cast h822
    linarith
  obtain ⟨j, hk_lo, hk_hi⟩ := block_containment speeds ⟨4, by omega⟩ hv5 a b hab h_incl
  -- Convert v_5 * a, v_5 * b to clean forms.
  have hva_eq : (speeds ⟨4, by omega⟩ : ℝ) * a =
                (speeds ⟨4, by omega⟩ : ℝ) / (6 * (speeds ⟨0, by omega⟩ : ℝ)) := by
    rw [ha_def]; ring
  have hvb_eq : (speeds ⟨4, by omega⟩ : ℝ) * b =
                5 * (speeds ⟨4, by omega⟩ : ℝ) / (6 * (speeds ⟨3, by omega⟩ : ℝ)) := by
    rw [hb_def]; ring
  rw [hva_eq] at hk_lo
  rw [hvb_eq] at hk_hi
  -- Convert to (6j - 1) v_1 < v_5 in ℝ.
  have hjL_R : (6 * (j : ℝ) - 1) * (speeds ⟨0, by omega⟩ : ℝ) <
               (speeds ⟨4, by omega⟩ : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hk_lo h6v1R
    have hclear : ((speeds ⟨4, by omega⟩ : ℝ) / (6 * (speeds ⟨0, by omega⟩ : ℝ))) *
                  (6 * (speeds ⟨0, by omega⟩ : ℝ)) = (speeds ⟨4, by omega⟩ : ℝ) := by
      field_simp
    nlinarith [hmul, hclear]
  -- Convert to 5 v_5 < (6j + 1) v_4 in ℝ.
  have hjR_R : 5 * (speeds ⟨4, by omega⟩ : ℝ) <
               (6 * (j : ℝ) + 1) * (speeds ⟨3, by omega⟩ : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hk_hi h6v4R
    have hclear : (5 * (speeds ⟨4, by omega⟩ : ℝ) / (6 * (speeds ⟨3, by omega⟩ : ℝ))) *
                  (6 * (speeds ⟨3, by omega⟩ : ℝ)) = 5 * (speeds ⟨4, by omega⟩ : ℝ) := by
      field_simp
    nlinarith [hmul, hclear]
  -- Cast to ℤ.
  have hjL : (6 * j - 1) * (speeds ⟨0, by omega⟩ : ℤ) <
             (speeds ⟨4, by omega⟩ : ℤ) := by exact_mod_cast hjL_R
  have hjR : 5 * (speeds ⟨4, by omega⟩ : ℤ) <
             (6 * j + 1) * (speeds ⟨3, by omega⟩ : ℤ) := by exact_mod_cast hjR_R
  exact ⟨j, hjL, hjR⟩

/-- **§8.2.2 RIGHT-strip `k`-extraction.** From the RIGHT-strip inclusion
    `[7/(6 v_4), 5/(6 v_3)] ⊆ unsafeOf 5`, extract the 5-block index `k`
    satisfying `(6k-1) v_4 < 7 v_5` and `5 v_5 < (6k+1) v_3`. Requires
    `h82 : 7 v_3 ≤ 5 v_4` (so the strip is non-empty). Sister to
    `bhk_case_8_2_1_find_j`. -/
lemma bhk_case_8_2_2_find_k (speeds : Fin 5 → ℕ)
    (hpos : ∀ i, 0 < speeds i)
    (h82 : 7 * speeds ⟨2, by omega⟩ ≤ 5 * speeds ⟨3, by omega⟩)
    (h_incl : Set.Icc (7 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
                       (5 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
              ⊆ unsafeOf speeds ⟨4, by omega⟩) :
    ∃ k : ℤ,
      (6 * k - 1) * (speeds ⟨3, by omega⟩ : ℤ) < 7 * (speeds ⟨4, by omega⟩ : ℤ) ∧
      5 * (speeds ⟨4, by omega⟩ : ℤ) < (6 * k + 1) * (speeds ⟨2, by omega⟩ : ℤ) := by
  have hv3 : 0 < speeds ⟨2, by omega⟩ := hpos _
  have hv4 : 0 < speeds ⟨3, by omega⟩ := hpos _
  have hv5 : 0 < speeds ⟨4, by omega⟩ := hpos _
  have hv3R : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hv3
  have hv4R : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hv4
  have h6v3R : (0 : ℝ) < 6 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  have h6v4R : (0 : ℝ) < 6 * (speeds ⟨3, by omega⟩ : ℝ) := by positivity
  set a : ℝ := 7 / (6 * (speeds ⟨3, by omega⟩ : ℝ)) with ha_def
  set b : ℝ := 5 / (6 * (speeds ⟨2, by omega⟩ : ℝ)) with hb_def
  have hab : a ≤ b := by
    rw [ha_def, hb_def, div_le_div_iff₀ h6v4R h6v3R]
    have h82R : 7 * (speeds ⟨2, by omega⟩ : ℝ) ≤ 5 * (speeds ⟨3, by omega⟩ : ℝ) := by
      exact_mod_cast h82
    linarith
  obtain ⟨k, hk_lo, hk_hi⟩ := block_containment speeds ⟨4, by omega⟩ hv5 a b hab h_incl
  have hva_eq : (speeds ⟨4, by omega⟩ : ℝ) * a =
                7 * (speeds ⟨4, by omega⟩ : ℝ) / (6 * (speeds ⟨3, by omega⟩ : ℝ)) := by
    rw [ha_def]; ring
  have hvb_eq : (speeds ⟨4, by omega⟩ : ℝ) * b =
                5 * (speeds ⟨4, by omega⟩ : ℝ) / (6 * (speeds ⟨2, by omega⟩ : ℝ)) := by
    rw [hb_def]; ring
  rw [hva_eq] at hk_lo
  rw [hvb_eq] at hk_hi
  have hkL_R : (6 * (k : ℝ) - 1) * (speeds ⟨3, by omega⟩ : ℝ) <
               7 * (speeds ⟨4, by omega⟩ : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hk_lo h6v4R
    have hclear : (7 * (speeds ⟨4, by omega⟩ : ℝ) / (6 * (speeds ⟨3, by omega⟩ : ℝ))) *
                  (6 * (speeds ⟨3, by omega⟩ : ℝ)) = 7 * (speeds ⟨4, by omega⟩ : ℝ) := by
      field_simp
    nlinarith [hmul, hclear]
  have hkR_R : 5 * (speeds ⟨4, by omega⟩ : ℝ) <
               (6 * (k : ℝ) + 1) * (speeds ⟨2, by omega⟩ : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hk_hi h6v3R
    have hclear : (5 * (speeds ⟨4, by omega⟩ : ℝ) / (6 * (speeds ⟨2, by omega⟩ : ℝ))) *
                  (6 * (speeds ⟨2, by omega⟩ : ℝ)) = 5 * (speeds ⟨4, by omega⟩ : ℝ) := by
      field_simp
    nlinarith [hmul, hclear]
  have hkL : (6 * k - 1) * (speeds ⟨3, by omega⟩ : ℤ) <
             7 * (speeds ⟨4, by omega⟩ : ℤ) := by exact_mod_cast hkL_R
  have hkR : 5 * (speeds ⟨4, by omega⟩ : ℤ) <
             (6 * k + 1) * (speeds ⟨2, by omega⟩ : ℤ) := by exact_mod_cast hkR_R
  exact ⟨k, hkL, hkR⟩

/-- **§8.2.2 arithmetic kernel: force `j = 2, k = 3`.** From the four BHK
    inequalities at indices `(j, k)` plus the §8 entry conditions, derive
    that `j = 2` and `k = 3`. Proof: combine L1+L4+hlarge to get
    `15 j < 9 k + 4`; combine L2+L3 to get `30 k < 42 j + 12`. Together with
    `j ≥ 1, k ≥ 1` (from monotonicity ruling out `j = 0, k = 0`), `omega`
    closes. -/
lemma bhk_case_8_2_2_force_j_k (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hlarge_int : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ))
    (j k : ℤ)
    (hjL : (6 * j - 1) * (speeds ⟨0, by omega⟩ : ℤ) <
              (speeds ⟨4, by omega⟩ : ℤ))
    (hjR : 5 * (speeds ⟨4, by omega⟩ : ℤ) <
              (6 * j + 1) * (speeds ⟨3, by omega⟩ : ℤ))
    (hkL : (6 * k - 1) * (speeds ⟨3, by omega⟩ : ℤ) <
              7 * (speeds ⟨4, by omega⟩ : ℤ))
    (hkR : 5 * (speeds ⟨4, by omega⟩ : ℤ) <
              (6 * k + 1) * (speeds ⟨2, by omega⟩ : ℤ)) :
    j = 2 ∧ k = 3 := by
  have hv1 : (0 : ℤ) < (speeds ⟨0, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  have hv3 : (0 : ℤ) < (speeds ⟨2, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℤ) < (speeds ⟨3, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℤ) < (speeds ⟨4, by omega⟩ : ℤ) := by exact_mod_cast hpos _
  have hv4_le_v5 : (speeds ⟨3, by omega⟩ : ℤ) ≤ (speeds ⟨4, by omega⟩ : ℤ) := by
    exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr (show (3:ℕ) < 4 by omega)))
  have hv3_le_v5 : (speeds ⟨2, by omega⟩ : ℤ) ≤ (speeds ⟨4, by omega⟩ : ℤ) := by
    exact_mod_cast Nat.le_of_lt
      (hmono (Fin.mk_lt_mk.mpr (show (2:ℕ) < 4 by omega)))
  -- (A) From L2 + L3: 30 k < 42 j + 12.
  -- Chain: 5(6k-1) v_4 < 35 v_5 < 7(6j+1) v_4 ⟹ 5(6k-1) < 7(6j+1).
  have stepA1 : 5 * ((6 * k - 1) * (speeds ⟨3, by omega⟩ : ℤ)) <
                5 * (7 * (speeds ⟨4, by omega⟩ : ℤ)) := by linarith
  have stepA2 : 7 * (5 * (speeds ⟨4, by omega⟩ : ℤ)) <
                7 * ((6 * j + 1) * (speeds ⟨3, by omega⟩ : ℤ)) := by linarith
  have hA : 5 * ((6 * k - 1) * (speeds ⟨3, by omega⟩ : ℤ)) <
            7 * ((6 * j + 1) * (speeds ⟨3, by omega⟩ : ℤ)) := by linarith
  have hbound_A : 30 * k < 42 * j + 12 := by nlinarith [hA, hv4]
  -- (B) From L1 + L4 + hlarge: 15 j < 9 k + 4.
  -- Chain: 5(6j-1) v_1 < 5 v_5 < (6k+1) v_3 ≤ 3(6k+1) v_1 ⟹ 5(6j-1) < 3(6k+1).
  have stepB1 : 5 * ((6 * j - 1) * (speeds ⟨0, by omega⟩ : ℤ)) <
                5 * (speeds ⟨4, by omega⟩ : ℤ) := by linarith
  have stepB2 : (6 * k + 1) * (speeds ⟨2, by omega⟩ : ℤ) ≤
                (6 * k + 1) * (3 * (speeds ⟨0, by omega⟩ : ℤ)) := by
    -- Need 6k+1 ≥ 0 to multiply hlarge_int on the left.
    -- Derive 6k+1 > 0 from hkR: 5 v_5 > 0 < (6k+1) v_3 needs 6k+1 > 0 since v_3 > 0.
    have h6kp1_pos : 0 < 6 * k + 1 := by
      by_contra hle
      push_neg at hle
      have h6kp1_le0 : 6 * k + 1 ≤ 0 := by linarith
      have h_prod_nonpos : (6 * k + 1) * (speeds ⟨2, by omega⟩ : ℤ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h6kp1_le0 (le_of_lt hv3)
      linarith [hkR, hv5]
    exact mul_le_mul_of_nonneg_left hlarge_int (le_of_lt h6kp1_pos)
  have hB : 5 * ((6 * j - 1) * (speeds ⟨0, by omega⟩ : ℤ)) <
            (6 * k + 1) * (3 * (speeds ⟨0, by omega⟩ : ℤ)) := by linarith
  have hbound_B : 15 * j < 9 * k + 4 := by nlinarith [hB, hv1]
  -- j ≥ 1: if j ≤ 0 then 6j+1 ≤ 1, so 5 v_5 < (6j+1) v_4 ≤ v_4 ≤ v_5, contradiction.
  have hj_pos : 1 ≤ j := by
    by_contra hjle
    push_neg at hjle
    have hj0 : j ≤ 0 := by linarith
    have h6jp1_le1 : 6 * j + 1 ≤ 1 := by linarith
    -- Case split on sign of 6j+1.
    rcases le_or_gt (6 * j + 1) 0 with hle | hpos
    · -- (6j+1) v_4 ≤ 0 but 5 v_5 > 0 < (6j+1) v_4 by hjR — contradiction.
      have h_prod_nonpos : (6 * j + 1) * (speeds ⟨3, by omega⟩ : ℤ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hle (le_of_lt hv4)
      linarith [hjR, hv5]
    · -- 6j+1 ∈ (0, 1], i.e. 6j+1 = 1 (integer). Then 5 v_5 < v_4 ≤ v_5.
      have h6jp1_eq : 6 * j + 1 = 1 := by linarith
      have hjR' : 5 * (speeds ⟨4, by omega⟩ : ℤ) < (speeds ⟨3, by omega⟩ : ℤ) := by
        have := hjR; rw [h6jp1_eq] at this; linarith
      linarith [hv4_le_v5, hv5]
  -- k ≥ 1: similar argument with L4.
  have hk_pos : 1 ≤ k := by
    by_contra hkle
    push_neg at hkle
    have hk0 : k ≤ 0 := by linarith
    have h6kp1_le1 : 6 * k + 1 ≤ 1 := by linarith
    rcases le_or_gt (6 * k + 1) 0 with hle | hpos
    · have h_prod_nonpos : (6 * k + 1) * (speeds ⟨2, by omega⟩ : ℤ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hle (le_of_lt hv3)
      linarith [hkR, hv5]
    · have h6kp1_eq : 6 * k + 1 = 1 := by linarith
      have hkR' : 5 * (speeds ⟨4, by omega⟩ : ℤ) < (speeds ⟨2, by omega⟩ : ℤ) := by
        have := hkR; rw [h6kp1_eq] at this; linarith
      linarith [hv3_le_v5, hv5]
  -- Apply omega with the bounds.
  -- We have: 30 k < 42 j + 12, 15 j < 9 k + 4, j ≥ 1, k ≥ 1.
  -- Linear integer combination forces (j, k) = (2, 3).
  have hj_le : j ≤ 2 := by
    -- 14 · B + 5 · A gives: 14(15j) + 5(30k) < 14(9k+4) + 5(42j+12)
    -- 210j + 150k < 126k + 56 + 210j + 60, so 24k < 116, k ≤ 4.
    -- 10 · B + 3 · A gives: 150j + 90k < 90k + 40 + 126j + 36, so 24j < 76, j ≤ 3.
    -- For j ≤ 2: 7 · B + 3 · A: 105j + 90k < 63k + 28 + 126j + 36
    -- ⟹ 27k < 21j + 64. Combined with 30k < 42j + 12: hmm not immediate.
    -- Tighter: from B, 15j ≤ 9k + 3. From A, 30k ≤ 42j + 11.
    -- 14 · B (≤): 210j ≤ 126k + 42. 5 · A (≤): 150k ≤ 210j + 55.
    -- Sub: 150k - 210j ≤ 55 - (210j - 126k - 42 = ...). Hmm.
    -- Just try omega directly:
    omega
  have hj_ge : 2 ≤ j := by omega
  have hk_le : k ≤ 3 := by omega
  have hk_ge : 3 ≤ k := by omega
  exact ⟨by omega, by omega⟩

set_option maxHeartbeats 1200000 in
/-- **§8.2.2 first point** `t = 7/(6 v_3)`. Under the (75) bounds
    (`11 v_1 < v_5, 5 v_5 < 13 v_4, 17 v_4 < 7 v_5, 5 v_5 < 19 v_3`) and §8
    entry conditions, the point `t = 7/(6 v_3)` is safe for runners 0, 2, 3, 4.
    By `h_no_lonely`, it must be in `B_2`, giving `5 v_3 < 7 v_2`. -/
lemma bhk_8_2_2_two_point_a (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hlarge_int : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ))
    (h82_int : 7 * (speeds ⟨2, by omega⟩ : ℤ) ≤ 5 * (speeds ⟨3, by omega⟩ : ℤ))
    (h11v1_lt_v5 : 11 * (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ))
    (h5v5_lt_13v4 : 5 * (speeds ⟨4, by omega⟩ : ℤ) < 13 * (speeds ⟨3, by omega⟩ : ℤ))
    (h17v4_lt_7v5 : 17 * (speeds ⟨3, by omega⟩ : ℤ) < 7 * (speeds ⟨4, by omega⟩ : ℤ))
    (h5v5_lt_19v3 : 5 * (speeds ⟨4, by omega⟩ : ℤ) < 19 * (speeds ⟨2, by omega⟩ : ℤ))
    (h_no_lonely : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1/6) :
    5 * (speeds ⟨2, by omega⟩ : ℤ) < 7 * (speeds ⟨1, by omega⟩ : ℤ) := by
  -- Basic positivity and monotonicity facts on the real casts.
  have hv1_pos : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv2_pos : (0 : ℝ) < (speeds ⟨1, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv3_pos : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4_pos : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5_pos : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv1_le_v2 : (speeds ⟨0, by omega⟩ : ℝ) ≤ (speeds ⟨1, by omega⟩ : ℝ) := by
    exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr (show (0:ℕ) < 1 by omega)))
  have hv2_le_v3 : (speeds ⟨1, by omega⟩ : ℝ) ≤ (speeds ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr (show (1:ℕ) < 2 by omega)))
  have hv3_le_v4 : (speeds ⟨2, by omega⟩ : ℝ) ≤ (speeds ⟨3, by omega⟩ : ℝ) := by
    exact_mod_cast Nat.le_of_lt (hmono (Fin.mk_lt_mk.mpr (show (2:ℕ) < 3 by omega)))
  have hv1_le_v3 : (speeds ⟨0, by omega⟩ : ℝ) ≤ (speeds ⟨2, by omega⟩ : ℝ) :=
    le_trans hv1_le_v2 hv2_le_v3
  -- Real versions of integer bounds.
  have hlargeR : (speeds ⟨2, by omega⟩ : ℝ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℝ) := by
    exact_mod_cast hlarge_int
  have h82R : 7 * (speeds ⟨2, by omega⟩ : ℝ) ≤ 5 * (speeds ⟨3, by omega⟩ : ℝ) := by
    exact_mod_cast h82_int
  have h11v1R : 11 * (speeds ⟨0, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    exact_mod_cast h11v1_lt_v5
  have h5v5_13v4_R : 5 * (speeds ⟨4, by omega⟩ : ℝ) < 13 * (speeds ⟨3, by omega⟩ : ℝ) := by
    exact_mod_cast h5v5_lt_13v4
  have h17v4_R : 17 * (speeds ⟨3, by omega⟩ : ℝ) < 7 * (speeds ⟨4, by omega⟩ : ℝ) := by
    exact_mod_cast h17v4_lt_7v5
  have h5v5_19v3_R : 5 * (speeds ⟨4, by omega⟩ : ℝ) < 19 * (speeds ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast h5v5_lt_19v3
  -- The point t = 7/(6 v_3).
  set ta : ℝ := 7 / (6 * (speeds ⟨2, by omega⟩ : ℝ)) with hta_def
  -- Show t_a is safe for runners 0, 2, 3, 4.
  -- Runner 2 (v_3): t_a in k=1 gap [7/(6 v_3), 11/(6 v_3)] — trivially.
  have hnot2 : ta ∉ unsafeOf speeds ⟨2, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨2, by omega⟩ (hpos _) 1 ta
    · rw [show ((1:ℤ):ℝ) + 1/6 = 7/6 from by norm_num, div_div, hta_def]
    · rw [show ((1:ℤ):ℝ) + 5/6 = 11/6 from by norm_num, div_div, hta_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith [hv3_pos]
  -- Runner 0 (v_1): t_a in k=0 gap [1/(6 v_1), 5/(6 v_1)].
  have h7v1_lt_5v3 : 7 * (speeds ⟨0, by omega⟩ : ℝ) < 5 * (speeds ⟨2, by omega⟩ : ℝ) := by
    nlinarith [h11v1R, h5v5_19v3_R, hv1_pos]
  have hnot0 : ta ∉ unsafeOf speeds ⟨0, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨0, by omega⟩ (hpos _) 0 ta
    · rw [show ((0:ℤ):ℝ) + 1/6 = 1/6 from by norm_num, div_div, hta_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hlargeR, hv1_pos, hv3_pos]
    · rw [show ((0:ℤ):ℝ) + 5/6 = 5/6 from by norm_num, div_div, hta_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h7v1_lt_5v3, hv1_pos, hv3_pos]
  -- Runner 3 (v_4): t_a in k=1 gap [7/(6 v_4), 11/(6 v_4)].
  have h7v4_lt_11v3 : 7 * (speeds ⟨3, by omega⟩ : ℝ) < 11 * (speeds ⟨2, by omega⟩ : ℝ) := by
    nlinarith [h17v4_R, h5v5_19v3_R, hv3_pos, hv4_pos]
  have hnot3 : ta ∉ unsafeOf speeds ⟨3, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨3, by omega⟩ (hpos _) 1 ta
    · rw [show ((1:ℤ):ℝ) + 1/6 = 7/6 from by norm_num, div_div, hta_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hv3_le_v4, hv3_pos, hv4_pos]
    · rw [show ((1:ℤ):ℝ) + 5/6 = 11/6 from by norm_num, div_div, hta_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h7v4_lt_11v3, hv3_pos, hv4_pos]
  -- Runner 4 (v_5): t_a in k=4 gap [25/(6 v_5), 29/(6 v_5)].
  have h25v3_lt_7v5 : 25 * (speeds ⟨2, by omega⟩ : ℝ) < 7 * (speeds ⟨4, by omega⟩ : ℝ) := by
    nlinarith [h11v1R, hlargeR, hv1_pos]
  have h7v5_lt_29v3 : 7 * (speeds ⟨4, by omega⟩ : ℝ) < 29 * (speeds ⟨2, by omega⟩ : ℝ) := by
    nlinarith [h5v5_19v3_R, hv3_pos]
  have hnot4 : ta ∉ unsafeOf speeds ⟨4, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨4, by omega⟩ (hpos _) 4 ta
    · rw [show ((4:ℤ):ℝ) + 1/6 = 25/6 from by norm_num, div_div, hta_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h25v3_lt_7v5, hv3_pos, hv5_pos]
    · rw [show ((4:ℤ):ℝ) + 5/6 = 29/6 from by norm_num, div_div, hta_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h7v5_lt_29v3, hv3_pos, hv5_pos]
  -- Apply h_no_lonely at t_a. The unsafe runner is 1 (i.e., v_2).
  obtain ⟨i, hi_unsafe⟩ := h_no_lonely ta
  rw [← mem_unsafeOf_iff] at hi_unsafe
  have hin1 : ta ∈ unsafeOf speeds ⟨1, by omega⟩ := by
    fin_cases i
    · exact absurd hi_unsafe hnot0
    · exact hi_unsafe
    · exact absurd hi_unsafe hnot2
    · exact absurd hi_unsafe hnot3
    · exact absurd hi_unsafe hnot4
  -- Extract: 5 v_3 < 7 v_2 from t_a ∈ B_2.
  rw [mem_unsafeOf_iff_bhkB] at hin1
  obtain ⟨k, hk⟩ := hin1
  -- v_2 · t_a = 7 v_2/(6 v_3).
  have hv2ta_eq : (speeds ⟨1, by omega⟩ : ℝ) * ta =
      7 * (speeds ⟨1, by omega⟩ : ℝ) / (6 * (speeds ⟨2, by omega⟩ : ℝ)) := by
    rw [hta_def]; ring
  rw [hv2ta_eq] at hk
  -- 0 < 7 v_2/(6 v_3) < 7/6.
  have h7v2_pos : 0 < 7 * (speeds ⟨1, by omega⟩ : ℝ) / (6 * (speeds ⟨2, by omega⟩ : ℝ)) := by
    positivity
  have hv2_lt_v3 : (speeds ⟨1, by omega⟩ : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (1:ℕ) < 2 by omega))
  have h7v2_lt : 7 * (speeds ⟨1, by omega⟩ : ℝ) / (6 * (speeds ⟨2, by omega⟩ : ℝ)) < 7/6 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [hv2_lt_v3, hv2_pos, hv3_pos]
  -- So k ∈ {0, 1}.
  have hk_bounds : k = 0 ∨ k = 1 := by
    have habs := abs_lt.mp hk
    obtain ⟨hL, hR⟩ := habs
    have hk_le : (k : ℝ) < 4/3 := by linarith
    have hk_ge : -1/6 < (k : ℝ) := by linarith
    have hk_le1 : k ≤ 1 := by
      by_contra h
      push_neg at h
      have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
      linarith
    have hk_ge0 : 0 ≤ k := by
      by_contra h
      push_neg at h
      have : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
      linarith
    omega
  rcases hk_bounds with hk0 | hk1
  · -- k = 0: would need 7 v_2 < v_3. But v_2 ≥ v_1 ≥ v_3/3, so 7 v_2 ≥ 7 v_3/3 > v_3.
    rw [hk0, Int.cast_zero] at hk
    have habs := abs_lt.mp hk
    obtain ⟨_hL, hR⟩ := habs
    have h_contra : 7 * (speeds ⟨1, by omega⟩ : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by
      have hh : 7 * (speeds ⟨1, by omega⟩ : ℝ) / (6 * (speeds ⟨2, by omega⟩ : ℝ)) < 1/6 := by
        linarith
      rw [div_lt_iff₀ (by positivity)] at hh
      linarith
    have hge : 7 * (speeds ⟨1, by omega⟩ : ℝ) ≥ (speeds ⟨2, by omega⟩ : ℝ) := by
      have hv1_ge : (speeds ⟨2, by omega⟩ : ℝ) / 3 ≤ (speeds ⟨0, by omega⟩ : ℝ) := by
        linarith
      nlinarith [hv1_le_v2, hv1_ge, hv3_pos]
    linarith
  · -- k = 1: derive 5 v_3 < 7 v_2.
    rw [hk1, Int.cast_one] at hk
    have habs := abs_lt.mp hk
    obtain ⟨hL, _hR⟩ := habs
    have h_get : 5/6 <
        7 * (speeds ⟨1, by omega⟩ : ℝ) / (6 * (speeds ⟨2, by omega⟩ : ℝ)) := by
      linarith
    rw [lt_div_iff₀ (by positivity)] at h_get
    have h_real : 5 * (speeds ⟨2, by omega⟩ : ℝ) < 7 * (speeds ⟨1, by omega⟩ : ℝ) := by
      linarith
    exact_mod_cast h_real

set_option maxHeartbeats 1200000 in
/-- **§8.2.2 second point** `t = 21/(12 v_3)`. Under the (75) bounds, §8 entry,
    and the LOWER bound `h_lo : 5 v_3 < 7 v_2` from `bhk_8_2_2_two_point_a`,
    the point `t = 21/(12 v_3)` is safe for runners 1, 3, 4, 5. Runner 2 must
    therefore be unsafe; with k forced to 1 (k=0 ruled out via h_lo), the
    upper-block bound yields `3 v_2 < 2 v_3`.

    Runner k-assignments at t_b = 21/(12 v_3):
    * Runner 1: k=0 [1/(6 v_1), 5/(6 v_1)]
    * Runner 3: k=1 [7/(6 v_3), 11/(6 v_3)]
    * Runner 4: k=2 [13/(6 v_4), 17/(6 v_4)]
    * Runner 5: k=6 [37/(6 v_5), 41/(6 v_5)]

    Combined with `h_lo` (= `5 v_3 < 7 v_2`), the kernel
    `bhk_case_8_2_2_kernel` derives False (15 v_3 < 21 v_2 < 14 v_3). -/
lemma bhk_8_2_2_two_point_b (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hlarge_int : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ))
    (h82_int : 7 * (speeds ⟨2, by omega⟩ : ℤ) ≤ 5 * (speeds ⟨3, by omega⟩ : ℤ))
    (h11v1_lt_v5 : 11 * (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ))
    (h17v4_lt_7v5 : 17 * (speeds ⟨3, by omega⟩ : ℤ) < 7 * (speeds ⟨4, by omega⟩ : ℤ))
    (h5v5_lt_19v3 : 5 * (speeds ⟨4, by omega⟩ : ℤ) < 19 * (speeds ⟨2, by omega⟩ : ℤ))
    (h_lo : 5 * (speeds ⟨2, by omega⟩ : ℤ) < 7 * (speeds ⟨1, by omega⟩ : ℤ))
    (h_no_lonely : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1/6) :
    3 * (speeds ⟨1, by omega⟩ : ℤ) < 2 * (speeds ⟨2, by omega⟩ : ℤ) := by
  -- Positivity & monotonicity on ℝ.
  have hv1_pos : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv2_pos : (0 : ℝ) < (speeds ⟨1, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv3_pos : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4_pos : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5_pos : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv2_lt_v3 : (speeds ⟨1, by omega⟩ : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (1:ℕ) < 2 by omega))
  -- Cast hypotheses to ℝ.
  have hlargeR : (speeds ⟨2, by omega⟩ : ℝ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℝ) := by
    exact_mod_cast hlarge_int
  have h82R : 7 * (speeds ⟨2, by omega⟩ : ℝ) ≤ 5 * (speeds ⟨3, by omega⟩ : ℝ) := by
    exact_mod_cast h82_int
  have h11v1R : 11 * (speeds ⟨0, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    exact_mod_cast h11v1_lt_v5
  have h17v4R : 17 * (speeds ⟨3, by omega⟩ : ℝ) < 7 * (speeds ⟨4, by omega⟩ : ℝ) := by
    exact_mod_cast h17v4_lt_7v5
  have h5v5R : 5 * (speeds ⟨4, by omega⟩ : ℝ) < 19 * (speeds ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast h5v5_lt_19v3
  have h_lo_R : 5 * (speeds ⟨2, by omega⟩ : ℝ) < 7 * (speeds ⟨1, by omega⟩ : ℝ) := by
    exact_mod_cast h_lo
  -- The point t_b = 21/(12 v_3).
  set tb : ℝ := 21 / (12 * (speeds ⟨2, by omega⟩ : ℝ)) with htb_def
  -- Runner 1 (v_1): k=0 gap [1/(6 v_1), 5/(6 v_1)].
  have hnot0 : tb ∉ unsafeOf speeds ⟨0, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨0, by omega⟩ (hpos _) 0 tb
    · rw [show ((0:ℤ):ℝ) + 1/6 = 1/6 from by norm_num, div_div, htb_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 12 v_3 ≤ 6·21 v_1 ⟺ 2 v_3 ≤ 21 v_1; from hlarge.
      nlinarith [hlargeR, hv1_pos]
    · rw [show ((0:ℤ):ℝ) + 5/6 = 5/6 from by norm_num, div_div, htb_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 21·6 v_1 ≤ 12·5 v_3 ⟺ 21 v_1 ≤ 10 v_3; from h11v1 + h5v5_lt_19v3.
      nlinarith [h11v1R, h5v5R, hv1_pos]
  -- Runner 3 (v_3): k=1 gap [7/(6 v_3), 11/(6 v_3)] — both endpoints trivial.
  have hnot2 : tb ∉ unsafeOf speeds ⟨2, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨2, by omega⟩ (hpos _) 1 tb
    · rw [show ((1:ℤ):ℝ) + 1/6 = 7/6 from by norm_num, div_div, htb_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith [hv3_pos]
    · rw [show ((1:ℤ):ℝ) + 5/6 = 11/6 from by norm_num, div_div, htb_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith [hv3_pos]
  -- Runner 4 (v_4): k=2 gap [13/(6 v_4), 17/(6 v_4)].
  have hnot3 : tb ∉ unsafeOf speeds ⟨3, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨3, by omega⟩ (hpos _) 2 tb
    · rw [show ((2:ℤ):ℝ) + 1/6 = 13/6 from by norm_num, div_div, htb_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 13·12 v_3 ≤ 21·6 v_4 ⟺ 26 v_3 ≤ 21 v_4; from h82 (7 v_3 ≤ 5 v_4).
      nlinarith [h82R, hv3_pos, hv4_pos]
    · rw [show ((2:ℤ):ℝ) + 5/6 = 17/6 from by norm_num, div_div, htb_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 21·6 v_4 ≤ 17·12 v_3 ⟺ 21 v_4 ≤ 34 v_3; from h17v4 + h5v5_lt_19v3.
      nlinarith [h17v4R, h5v5R, hv3_pos, hv4_pos, hv5_pos]
  -- Runner 5 (v_5): k=6 gap [37/(6 v_5), 41/(6 v_5)].
  have hnot4 : tb ∉ unsafeOf speeds ⟨4, by omega⟩ := by
    apply not_mem_unsafeOf_of_in_gap speeds ⟨4, by omega⟩ (hpos _) 6 tb
    · rw [show ((6:ℤ):ℝ) + 1/6 = 37/6 from by norm_num, div_div, htb_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 37·12 v_3 ≤ 21·6 v_5 ⟺ 74 v_3 ≤ 21 v_5; from h11v1 + hlarge.
      nlinarith [h11v1R, hlargeR, hv1_pos, hv5_pos]
    · rw [show ((6:ℤ):ℝ) + 5/6 = 41/6 from by norm_num, div_div, htb_def]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      -- 21·6 v_5 ≤ 41·12 v_3 ⟺ 21 v_5 ≤ 82 v_3; from h5v5_lt_19v3.
      nlinarith [h5v5R, hv3_pos, hv5_pos]
  -- Apply h_no_lonely at t_b. The unsafe runner is 1 (i.e., v_2).
  obtain ⟨i, hi_unsafe⟩ := h_no_lonely tb
  rw [← mem_unsafeOf_iff] at hi_unsafe
  have hin1 : tb ∈ unsafeOf speeds ⟨1, by omega⟩ := by
    fin_cases i
    · exact absurd hi_unsafe hnot0
    · exact hi_unsafe
    · exact absurd hi_unsafe hnot2
    · exact absurd hi_unsafe hnot3
    · exact absurd hi_unsafe hnot4
  -- Extract: 3 v_2 < 2 v_3 from t_b ∈ B_2.
  rw [mem_unsafeOf_iff_bhkB] at hin1
  obtain ⟨k, hk⟩ := hin1
  -- v_2 · t_b = 21 v_2/(12 v_3) = 7 v_2/(4 v_3).
  have hv2tb_eq : (speeds ⟨1, by omega⟩ : ℝ) * tb =
      21 * (speeds ⟨1, by omega⟩ : ℝ) / (12 * (speeds ⟨2, by omega⟩ : ℝ)) := by
    rw [htb_def]; ring
  rw [hv2tb_eq] at hk
  -- 0 < 21 v_2/(12 v_3) < 7/4 (strict v_2 < v_3 ⟹ 21 v_2 < 21 v_3 ⟹ 21 v_2/(12 v_3) < 21/12 = 7/4).
  have h_quot_pos : 0 < 21 * (speeds ⟨1, by omega⟩ : ℝ) / (12 * (speeds ⟨2, by omega⟩ : ℝ)) := by
    positivity
  have h_quot_lt : 21 * (speeds ⟨1, by omega⟩ : ℝ) / (12 * (speeds ⟨2, by omega⟩ : ℝ)) < 7/4 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [hv2_lt_v3, hv2_pos, hv3_pos]
  -- k ∈ {0, 1}.
  have hk_bounds : k = 0 ∨ k = 1 := by
    have habs := abs_lt.mp hk
    obtain ⟨hL, hR⟩ := habs
    have hk_le_R : (k : ℝ) < 7/4 + 1/6 := by linarith
    have hk_ge_R : -1/6 < (k : ℝ) := by linarith
    have hk_le1 : k ≤ 1 := by
      by_contra h
      push_neg at h
      have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
      linarith
    have hk_ge0 : 0 ≤ k := by
      by_contra h
      push_neg at h
      have : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
      linarith
    omega
  rcases hk_bounds with hk0 | hk1
  · -- k = 0: would need 21 v_2 < 2 v_3. But h_lo: 5 v_3 < 7 v_2 ⟹ 15 v_3 < 21 v_2.
    rw [hk0, Int.cast_zero] at hk
    have habs := abs_lt.mp hk
    obtain ⟨_hL, hR⟩ := habs
    -- 21 v_2/(12 v_3) < 1/6 ⟺ 21 v_2 < 2 v_3.
    have h_contra : 21 * (speeds ⟨1, by omega⟩ : ℝ) < 2 * (speeds ⟨2, by omega⟩ : ℝ) := by
      have hh : 21 * (speeds ⟨1, by omega⟩ : ℝ) / (12 * (speeds ⟨2, by omega⟩ : ℝ)) < 1/6 := by
        linarith
      rw [div_lt_iff₀ (by positivity)] at hh
      linarith
    -- h_lo_R: 5 v_3 < 7 v_2 ⟹ 15 v_3 < 21 v_2. Combine with h_contra.
    linarith [h_lo_R, h_contra]
  · -- k = 1: 21 v_2/(12 v_3) - 1 < 1/6 ⟺ 21 v_2 < 14 v_3 ⟺ 3 v_2 < 2 v_3.
    rw [hk1, Int.cast_one] at hk
    have habs := abs_lt.mp hk
    obtain ⟨_hL, hR⟩ := habs
    have h_get : 21 * (speeds ⟨1, by omega⟩ : ℝ) / (12 * (speeds ⟨2, by omega⟩ : ℝ)) < 7/6 := by
      linarith
    rw [div_lt_iff₀ (by positivity)] at h_get
    have h_real : 3 * (speeds ⟨1, by omega⟩ : ℝ) < 2 * (speeds ⟨2, by omega⟩ : ℝ) := by
      linarith
    exact_mod_cast h_real

/-- **BHK §8.2.2.** Sub-case of `x_1 ≤ 3` with `x_4 ≤ 5/7` (de-normalised:
    `7 * speeds ⟨2⟩ ≤ 5 * speeds ⟨3⟩`) AND `x_1 ≤ 5 x_4` (de-normalised:
    `speeds ⟨3⟩ ≤ 5 * speeds ⟨0⟩`). See BHK p47–48. -/
theorem bhk_case_8_2_2 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hlarge : speeds ⟨2, by omega⟩ ≤ 3 * speeds ⟨0, by omega⟩)
    (h82 : 7 * speeds ⟨2, by omega⟩ ≤ 5 * speeds ⟨3, by omega⟩)
    (h822 : speeds ⟨3, by omega⟩ ≤ 5 * speeds ⟨0, by omega⟩) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  by_contra h_no_lonely
  push_neg at h_no_lonely
  -- Cast hypotheses to ℤ.
  have hlarge_int : (speeds ⟨2, by omega⟩ : ℤ) ≤ 3 * (speeds ⟨0, by omega⟩ : ℤ) := by
    exact_mod_cast hlarge
  have h82_int : 7 * (speeds ⟨2, by omega⟩ : ℤ) ≤ 5 * (speeds ⟨3, by omega⟩ : ℤ) := by
    exact_mod_cast h82
  -- LEFT-strip inclusion → find_j.
  have h_left_incl := bhk_8_2_2_left_strip_incl speeds hmono hpos h_no_lonely
  obtain ⟨j, hjL, hjR⟩ := bhk_case_8_2_2_find_j speeds hpos h822 h_left_incl
  -- RIGHT-strip inclusion → find_k.
  have h_right_incl := bhk_8_2_right_strip_incl speeds hmono hpos hlarge h_no_lonely
  obtain ⟨k, hkL, hkR⟩ := bhk_case_8_2_2_find_k speeds hpos h82 h_right_incl
  -- Force j = 2, k = 3.
  obtain ⟨hj_eq, hk_eq⟩ :=
    bhk_case_8_2_2_force_j_k speeds hmono hpos hlarge_int j k hjL hjR hkL hkR
  subst hj_eq
  subst hk_eq
  -- Now substitute back to obtain (75) bounds.
  have h11v1_lt_v5 : 11 * (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ) := by
    linarith [hjL]
  have h5v5_lt_13v4 : 5 * (speeds ⟨4, by omega⟩ : ℤ) < 13 * (speeds ⟨3, by omega⟩ : ℤ) := by
    linarith [hjR]
  have h17v4_lt_7v5 : 17 * (speeds ⟨3, by omega⟩ : ℤ) < 7 * (speeds ⟨4, by omega⟩ : ℤ) := by
    linarith [hkL]
  have h5v5_lt_19v3 : 5 * (speeds ⟨4, by omega⟩ : ℤ) < 19 * (speeds ⟨2, by omega⟩ : ℤ) := by
    linarith [hkR]
  -- two_point_a → h_lo (5 v_3 < 7 v_2).
  have h_lo := bhk_8_2_2_two_point_a speeds hmono hpos hlarge_int h82_int
                                      h11v1_lt_v5 h5v5_lt_13v4 h17v4_lt_7v5 h5v5_lt_19v3
                                      h_no_lonely
  -- two_point_b → h_up (3 v_2 < 2 v_3).
  have h_up := bhk_8_2_2_two_point_b speeds hmono hpos hlarge_int h82_int
                                      h11v1_lt_v5 h17v4_lt_7v5 h5v5_lt_19v3 h_lo
                                      h_no_lonely
  -- Apply kernel.
  exact bhk_case_8_2_2_kernel speeds hpos h_lo h_up

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
    · by_cases ht0 : Int.fract ((speeds ⟨2, by omega⟩ : ℝ) * t₀) = 0
      · exact bhk_case_t0_zero speeds hmono hpos hgcd hlarge ht0 hv1t0
      · exact bhk_case_v1_small_generic speeds hmono hpos hgcd hlarge ht0 hv1t0

end BHK

/-- Exported alias: the integer-speed n=6 Hard Case theorem.
    Cited from `IntLRC_6.lean`. -/
theorem intLRC_six_hard (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 :=
  BHK.bhk_theorem_2 speeds hmono hpos hgcd
