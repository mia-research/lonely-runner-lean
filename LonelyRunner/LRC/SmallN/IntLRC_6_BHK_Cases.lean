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

    * 1234-gap analysis → (65) `5 x_5 < x_1`
    * 123-gap `[13/6, 5 x_1/6]` → (70) `5 x_1 < 19 x_4`
    * 1235-gap `[37 x_5/6, 23/6]` → (71) `29 x_4 < 37 x_5`

    These three contradict via `bhk_case_8_1_1_kernel`. -/
theorem bhk_case_8_1_1 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hlarge : speeds ⟨2, by omega⟩ ≤ 3 * speeds ⟨0, by omega⟩)
    (h81 : 5 * speeds ⟨3, by omega⟩ < 7 * speeds ⟨2, by omega⟩)
    (h811 : 13 * speeds ⟨1, by omega⟩ ≤ 7 * speeds ⟨3, by omega⟩) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  by_contra h_no_lonely
  push_neg at h_no_lonely
  -- STRUCTURAL SORRY: from h_no_lonely + case hypotheses, derive BHK's
  -- (65), (70b), (71b) — the three gap analyses on p46.
  obtain ⟨h65, h70b, h71b⟩ :
      (5 * (speeds ⟨0, by omega⟩ : ℤ) < (speeds ⟨4, by omega⟩ : ℤ)) ∧
      (5 * (speeds ⟨3, by omega⟩ : ℤ) < 19 * (speeds ⟨0, by omega⟩ : ℤ)) ∧
      (29 * (speeds ⟨4, by omega⟩ : ℤ) < 37 * (speeds ⟨3, by omega⟩ : ℤ)) := by
    sorry
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
  -- STRUCTURAL SORRY (now narrowed): the BHK §8.2.1 geometric inclusion
  -- [7/(6 v_4), 5/(6 v_3)] ⊆ unsafeOf 5, derived from h_no_lonely + 123-gap
  -- argument + case 8.2.1's `5 x_4 < x_1` ruling out 4-block coverage.
  have h_incl : Set.Icc (7 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
                         (5 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
                ⊆ unsafeOf speeds ⟨4, by omega⟩ := by
    sorry
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
