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

/-- **BHK §8.1.1.** Sub-case of `x_1 ≤ 3` with `x_4 > 5/7` (de-normalised:
    `5 v_3 < 7 v_2`, since BHK uses `x_3 = 1`, i.e. `5 * speeds ⟨3⟩ < 7 * speeds ⟨2⟩`)
    AND `13 x_4 ≤ 7 x_2` (de-normalised: `13 v_2 ≤ 7 v_4`, i.e.
    `13 * speeds ⟨1⟩ ≤ 7 * speeds ⟨3⟩`). See BHK p46. -/
theorem bhk_case_8_1_1 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hlarge : speeds ⟨2, by omega⟩ ≤ 3 * speeds ⟨0, by omega⟩)
    (h81 : 5 * speeds ⟨3, by omega⟩ < 7 * speeds ⟨2, by omega⟩)
    (h811 : 13 * speeds ⟨1, by omega⟩ ≤ 7 * speeds ⟨3, by omega⟩) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  sorry

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

/-- **BHK §8.2.1.** Sub-case of `x_1 ≤ 3` with `x_4 ≤ 5/7` (de-normalised:
    `7 * speeds ⟨2⟩ ≤ 5 * speeds ⟨3⟩`) AND `5 x_4 < x_1` (de-normalised:
    `5 * speeds ⟨0⟩ < speeds ⟨3⟩`). See BHK p47. -/
theorem bhk_case_8_2_1 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hlarge : speeds ⟨2, by omega⟩ ≤ 3 * speeds ⟨0, by omega⟩)
    (h82 : 7 * speeds ⟨2, by omega⟩ ≤ 5 * speeds ⟨3, by omega⟩)
    (h821 : 5 * speeds ⟨0, by omega⟩ < speeds ⟨3, by omega⟩) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  sorry

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
