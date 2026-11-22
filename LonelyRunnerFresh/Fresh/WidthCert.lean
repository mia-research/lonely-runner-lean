import Mathlib.Tactic
import Fresh.K6BandUnion

/-!
# The width certificate: the closed-form column-death lemma

From `Band p s j` (`(8j−1)/p.1 ≤ s ∧ s < (8j+1)/p.2`), multiplying out gives
`s·(p.2 − p.1) < 2`: a reader can cover the component only if its speed times the
component's WIDTH stays under 2.  Hence width ≥ 2/S kills the component for every
s ≥ S — one lemma, all columns, all scales, no race quantities, no lap enumeration.
-/

namespace Fresh.WidthCert

/-- **The width lemma (master form).** -/
theorem no_band_of_width (p : ℚ × ℚ) (hp1 : 0 < p.1) (hp2 : 0 < p.2)
    (S : ℚ) (hS : 0 < S) (hw : 2 / S ≤ p.2 - p.1)
    (s : ℚ) (hs : S ≤ s) (j : ℕ)
    (hb : (8 * (j:ℚ) - 1) / p.1 ≤ s ∧ s < (8 * (j:ℚ) + 1) / p.2) : False := by
  have h1 : (8 * (j:ℚ) - 1) ≤ s * p.1 := (div_le_iff₀ hp1).mp hb.1
  have h2 : s * p.2 < (8 * (j:ℚ) + 1) := (lt_div_iff₀ hp2).mp hb.2
  have hdiff : s * (p.2 - p.1) = s * p.2 - s * p.1 := by ring
  have hsub : s * (p.2 - p.1) < 2 := by rw [hdiff]; linarith
  have h2pos : (0:ℚ) < 2 / S := div_pos (by norm_num : (0:ℚ) < 2) hS
  have hS0 : (0:ℚ) ≤ S := le_of_lt hS
  have hwp0 : (0:ℚ) ≤ p.2 - p.1 := (le_of_lt h2pos).trans hw
  have hs0 : (0:ℚ) ≤ S := le_of_lt hS
  have hfact : (2:ℚ)/S * S ≤ (p.2 - p.1) * s := mul_le_mul hw hs hS0 hwp0
  have hcomm : (p.2 - p.1) * s = s * (p.2 - p.1) := mul_comm _ _
  have h6 : (2:ℚ) = (2:ℚ)/S * S := by field_simp
  linarith [hsub, hcomm, hfact, h6]

/-- **The [25,50) column corollary** — width ≥ 2/25 gives `ColDead`. -/
theorem colDead_of_width (p : ℚ × ℚ) (hp1 : 0 < p.1) (hp2 : 0 < p.2)
    (hw : (2:ℚ) / 25 ≤ p.2 - p.1) : Fresh.K6BandUnion.ColDead p := by
  intro s hs h50 j hb
  exact no_band_of_width p hp1 hp2 (25:ℚ) (by norm_num) hw s hs j hb

/-- **The datasheet form** — width ≥ 2/25 gives `ColDead50`'s content. -/
theorem colDead50_of_width (p : ℚ × ℚ) (hp1 : 0 < p.1) (hp2 : 0 < p.2)
    (hw : (2:ℚ) / 25 ≤ p.2 - p.1) :
    ∀ s : ℚ, 25 ≤ s → s < 50 → ∀ j : ℕ,
      ¬ ((8 * (j:ℚ) - 1) / p.1 ≤ s ∧ s < (8 * (j:ℚ) + 1) / p.2) := by
  intro s hs h50 j hb
  exact no_band_of_width p hp1 hp2 (25:ℚ) (by norm_num) hw s hs j hb

/-- **The column extension at S = 50** — width ≥ 1/25 kills the [50,∞) column. -/
theorem colDead_of_width_50 (p : ℚ × ℚ) (hp1 : 0 < p.1) (hp2 : 0 < p.2)
    (hw : (1:ℚ) / 25 ≤ p.2 - p.1)
    (s : ℚ) (hs : 50 ≤ s) (j : ℕ)
    (hb : (8 * (j:ℚ) - 1) / p.1 ≤ s ∧ s < (8 * (j:ℚ) + 1) / p.2) : False := by
  have h1 : (8 * (j:ℚ) - 1) ≤ s * p.1 := (div_le_iff₀ hp1).mp hb.1
  have h2 : s * p.2 < (8 * (j:ℚ) + 1) := (lt_div_iff₀ hp2).mp hb.2
  have hdiff : s * (p.2 - p.1) = s * p.2 - s * p.1 := by ring
  have hsub : s * (p.2 - p.1) < 2 := by rw [hdiff]; linarith
  have h25pos : (0:ℚ) < 1 / 25 := by positivity
  have hw0 : (0:ℚ) ≤ p.2 - p.1 := (le_of_lt h25pos).trans hw
  have h50lt : (0:ℚ) < 50 := by norm_num
  have hs0 : (0:ℚ) ≤ 50 := le_of_lt h50lt
  have hfact : (1:ℚ)/25 * 50 ≤ (p.2 - p.1) * s := mul_le_mul hw hs (le_of_lt h50lt) hw0
  have hcomm : (p.2 - p.1) * s = s * (p.2 - p.1) := mul_comm _ _
  have htwo : (2:ℚ) = (1:ℚ)/25 * 50 := by norm_num
  linarith [hsub, hcomm, hfact, htwo]

end Fresh.WidthCert

#print axioms Fresh.WidthCert.no_band_of_width
#print axioms Fresh.WidthCert.colDead_of_width
#print axioms Fresh.WidthCert.colDead50_of_width
#print axioms Fresh.WidthCert.colDead_of_width_50
