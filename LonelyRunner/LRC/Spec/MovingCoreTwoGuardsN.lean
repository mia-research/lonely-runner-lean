import LonelyRunner.LRC.Spec.MovingCoreFallbackN

/-!
# Reduce the changed-lap replacement to two guards

The setters are now identified with their core readings: c=d₂, e=d₃,
b=d₅. Beyond the old rescue face, all the new fallback inequalities
follow from the original windows except two closing-edge conditions.
This does not assume that those final two conditions always hold.
-/

namespace LRC.MovingCoreTwoGuards

open MovingCoreWindows

theorem derived_guards (d : Fin 6 → ℝ) {b c e : ℝ}
    (hb7 : b ≤ 7) (he : 101 / 20 ≤ e) (hface : 1953 * c ≤ 1105 * b)
    (hc : d 2 = c) (heq : d 3 = e) (hb : d 5 = b)
    (hlo : ∀ w i, (8 * (laps w i : ℝ) + 1) * setter c e w ≤ opening w * d i)
    (hhi : ∀ w i, closing w * d i ≤ (8 * (laps w i : ℝ) + 7) * b)
    (ha : 49 * d 1 ≤ 31 * e) (hf : 49 * d 4 ≤ 63 * e) :
    1105 * e ≤ 1519 * c ∧ 2401 * b ≤ 3337 * e ∧
    (∀ i, (8 * (MovingCoreFallback.laps i : ℝ) + 1) * e ≤ 49 * d i) ∧
    (∀ i, 49 * d i ≤ (8 * (MovingCoreFallback.laps i : ℝ) + 7) * e) := by
  change d ⟨2, by decide⟩ = c at hc
  change d ⟨3, by decide⟩ = e at heq
  change d ⟨5, by decide⟩ = b at hb
  change 49 * d ⟨1, by decide⟩ ≤ 31 * e at ha
  change 49 * d ⟨4, by decide⟩ ≤ 63 * e at hf
  have heu := hhi ⟨3, by decide⟩ ⟨3, by decide⟩
  have hcl := hlo ⟨2, by decide⟩ ⟨2, by decide⟩
  norm_num [laps, setter, opening, closing, hc, heq] at heu hcl
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · intro i
    have hl := hlo ⟨3, by decide⟩ i
    fin_cases i <;>
      norm_num [laps, setter, opening, closing, MovingCoreFallback.laps, hc, heq, hb] at hl ⊢ <;>
      first | exact ha | exact hf | linarith
  · intro i
    have hu := hhi ⟨2, by decide⟩ i
    fin_cases i <;>
      norm_num [laps, setter, opening, closing, MovingCoreFallback.laps, hc, heq, hb] at hu ⊢ <;>
      first | exact ha | exact hf | linarith

/-- Only the two unforced closing edges remain as additional hypotheses. -/
theorem family_isolated (d : Fin 6 → ℝ) {b c e V : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hb7 : b ≤ 7) (he : 101 / 20 ≤ e)
    (hcross : 51 * b ≤ 91 * c) (hface : 1953 * c ≤ 1105 * b)
    (hV : b ≤ V) (hd : ∀ i, 0 < d i)
    (hcEq : d 2 = c) (heEq : d 3 = e) (hbEq : d 5 = b)
    (hlo : ∀ w i, (8 * (laps w i : ℝ) + 1) * setter c e w ≤ opening w * d i)
    (hhi : ∀ w i, closing w * d i ≤ (8 * (laps w i : ℝ) + 7) * b)
    (ha : 49 * d 1 ≤ 31 * e) (hf : 49 * d 4 ≤ 63 * e) :
    ∃ t : ℝ, 0 < t ∧ (8 : ℝ)⁻¹ ≤ circDist (V * t) ∧
      ∀ i, (8 : ℝ)⁻¹ ≤ circDist (d i * t) := by
  obtain ⟨hce, hbe, hfl, hfu⟩ := derived_guards d hb7 he hface hcEq heEq hbEq hlo hhi ha hf
  exact MovingCoreFallback.family_isolated d hb hc hb7 he hcross hV hd hlo hhi hce hbe hfl hfu

/-- The fifth core reading has already left its next capture zone. -/
def laterLaps : Fin 6 → ℤ := ![1, 3, 4, 6, 8, 8]

theorem later_derived_guards (d : Fin 6 → ℝ) {b c e : ℝ}
    (hb7 : b ≤ 7) (he : 101 / 20 ≤ e) (hface : 1953 * c ≤ 1105 * b)
    (hc : d 2 = c) (heq : d 3 = e) (hb : d 5 = b)
    (hlo : ∀ w i, (8 * (laps w i : ℝ) + 1) * setter c e w ≤ opening w * d i)
    (hhi : ∀ w i, closing w * d i ≤ (8 * (laps w i : ℝ) + 7) * b)
    (ha : 49 * d 1 ≤ 31 * e) (hf : 65 * e ≤ 49 * d 4) :
    1105 * e ≤ 1519 * c ∧ 2401 * b ≤ 3337 * e ∧
    (∀ i, (8 * (laterLaps i : ℝ) + 1) * e ≤ 49 * d i) ∧
    (∀ i, 49 * d i ≤ (8 * (laterLaps i : ℝ) + 7) * e) := by
  change d ⟨2, by decide⟩ = c at hc
  change d ⟨3, by decide⟩ = e at heq
  change d ⟨5, by decide⟩ = b at hb
  change 49 * d ⟨1, by decide⟩ ≤ 31 * e at ha
  change 65 * e ≤ 49 * d ⟨4, by decide⟩ at hf
  have heu := hhi ⟨3, by decide⟩ ⟨3, by decide⟩
  have hcl := hlo ⟨2, by decide⟩ ⟨2, by decide⟩
  norm_num [laps, setter, opening, closing, hc, heq] at heu hcl
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · intro i
    have hl := hlo ⟨3, by decide⟩ i
    fin_cases i <;>
      norm_num [laps, setter, opening, closing, laterLaps, hc, heq, hb] at hl ⊢ <;>
      first | exact ha | exact hf | linarith
  · intro i
    have hu := hhi ⟨2, by decide⟩ i
    have hu0 := hhi ⟨0, by decide⟩ i
    fin_cases i <;>
      norm_num [laps, setter, opening, closing, laterLaps, hc, heq, hb] at hu hu0 ⊢ <;>
      first | exact ha | exact hf | linarith

/-- The same named instant also covers the far side of the fifth reading's
capture strip; failing its old closing guard need not lose isolation. -/
theorem family_isolated_later (d : Fin 6 → ℝ) {b c e V : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hb7 : b ≤ 7) (he : 101 / 20 ≤ e)
    (hcross : 51 * b ≤ 91 * c) (hface : 1953 * c ≤ 1105 * b)
    (hV : b ≤ V) (hd : ∀ i, 0 < d i)
    (hcEq : d 2 = c) (heEq : d 3 = e) (hbEq : d 5 = b)
    (hlo : ∀ w i, (8 * (laps w i : ℝ) + 1) * setter c e w ≤ opening w * d i)
    (hhi : ∀ w i, closing w * d i ≤ (8 * (laps w i : ℝ) + 7) * b)
    (ha : 49 * d 1 ≤ 31 * e) (hf : 65 * e ≤ 49 * d 4) :
    ∃ t : ℝ, 0 < t ∧ (8 : ℝ)⁻¹ ≤ circDist (V * t) ∧
      ∀ i, (8 : ℝ)⁻¹ ≤ circDist (d i * t) := by
  obtain ⟨hce, hbe, hfl, hfu⟩ := later_derived_guards d hb7 he hface hcEq heEq hbEq hlo hhi ha hf
  apply MovingCoreWindows.family_isolated_of_residual d hb hc hb7 he hcross hV hd hlo hhi
  intro hvlo hvhi
  have hep : 0 < e := by linarith
  refine ⟨(49 / e) / 8, by positivity,
    MovingCoreFallback.residual_clear hep hce hbe hvlo hvhi, ?_⟩
  intro i
  have hl : 8 * (laterLaps i : ℝ) + 1 ≤ d i * (49 / e) := by
    rw [← mul_div_assoc, le_div_iff₀ hep]
    nlinarith [hfl i]
  have hu : d i * (49 / e) ≤ 8 * (laterLaps i : ℝ) + 7 := by
    rw [← mul_div_assoc, div_le_iff₀ hep]
    nlinarith [hfu i]
  apply TwoPinner.clear_of_band (N := laterLaps i) <;> nlinarith

/-- Exhaustive branch reduction within the supplied moving-core region.
Either isolation is proved, or the two remaining obstruction branches are
named explicitly. This is not an exhaustive classification of all cores. -/
theorem isolation_or_two_obstructions (d : Fin 6 → ℝ) {b c e V : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hb7 : b ≤ 7) (he : 101 / 20 ≤ e)
    (hcross : 51 * b ≤ 91 * c) (hface : 1953 * c ≤ 1105 * b)
    (hV : b ≤ V) (hd : ∀ i, 0 < d i)
    (hcEq : d 2 = c) (heEq : d 3 = e) (hbEq : d 5 = b)
    (hlo : ∀ w i, (8 * (laps w i : ℝ) + 1) * setter c e w ≤ opening w * d i)
    (hhi : ∀ w i, closing w * d i ≤ (8 * (laps w i : ℝ) + 7) * b) :
    (∃ t : ℝ, 0 < t ∧ (8 : ℝ)⁻¹ ≤ circDist (V * t) ∧
      ∀ i, (8 : ℝ)⁻¹ ≤ circDist (d i * t)) ∨
    (31 * e < 49 * d 1 ∨ (63 * e < 49 * d 4 ∧ 49 * d 4 < 65 * e)) := by
  by_cases ha : 49 * d 1 ≤ 31 * e
  · by_cases hf : 49 * d 4 ≤ 63 * e
    · exact Or.inl (family_isolated d hb hc hb7 he hcross hface hV hd
        hcEq heEq hbEq hlo hhi ha hf)
    · by_cases hfl : 65 * e ≤ 49 * d 4
      · exact Or.inl (family_isolated_later d hb hc hb7 he hcross hface hV hd
          hcEq heEq hbEq hlo hhi ha hfl)
      · exact Or.inr (Or.inr ⟨lt_of_not_ge hf, lt_of_not_ge hfl⟩)
  · exact Or.inr (Or.inl (lt_of_not_ge ha))

end LRC.MovingCoreTwoGuards
