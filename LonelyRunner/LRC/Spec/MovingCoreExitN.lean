import LonelyRunner.LRC.Spec.MovingCoreTwoGuardsN

/-!
# Replacement exits for the two remaining core obstructions

These are derived subregions of the original moving-core family. They do
not assert that every core satisfies the new guards, or that the named
isolation is the first cascade landing.
-/
namespace LRC.MovingCoreExit
open MovingCoreWindows

theorem clear_at_exit (d : Fin 6 → ℝ) (q : Fin 6 → ℤ) {A P : ℝ}
    (hP : 0 < P)
    (hl : ∀ i, (8 * (q i : ℝ) + 1) * P ≤ A * d i)
    (hu : ∀ i, A * d i ≤ (8 * (q i : ℝ) + 7) * P) :
    ∀ i, (8 : ℝ)⁻¹ ≤ circDist (d i * ((A / P) / 8)) := by
  intro i
  have hL : 8 * (q i : ℝ) + 1 ≤ d i * (A / P) := by
    rw [← mul_div_assoc, le_div_iff₀ hP]
    nlinarith [hl i]
  have hU : d i * (A / P) ≤ 8 * (q i : ℝ) + 7 := by
    rw [← mul_div_assoc, div_le_iff₀ hP]
    nlinarith [hu i]
  apply TwoPinner.clear_of_band (N := q i) <;> nlinarith

def cLaps : Fin 6 → ℤ := ![1, 4, 5, 6, 8, 9]

/-- The second-reading obstruction is carried to c's next opening, 41/c.
Only the b opening and f closing remain as extra core guards. -/
theorem c_guards (d : Fin 6 → ℝ) {b c e : ℝ}
    (hb7 : b ≤ 7) (he : 101 / 20 ≤ e)
    (hcross : 51 * b ≤ 91 * c) (hface : 1953 * c ≤ 1105 * b)
    (hc : d 2 = c) (heq : d 3 = e) (hb : d 5 = b)
    (hlo : ∀ w i, (8 * (laps w i : ℝ) + 1) * setter c e w ≤ opening w * d i)
    (hhi : ∀ w i, closing w * d i ≤ (8 * (laps w i : ℝ) + 7) * b)
    (ha : 31 * e ≤ 49 * d 1) (hbc : 73 * c ≤ 41 * b)
    (hf : 41 * d 4 ≤ 71 * c) :
    (∀ i, (8 * (cLaps i : ℝ) + 1) * c ≤ 41 * d i) ∧
    (∀ i, 41 * d i ≤ (8 * (cLaps i : ℝ) + 7) * c) := by
  change d ⟨2, by decide⟩ = c at hc
  change d ⟨3, by decide⟩ = e at heq
  change d ⟨5, by decide⟩ = b at hb
  have heu := hhi ⟨3, by decide⟩ ⟨3, by decide⟩
  norm_num [laps, closing, heq] at heu
  constructor
  · intro i
    have hl := hlo ⟨3, by decide⟩ i
    fin_cases i <;> norm_num [laps, setter, opening, cLaps, hc, heq, hb] at hl ⊢ <;>
      first | exact hbc | linarith
  · intro i
    have hu := hhi ⟨1, by decide⟩ i
    have hu2 := hhi ⟨2, by decide⟩ i
    fin_cases i <;> norm_num [laps, closing, cLaps, hc, heq, hb] at hu hu2 ⊢ <;>
      first | exact hf | linarith

theorem c_family (d : Fin 6 → ℝ) {b c e V : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hb7 : b ≤ 7) (he : 101 / 20 ≤ e)
    (hcross : 51 * b ≤ 91 * c) (hface : 1953 * c ≤ 1105 * b)
    (hV : b ≤ V) (hd : ∀ i, 0 < d i)
    (hcEq : d 2 = c) (heEq : d 3 = e) (hbEq : d 5 = b)
    (hlo : ∀ w i, (8 * (laps w i : ℝ) + 1) * setter c e w ≤ opening w * d i)
    (hhi : ∀ w i, closing w * d i ≤ (8 * (laps w i : ℝ) + 7) * b)
    (ha : 31 * e ≤ 49 * d 1) (hbc : 73 * c ≤ 41 * b)
    (hf : 41 * d 4 ≤ 71 * c) :
    ∃ t : ℝ, 0 < t ∧ (8 : ℝ)⁻¹ ≤ circDist (V * t) ∧
      ∀ i, (8 : ℝ)⁻¹ ≤ circDist (d i * t) := by
  obtain ⟨hfl, hfu⟩ := c_guards d hb7 he hcross hface hcEq heEq hbEq hlo hhi ha hbc hf
  apply family_isolated_of_residual d hb hc hb7 he hcross hV hd hlo hhi
  intro hvlo hvhi
  have hL : 73 ≤ V * (41 / c) := by
    rw [← mul_div_assoc, le_div_iff₀ hc]
    linarith
  have hU : V * (41 / c) ≤ 79 := by
    rw [← mul_div_assoc, div_le_iff₀ hc]
    linarith
  refine ⟨(41 / c) / 8, by positivity, ?_, clear_at_exit d cLaps hc hfl hfu⟩
  apply TwoPinner.clear_of_band (N := 9) <;> norm_num <;> nlinarith

def fLaps : Fin 6 → ℤ := ![1, 3, 4, 6, 8, 8]

theorem f_guards (d : Fin 6 → ℝ) {b c e f : ℝ}
    (hb7 : b ≤ 7) (he : 101 / 20 ≤ e)
    (hc : d 2 = c) (heq : d 3 = e) (hfEq : d 4 = f) (hb : d 5 = b)
    (hlo : ∀ w i, (8 * (laps w i : ℝ) + 1) * setter c e w ≤ opening w * d i)
    (hhi : ∀ w i, closing w * d i ≤ (8 * (laps w i : ℝ) + 7) * b)
    (hstripL : 63 * e ≤ 49 * f) (hstripU : 49 * f ≤ 65 * e)
    (ha : 65 * d 1 ≤ 31 * f) (hcf : 65 * c ≤ 39 * f)
    (hbf : 3185 * b ≤ 3337 * f) :
    (∀ i, (8 * (fLaps i : ℝ) + 1) * f ≤ 65 * d i) ∧
    (∀ i, 65 * d i ≤ (8 * (fLaps i : ℝ) + 7) * f) := by
  change d ⟨2, by decide⟩ = c at hc
  change d ⟨3, by decide⟩ = e at heq
  change d ⟨4, by decide⟩ = f at hfEq
  change d ⟨5, by decide⟩ = b at hb
  have heu := hhi ⟨3, by decide⟩ ⟨3, by decide⟩
  have hcl := hlo ⟨2, by decide⟩ ⟨2, by decide⟩
  have hfb := hhi ⟨0, by decide⟩ ⟨4, by decide⟩
  norm_num [laps, setter, opening, closing, hc, heq, hfEq] at heu hcl hfb
  constructor
  · intro i
    have hl := hlo ⟨3, by decide⟩ i
    fin_cases i <;> norm_num [laps, setter, opening, fLaps, hc, heq, hfEq, hb] at hl ⊢ <;>
      first | exact hstripU | linarith
  · intro i
    have hu := hhi ⟨2, by decide⟩ i
    fin_cases i <;> norm_num [laps, closing, fLaps, hc, heq, hfEq, hb] at hu ⊢ <;>
      first | exact ha | exact hcf | linarith

theorem f_family (d : Fin 6 → ℝ) {b c e f V : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hb7 : b ≤ 7) (he : 101 / 20 ≤ e)
    (hcross : 51 * b ≤ 91 * c) (hV : b ≤ V) (hd : ∀ i, 0 < d i)
    (hcEq : d 2 = c) (heEq : d 3 = e) (hfEq : d 4 = f) (hbEq : d 5 = b)
    (hlo : ∀ w i, (8 * (laps w i : ℝ) + 1) * setter c e w ≤ opening w * d i)
    (hhi : ∀ w i, closing w * d i ≤ (8 * (laps w i : ℝ) + 7) * b)
    (hstripL : 63 * e ≤ 49 * f) (hstripU : 49 * f ≤ 65 * e)
    (ha : 65 * d 1 ≤ 31 * f) (hcf : 65 * c ≤ 39 * f)
    (hbf : 3185 * b ≤ 3337 * f) :
    ∃ t : ℝ, 0 < t ∧ (8 : ℝ)⁻¹ ≤ circDist (V * t) ∧
      ∀ i, (8 : ℝ)⁻¹ ≤ circDist (d i * t) := by
  obtain ⟨hfl, hfu⟩ := f_guards d hb7 he hcEq heEq hfEq hbEq hlo hhi hstripL hstripU ha hcf hbf
  have hfp : 0 < f := by rw [← hfEq]; exact hd 4
  have hfb := hhi ⟨0, by decide⟩ ⟨4, by decide⟩
  change d ⟨4, by decide⟩ = f at hfEq
  norm_num [laps, closing, hfEq] at hfb
  apply family_isolated_of_residual d hb hc hb7 he hcross hV hd hlo hhi
  intro _ hvhi
  have hL : 65 ≤ V * (65 / f) := by
    rw [← mul_div_assoc, le_div_iff₀ hfp]
    linarith
  have hU : V * (65 / f) ≤ 71 := by
    rw [← mul_div_assoc, div_le_iff₀ hfp]
    linarith
  refine ⟨(65 / f) / 8, by positivity, ?_, clear_at_exit d fLaps hfp hfl hfu⟩
  apply TwoPinner.clear_of_band (N := 8) <;> norm_num <;> nlinarith

/-- On the far side of the original rescue face, protecting the inserted
reading already protects c at this exit. It is not an independent guard. -/
theorem f_c_guard_derived {b c f : ℝ} (hb : 0 < b)
    (hface : 1953 * c ≤ 1105 * b) (hbf : 3185 * b ≤ 3337 * f) :
    65 * c ≤ 39 * f := by linarith

theorem f_family_two_guards (d : Fin 6 → ℝ) {b c e f V : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hb7 : b ≤ 7) (he : 101 / 20 ≤ e)
    (hcross : 51 * b ≤ 91 * c) (hface : 1953 * c ≤ 1105 * b)
    (hV : b ≤ V) (hd : ∀ i, 0 < d i)
    (hcEq : d 2 = c) (heEq : d 3 = e) (hfEq : d 4 = f) (hbEq : d 5 = b)
    (hlo : ∀ w i, (8 * (laps w i : ℝ) + 1) * setter c e w ≤ opening w * d i)
    (hhi : ∀ w i, closing w * d i ≤ (8 * (laps w i : ℝ) + 7) * b)
    (hstripL : 63 * e ≤ 49 * f) (hstripU : 49 * f ≤ 65 * e)
    (ha : 65 * d 1 ≤ 31 * f) (hbf : 3185 * b ≤ 3337 * f) :
    ∃ t : ℝ, 0 < t ∧ (8 : ℝ)⁻¹ ≤ circDist (V * t) ∧
      ∀ i, (8 : ℝ)⁻¹ ≤ circDist (d i * t) :=
  f_family d hb hc hb7 he hcross hV hd hcEq heEq hfEq hbEq hlo hhi
    hstripL hstripU ha (f_c_guard_derived hb hface hbf) hbf

/-- When b has not yet opened at 41/c, continue instead to its opening 73/b. -/
theorem b_guards (d : Fin 6 → ℝ) {b c e : ℝ}
    (hb7 : b ≤ 7) (he : 101 / 20 ≤ e) (hface : 1953 * c ≤ 1105 * b)
    (hc : d 2 = c) (heq : d 3 = e) (hb : d 5 = b)
    (hlo : ∀ w i, (8 * (laps w i : ℝ) + 1) * setter c e w ≤ opening w * d i)
    (hhi : ∀ w i, closing w * d i ≤ (8 * (laps w i : ℝ) + 7) * b)
    (ha : 31 * e ≤ 49 * d 1) (hbc : 41 * b ≤ 73 * c)
    (hf : 73 * d 4 ≤ 71 * b) :
    (∀ i, (8 * (cLaps i : ℝ) + 1) * b ≤ 73 * d i) ∧
    (∀ i, 73 * d i ≤ (8 * (cLaps i : ℝ) + 7) * b) := by
  change d ⟨2, by decide⟩ = c at hc
  change d ⟨3, by decide⟩ = e at heq
  change d ⟨5, by decide⟩ = b at hb
  have heu := hhi ⟨3, by decide⟩ ⟨3, by decide⟩
  norm_num [laps, closing, heq] at heu
  constructor
  · intro i
    have hl := hlo ⟨3, by decide⟩ i
    fin_cases i <;> norm_num [laps, setter, opening, cLaps, hc, heq, hb] at hl ⊢ <;>
      first | exact hbc | linarith
  · intro i
    have hu := hhi ⟨1, by decide⟩ i
    have hu2 := hhi ⟨2, by decide⟩ i
    fin_cases i <;> norm_num [laps, closing, cLaps, hc, heq, hb] at hu hu2 ⊢ <;>
      first | exact hf | linarith

theorem b_family (d : Fin 6 → ℝ) {b c e V : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hb7 : b ≤ 7) (he : 101 / 20 ≤ e)
    (hcross : 51 * b ≤ 91 * c) (hface : 1953 * c ≤ 1105 * b)
    (hV : b ≤ V) (hd : ∀ i, 0 < d i)
    (hcEq : d 2 = c) (heEq : d 3 = e) (hbEq : d 5 = b)
    (hlo : ∀ w i, (8 * (laps w i : ℝ) + 1) * setter c e w ≤ opening w * d i)
    (hhi : ∀ w i, closing w * d i ≤ (8 * (laps w i : ℝ) + 7) * b)
    (ha : 31 * e ≤ 49 * d 1) (hbc : 41 * b ≤ 73 * c)
    (hf : 73 * d 4 ≤ 71 * b) :
    ∃ t : ℝ, 0 < t ∧ (8 : ℝ)⁻¹ ≤ circDist (V * t) ∧
      ∀ i, (8 : ℝ)⁻¹ ≤ circDist (d i * t) := by
  obtain ⟨hfl, hfu⟩ := b_guards d hb7 he hface hcEq heEq hbEq hlo hhi ha hbc hf
  apply family_isolated_of_residual d hb hc hb7 he hcross hV hd hlo hhi
  intro _ hvhi
  have hL : 73 ≤ V * (73 / b) := by
    rw [← mul_div_assoc, le_div_iff₀ hb]
    linarith
  have hU : V * (73 / b) ≤ 79 := by
    rw [← mul_div_assoc, div_le_iff₀ hb]
    linarith
  refine ⟨(73 / b) / 8, by positivity, ?_, clear_at_exit d cLaps hb hfl hfu⟩
  apply TwoPinner.clear_of_band (N := 9) <;> norm_num <;> nlinarith

def highFLaps : Fin 6 → ℤ := ![1, 4, 5, 6, 9, 9]

/-- Either failed f-closing guard from the two preceding branches forces
the lower ratio used below. -/
theorem high_f_ratio {b c f : ℝ} (hb : 0 < b)
    (hcross : 51 * b ≤ 91 * c)
    (hblock : 71 * c ≤ 41 * f ∨ 71 * b ≤ 73 * f) :
    3621 * b ≤ 3731 * f := by
  rcases hblock with h | h <;> linarith

theorem high_f_guards (d : Fin 6 → ℝ) {b c e f : ℝ}
    (hb7 : b ≤ 7) (he : 101 / 20 ≤ e) (hface : 1953 * c ≤ 1105 * b)
    (hc : d 2 = c) (heq : d 3 = e) (hfEq : d 4 = f) (hb : d 5 = b)
    (hlo : ∀ w i, (8 * (laps w i : ℝ) + 1) * setter c e w ≤ opening w * d i)
    (hhi : ∀ w i, closing w * d i ≤ (8 * (laps w i : ℝ) + 7) * b)
    (ha : 31 * e ≤ 49 * d 1) (hnear : 3621 * b ≤ 3731 * f)
    (hcf : 41 * f ≤ 73 * c) (hef : 73 * e ≤ 55 * f) :
    (∀ i, (8 * (highFLaps i : ℝ) + 1) * f ≤ 73 * d i) ∧
    (∀ i, 73 * d i ≤ (8 * (highFLaps i : ℝ) + 7) * f) := by
  change d ⟨2, by decide⟩ = c at hc
  change d ⟨3, by decide⟩ = e at heq
  change d ⟨4, by decide⟩ = f at hfEq
  change d ⟨5, by decide⟩ = b at hb
  have hfb := hhi ⟨0, by decide⟩ ⟨4, by decide⟩
  norm_num [laps, closing, hfEq] at hfb
  constructor
  · intro i
    have hl := hlo ⟨3, by decide⟩ i
    fin_cases i <;> norm_num [laps, setter, opening, highFLaps, hc, heq, hfEq, hb] at hl ⊢ <;>
      first | exact hcf | linarith
  · intro i
    have hu := hhi ⟨1, by decide⟩ i
    have hu2 := hhi ⟨2, by decide⟩ i
    fin_cases i <;> norm_num [laps, closing, highFLaps, hc, heq, hfEq, hb] at hu hu2 ⊢ <;>
      first | exact hef | linarith

theorem high_f_family (d : Fin 6 → ℝ) {b c e f V : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hb7 : b ≤ 7) (he : 101 / 20 ≤ e)
    (hcross : 51 * b ≤ 91 * c) (hface : 1953 * c ≤ 1105 * b)
    (hV : b ≤ V) (hd : ∀ i, 0 < d i)
    (hcEq : d 2 = c) (heEq : d 3 = e) (hfEq : d 4 = f) (hbEq : d 5 = b)
    (hlo : ∀ w i, (8 * (laps w i : ℝ) + 1) * setter c e w ≤ opening w * d i)
    (hhi : ∀ w i, closing w * d i ≤ (8 * (laps w i : ℝ) + 7) * b)
    (ha : 31 * e ≤ 49 * d 1)
    (hblock : 71 * c ≤ 41 * f ∨ 71 * b ≤ 73 * f)
    (hcf : 41 * f ≤ 73 * c) (hef : 73 * e ≤ 55 * f) :
    ∃ t : ℝ, 0 < t ∧ (8 : ℝ)⁻¹ ≤ circDist (V * t) ∧
      ∀ i, (8 : ℝ)⁻¹ ≤ circDist (d i * t) := by
  have hnear := high_f_ratio hb hcross hblock
  obtain ⟨hfl, hfu⟩ := high_f_guards d hb7 he hface hcEq heEq hfEq hbEq hlo hhi ha hnear hcf hef
  have hfp : 0 < f := by rw [← hfEq]; exact hd 4
  have hfb := hhi ⟨0, by decide⟩ ⟨4, by decide⟩
  change d ⟨4, by decide⟩ = f at hfEq
  norm_num [laps, closing, hfEq] at hfb
  apply family_isolated_of_residual d hb hc hb7 he hcross hV hd hlo hhi
  intro _ hvhi
  have hL : 73 ≤ V * (73 / f) := by
    rw [← mul_div_assoc, le_div_iff₀ hfp]
    linarith
  have hU : V * (73 / f) ≤ 79 := by
    rw [← mul_div_assoc, div_le_iff₀ hfp]
    linarith
  refine ⟨(73 / f) / 8, by positivity, ?_, clear_at_exit d highFLaps hfp hfl hfu⟩
  apply TwoPinner.clear_of_band (N := 9) <;> norm_num <;> nlinarith

/-- Past f's next opening, 41/c is clear again with f on lap 9. -/
theorem late_c_guards (d : Fin 6 → ℝ) {b c e : ℝ}
    (hb7 : b ≤ 7) (he : 101 / 20 ≤ e)
    (hcross : 51 * b ≤ 91 * c) (hface : 1953 * c ≤ 1105 * b)
    (hc : d 2 = c) (heq : d 3 = e) (hb : d 5 = b)
    (hlo : ∀ w i, (8 * (laps w i : ℝ) + 1) * setter c e w ≤ opening w * d i)
    (hhi : ∀ w i, closing w * d i ≤ (8 * (laps w i : ℝ) + 7) * b)
    (ha : 31 * e ≤ 49 * d 1) (hf : 73 * c ≤ 41 * d 4) :
    (∀ i, (8 * (highFLaps i : ℝ) + 1) * c ≤ 41 * d i) ∧
    (∀ i, 41 * d i ≤ (8 * (highFLaps i : ℝ) + 7) * c) := by
  change d ⟨2, by decide⟩ = c at hc
  change d ⟨3, by decide⟩ = e at heq
  change d ⟨5, by decide⟩ = b at hb
  have heu := hhi ⟨3, by decide⟩ ⟨3, by decide⟩
  have hfb := hhi ⟨0, by decide⟩ ⟨4, by decide⟩
  norm_num [laps, closing, heq] at heu hfb
  have hfb' : d 4 ≤ b := hfb
  constructor
  · intro i
    have hl := hlo ⟨3, by decide⟩ i
    fin_cases i <;> norm_num [laps, setter, opening, highFLaps, hc, heq, hb] at hl ⊢ <;>
      first | exact hf | linarith
  · intro i
    have hu := hhi ⟨1, by decide⟩ i
    have hu2 := hhi ⟨2, by decide⟩ i
    have hu0 := hhi ⟨0, by decide⟩ i
    fin_cases i <;> norm_num [laps, closing, highFLaps, hc, heq, hb] at hu hu2 hu0 ⊢ <;>
      linarith

theorem late_c_family (d : Fin 6 → ℝ) {b c e V : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hb7 : b ≤ 7) (he : 101 / 20 ≤ e)
    (hcross : 51 * b ≤ 91 * c) (hface : 1953 * c ≤ 1105 * b)
    (hV : b ≤ V) (hd : ∀ i, 0 < d i)
    (hcEq : d 2 = c) (heEq : d 3 = e) (hbEq : d 5 = b)
    (hlo : ∀ w i, (8 * (laps w i : ℝ) + 1) * setter c e w ≤ opening w * d i)
    (hhi : ∀ w i, closing w * d i ≤ (8 * (laps w i : ℝ) + 7) * b)
    (ha : 31 * e ≤ 49 * d 1) (hf : 73 * c ≤ 41 * d 4) :
    ∃ t : ℝ, 0 < t ∧ (8 : ℝ)⁻¹ ≤ circDist (V * t) ∧
      ∀ i, (8 : ℝ)⁻¹ ≤ circDist (d i * t) := by
  obtain ⟨hfl, hfu⟩ := late_c_guards d hb7 he hcross hface hcEq heEq hbEq hlo hhi ha hf
  apply family_isolated_of_residual d hb hc hb7 he hcross hV hd hlo hhi
  intro hvlo hvhi
  have hL : 73 ≤ V * (41 / c) := by
    rw [← mul_div_assoc, le_div_iff₀ hc]
    linarith
  have hU : V * (41 / c) ≤ 79 := by
    rw [← mul_div_assoc, div_le_iff₀ hc]
    linarith
  refine ⟨(41 / c) / 8, by positivity, ?_, clear_at_exit d highFLaps hc hfl hfu⟩
  apply TwoPinner.clear_of_band (N := 9) <;> norm_num <;> nlinarith

/-- Combine all c/b/f orderings: the a-obstruction is resolved whenever
e stays clear through f's opening. No extra ordering is assumed. -/
theorem a_branch_family (d : Fin 6 → ℝ) {b c e f V : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hb7 : b ≤ 7) (he : 101 / 20 ≤ e)
    (hcross : 51 * b ≤ 91 * c) (hface : 1953 * c ≤ 1105 * b)
    (hV : b ≤ V) (hd : ∀ i, 0 < d i)
    (hcEq : d 2 = c) (heEq : d 3 = e) (hfEq : d 4 = f) (hbEq : d 5 = b)
    (hlo : ∀ w i, (8 * (laps w i : ℝ) + 1) * setter c e w ≤ opening w * d i)
    (hhi : ∀ w i, closing w * d i ≤ (8 * (laps w i : ℝ) + 7) * b)
    (ha : 31 * e ≤ 49 * d 1) (hef : 73 * e ≤ 55 * f) :
    ∃ t : ℝ, 0 < t ∧ (8 : ℝ)⁻¹ ≤ circDist (V * t) ∧
      ∀ i, (8 : ℝ)⁻¹ ≤ circDist (d i * t) := by
  by_cases hcf : 41 * f ≤ 73 * c
  · have finish := high_f_family d hb hc hb7 he hcross hface hV hd
      hcEq heEq hfEq hbEq hlo hhi ha
    by_cases hbc : 73 * c ≤ 41 * b
    · by_cases hf : 41 * f ≤ 71 * c
      · exact c_family d hb hc hb7 he hcross hface hV hd hcEq heEq hbEq hlo hhi ha hbc
          (by simpa only [hfEq] using hf)
      · exact finish (Or.inl (le_of_not_ge hf)) hcf hef
    · by_cases hf : 73 * f ≤ 71 * b
      · exact b_family d hb hc hb7 he hcross hface hV hd hcEq heEq hbEq hlo hhi ha
          (le_of_not_ge hbc) (by simpa only [hfEq] using hf)
      · exact finish (Or.inr (le_of_not_ge hf)) hcf hef
  · exact late_c_family d hb hc hb7 he hcross hface hV hd hcEq heEq hbEq hlo hhi ha
      (by simpa only [hfEq] using (le_of_not_ge hcf))

end LRC.MovingCoreExit
