import LonelyRunner.LRC.Spec.CoreWindowReplacementExampleN

/-!
# A variable-core family with a forced replacement

All six core readings vary independently in explicit intervals. Four fixed
subwindows carry their clearance. Joint obstruction of the first three forces
labels (1,4,6), whose speed interval is rescued by the fourth. These are
sufficient family conditions, not an exhaustive classification of all cores.
-/

namespace LRC.VariableCoreReplacement

noncomputable def lower : Fin 6 → ℝ :=
  ![1, 25 / 9, 170 / 43, 3300 / 653, 19 / 3, 19 / 3]
noncomputable def upper : Fin 6 → ℝ :=
  ![350 / 337, 125 / 37, 1300 / 301, 575 / 111, 2350 / 337, 2350 / 337]
noncomputable def left : Fin 4 → ℝ := ![1, 43 / 10, 653 / 100, 9]
noncomputable def right : Fin 4 → ℝ := ![1001 / 1000, 111 / 25, 337 / 50, 903 / 100]

theorem endpoints (w : Fin 4) : 0 < left w ∧ left w ≤ right w := by
  fin_cases w <;> norm_num [left, right]

set_option maxHeartbeats 1000000 in
/-- Uniform clearance throughout each window, derived from speed bounds. -/
theorem windows_clear (d : Fin 6 → ℝ)
    (hd : ∀ i, lower i ≤ d i ∧ d i ≤ upper i)
    (w : Fin 4) {R : ℝ} (hl : left w ≤ R) (hu : R ≤ right w) :
    ∀ i, (8 : ℝ)⁻¹ ≤ circDist (d i * (R / 8)) := by
  intro i
  let q : Fin 4 → Fin 6 → ℤ :=
    ![![0, 0, 0, 0, 0, 0], ![0, 1, 2, 2, 3, 3],
      ![0, 2, 3, 4, 5, 5], ![1, 3, 4, 5, 7, 7]]
  have hb := hd i
  have hprodL : lower i * left w ≤ d i * R := by
    apply mul_le_mul hb.1 hl (endpoints w).1.le
    have : 0 ≤ lower i := by fin_cases i <;> norm_num [lower]
    exact this.trans hb.1
  have hprodU : d i * R ≤ upper i * right w := by
    apply mul_le_mul hb.2 hu
    · exact (endpoints w).1.le.trans hl
    · fin_cases i <;> norm_num [upper]
  apply TwoPinner.clear_of_band (N := q w i)
  · fin_cases w <;> fin_cases i <;>
      norm_num [q, lower, left] at * <;> nlinarith
  · fin_cases w <;> fin_cases i <;>
      norm_num [q, upper, right] at * <;> nlinarith

/-- Joint failure of the three early subwindows fixes every capture label
and bounds the inserted speed. No fixed core values enter this calculation. -/
theorem obstruction_interval {V : ℝ} (hV : 19 / 3 ≤ V)
    (K₁ K₂ K₃ : ℤ)
    (h1l : 8 * (K₁ : ℝ) - 1 < V)
    (h1u : V * (1001 / 1000) < 8 * (K₁ : ℝ) + 1)
    (h2l : 8 * (K₂ : ℝ) - 1 < V * (43 / 10))
    (h2u : V * (111 / 25) < 8 * (K₂ : ℝ) + 1)
    (h3l : 8 * (K₃ : ℝ) - 1 < V * (653 / 100))
    (h3u : V * (337 / 50) < 8 * (K₃ : ℝ) + 1) :
    K₁ = 1 ∧ K₂ = 4 ∧ K₃ = 6 ∧ 310 / 43 < V ∧ V < 2450 / 337 := by
  have hv10 : V < 10 := by linarith
  have h1a : (0 : ℝ) < K₁ := by linarith
  have h1b : (K₁ : ℝ) < 2 := by linarith
  have h1ai : (0 : ℤ) < K₁ := by exact_mod_cast h1a
  have h1bi : K₁ < 2 := by exact_mod_cast h1b
  have hk1 : K₁ = 1 := by omega
  subst K₁
  norm_num at h1l h1u
  have h2a : (3 : ℝ) < K₂ := by linarith
  have h2b : (K₂ : ℝ) < 5 := by linarith
  have h2ai : (3 : ℤ) < K₂ := by exact_mod_cast h2a
  have h2bi : K₂ < 5 := by exact_mod_cast h2b
  have hk2 : K₂ = 4 := by omega
  subst K₂
  norm_num at h2l h2u
  have h3a : (5 : ℝ) < K₃ := by linarith
  have h3b : (K₃ : ℝ) < 7 := by linarith
  have h3ai : (5 : ℤ) < K₃ := by exact_mod_cast h3a
  have h3bi : K₃ < 7 := by exact_mod_cast h3b
  have hk3 : K₃ = 6 := by omega
  subst K₃
  norm_num at h3l h3u
  exact ⟨rfl, rfl, rfl, by linarith, by linarith⟩

theorem rescue_reading {V : ℝ} (hlo : 310 / 43 < V) (hhi : V < 2450 / 337) :
    ∃ R : ℝ, (R = 9 ∨ R = 65 / V) ∧ 9 ≤ R ∧ R ≤ 903 / 100 ∧
      65 ≤ V * R ∧ V * R ≤ 71 := by
  have hV : 0 < V := by linarith
  by_cases h : 65 ≤ V * 9
  · refine ⟨9, Or.inl rfl, le_rfl, by norm_num, h, ?_⟩
    linarith
  · have he : V * (65 / V) = 65 := mul_div_cancel₀ _ hV.ne'
    refine ⟨65 / V, Or.inr rfl, ?_, ?_, he.ge, ?_⟩
    · apply (le_div_iff₀ hV).mpr
      linarith
    · apply (div_le_iff₀ hV).mpr
      linarith
    · linarith

/-- Every core in the displayed six-dimensional region, with any inserted
speed V >= 19/3, has a positive isolation time for the subject. -/
theorem family_isolated (d : Fin 6 → ℝ)
    (hd : ∀ i, lower i ≤ d i ∧ d i ≤ upper i)
    {V : ℝ} (hV : 19 / 3 ≤ V) :
    ∃ t : ℝ, 0 < t ∧ (8 : ℝ)⁻¹ ≤ circDist (V * t) ∧
      ∀ i, (8 : ℝ)⁻¹ ≤ circDist (d i * t) := by
  have hVp : 0 < V := by linarith
  by_cases h : ∃ w : Fin 3, ∃ R : ℝ,
      left w.castSucc ≤ R ∧ R ≤ right w.castSucc ∧
        (8 : ℝ)⁻¹ ≤ circDist (V * (R / 8))
  · obtain ⟨w, R, hl, hu, hc⟩ := h
    exact ⟨R / 8, by have := (endpoints w.castSucc).1; linarith,
      hc, windows_clear d hd w.castSucc hl hu⟩
  · have hb : ∀ w : Fin 3, ∃ K : ℤ,
        8 * (K : ℝ) - 1 < V * left w.castSucc ∧
        V * right w.castSucc < 8 * (K : ℝ) + 1 := by
      intro w
      have hep := endpoints w.castSucc
      have hc : ∀ t, left w.castSucc / 8 ≤ t → t ≤ right w.castSucc / 8 →
          circDist (V * t) < (8 : ℝ)⁻¹ := by
        intro t hl hu
        apply lt_of_not_ge
        intro ht
        apply h
        refine ⟨w, 8 * t, by linarith, by linarith, ?_⟩
        simpa using ht
      obtain ⟨K, hl, hu⟩ := (CoreWindowInsertion.swallowed_iff hVp
        (show left w.castSucc / 8 ≤ right w.castSucc / 8 by linarith)).mp hc
      exact ⟨K, by nlinarith, by nlinarith⟩
    obtain ⟨K₁, h1l, h1u⟩ := hb 0
    obtain ⟨K₂, h2l, h2u⟩ := hb 1
    obtain ⟨K₃, h3l, h3u⟩ := hb 2
    norm_num [left, right] at h1l h1u h2l h2u h3l h3u
    obtain ⟨_, _, _, hlo, hhi⟩ := obstruction_interval hV K₁ K₂ K₃
      h1l h1u h2l h2u h3l h3u
    obtain ⟨R, _, hl, hu, hvL, hvU⟩ := rescue_reading hlo hhi
    refine ⟨R / 8, by linarith, ?_, ?_⟩
    · apply TwoPinner.clear_of_band (N := 8) <;> norm_num <;> nlinarith
    · exact windows_clear d hd 3 (by simpa [left] using hl) (by simpa [right] using hu)

end LRC.VariableCoreReplacement
