import LonelyRunner.LRC.Spec.CoreWindowCompatibilityN

/-!
# A uniform replacement for the compatible three-window obstruction

The six core readings are fixed. The inserted speed ranges over a whole open
interval, not a sample. Times R below are measured in eighths (t = R / 8).
The conclusion does not assert that all core arrangements have this mechanism.
-/

namespace LRC.CoreWindowReplacementExample

noncomputable def core : Fin 6 → ℝ :=
  ![1, 73 / 25, 99 / 25, 253 / 50, 321 / 50, 697 / 100]

noncomputable def earlyLo : Fin 3 → ℝ := ![1, 425 / 99, 150 / 23]
noncomputable def earlyHi : Fin 3 → ℝ := ![700 / 697, 3100 / 697, 4700 / 697]

theorem early_endpoints (w : Fin 3) : 0 < earlyLo w ∧ earlyLo w ≤ earlyHi w := by
  fin_cases w <;> norm_num [earlyLo, earlyHi]

/-- These three entire early windows are clear for the core. -/
theorem early_core_window (w : Fin 3) {R : ℝ}
    (hL : earlyLo w ≤ R) (hU : R ≤ earlyHi w) :
    ∀ i, (8 : ℝ)⁻¹ ≤ circDist (core i * (R / 8)) := by
  intro i
  let q : Fin 3 → Fin 6 → ℤ :=
    ![![0, 0, 0, 0, 0, 0], ![0, 1, 2, 2, 3, 3], ![0, 2, 3, 4, 5, 5]]
  apply TwoPinner.clear_of_band (N := q w i)
  · fin_cases w <;> fin_cases i <;>
      norm_num [core, q, earlyLo, earlyHi] at * <;> nlinarith
  · fin_cases w <;> fin_cases i <;>
      norm_num [core, q, earlyLo, earlyHi] at * <;> nlinarith

/-- Eliminate every possible triple of obstruction labels. For this core,
joint obstruction forces precisely labels (1,4,6) and this open speed interval.
The added speed is at least the largest core reading. -/
theorem three_captures_force_interval {V : ℝ} (hV : 697 / 100 ≤ V)
    (K₁ K₂ K₃ : ℤ)
    (h1l : 8 * (K₁ : ℝ) - 1 < V)
    (h1u : V * (700 / 697) < 8 * (K₁ : ℝ) + 1)
    (h2l : 8 * (K₂ : ℝ) - 1 < V * (425 / 99))
    (h2u : V * (3100 / 697) < 8 * (K₂ : ℝ) + 1)
    (h3l : 8 * (K₃ : ℝ) - 1 < V * (150 / 23))
    (h3u : V * (4700 / 697) < 8 * (K₃ : ℝ) + 1) :
    K₁ = 1 ∧ K₂ = 4 ∧ K₃ = 6 ∧ 3069 / 425 < V ∧ V < 34153 / 4700 := by
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

/-- Every core reading stays clear throughout the replacement window. -/
theorem core_window {R : ℝ} (hL : 9 ≤ R) (hU : R ≤ 6300 / 697) :
    ∀ i, (8 : ℝ)⁻¹ ≤ circDist (core i * (R / 8)) := by
  intro i
  let q : Fin 6 → ℤ := ![1, 3, 4, 5, 7, 7]
  apply TwoPinner.clear_of_band (N := q i)
  · fin_cases i <;> norm_num [core, q] <;> nlinarith
  · fin_cases i <;> norm_num [core, q] <;> nlinarith

/-- On the entire compatible speed interval, either R=9 works or the
inserted reading's lap-8 exit R=65/V lies in the same core-clear window. -/
theorem replacement_in_window {V : ℝ}
    (hlo : 3069 / 425 < V) (hhi : V < 34153 / 4700) :
    ∃ R : ℝ, (R = 9 ∨ R = 65 / V) ∧ 9 ≤ R ∧ R ≤ 6300 / 697 ∧
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

/-- A genuine infinite family: six fixed core readings plus every inserted
speed in the compatible interval have an explicit replacement isolation. -/
theorem compatible_family_isolated {V : ℝ}
    (hlo : 3069 / 425 < V) (hhi : V < 34153 / 4700) :
    ∃ t : ℝ, 0 < t ∧ (t = 9 / 8 ∨ t = 65 / (8 * V)) ∧
      (8 : ℝ)⁻¹ ≤ circDist (V * t) ∧
      ∀ i, (8 : ℝ)⁻¹ ≤ circDist (core i * t) := by
  obtain ⟨R, hR, hL, hU, hfL, hfU⟩ := replacement_in_window hlo hhi
  refine ⟨R / 8, by linarith, ?_, ?_, core_window hL hU⟩
  · rcases hR with h | h
    · exact Or.inl (by rw [h])
    · right
      rw [h]
      ring
  · apply TwoPinner.clear_of_band (N := 8) <;> norm_num <;> nlinarith

/-- For this fixed core, EVERY added speed at least its largest reading is
covered: one early window survives, or the compatible obstruction forces
the explicit late replacement. No speed sampling and no time enumeration. -/
theorem all_largest_insertions {V : ℝ} (hV : 697 / 100 ≤ V) :
    ∃ t : ℝ, 0 < t ∧ (8 : ℝ)⁻¹ ≤ circDist (V * t) ∧
      ∀ i, (8 : ℝ)⁻¹ ≤ circDist (core i * t) := by
  have hVp : 0 < V := by linarith
  by_cases h : ∃ w : Fin 3, ∃ R : ℝ,
      earlyLo w ≤ R ∧ R ≤ earlyHi w ∧ (8 : ℝ)⁻¹ ≤ circDist (V * (R / 8))
  · obtain ⟨w, R, hl, hu, hc⟩ := h
    exact ⟨R / 8, by have := (early_endpoints w).1; linarith,
      hc, early_core_window w hl hu⟩
  · have hb : ∀ w : Fin 3, ∃ K : ℤ,
        8 * (K : ℝ) - 1 < V * earlyLo w ∧
        V * earlyHi w < 8 * (K : ℝ) + 1 := by
      intro w
      have hep := early_endpoints w
      have hc : ∀ t, earlyLo w / 8 ≤ t → t ≤ earlyHi w / 8 →
          circDist (V * t) < (8 : ℝ)⁻¹ := by
        intro t hl hu
        apply lt_of_not_ge
        intro ht
        apply h
        refine ⟨w, 8 * t, by linarith, by linarith, ?_⟩
        simpa using ht
      obtain ⟨K, hl, hu⟩ := (CoreWindowInsertion.swallowed_iff hVp
        (show earlyLo w / 8 ≤ earlyHi w / 8 by linarith)).mp hc
      exact ⟨K, by nlinarith, by nlinarith⟩
    obtain ⟨K₁, h1l, h1u⟩ := hb 0
    obtain ⟨K₂, h2l, h2u⟩ := hb 1
    obtain ⟨K₃, h3l, h3u⟩ := hb 2
    norm_num [earlyLo, earlyHi] at h1l h1u h2l h2u h3l h3u
    obtain ⟨_, _, _, hlo, hhi⟩ := three_captures_force_interval hV K₁ K₂ K₃
      h1l h1u h2l h2u h3l h3u
    obtain ⟨t, ht, _, hfast, hcore⟩ := compatible_family_isolated hlo hhi
    exact ⟨t, ht, hfast, hcore⟩

end LRC.CoreWindowReplacementExample
