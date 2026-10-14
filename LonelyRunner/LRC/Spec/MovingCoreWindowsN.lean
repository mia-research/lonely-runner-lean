import LonelyRunner.LRC.Spec.CoreWindowCompatibilityN

/-!
# Moving core windows and ratio-controlled replacement

Window endpoints follow three positive parameters b,c,e (which can be chosen
as core readings). Their joint capture labels are derived, not assumed.
The core-clearance hypotheses below are explicit linear speed inequalities.
They describe one mechanism region, not all arrangements.
-/

namespace LRC.MovingCoreWindows

noncomputable def opening : Fin 4 → ℝ := ![1, 17, 33, 9]
noncomputable def closing : Fin 4 → ℝ := ![7, 31, 47, 63]
noncomputable def setter (c e : ℝ) : Fin 4 → ℝ := ![1, c, e, 1]
def laps : Fin 4 → Fin 6 → ℤ :=
  ![![0, 0, 0, 0, 0, 0], ![0, 1, 2, 2, 3, 3],
    ![0, 2, 3, 4, 5, 5], ![1, 3, 4, 5, 7, 7]]

theorem window_endpoints_of_cross {b c e : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hb7 : b ≤ 7) (he : 101 / 20 ≤ e) (hbc : 51 * b ≤ 91 * c)
    (w : Fin 4) :
    0 < opening w / setter c e w ∧ opening w / setter c e w ≤ closing w / b := by
  have hep : 0 < e := by linarith
  fin_cases w
  · norm_num [opening, closing, setter]
    exact (le_div_iff₀ hb).mpr (by linarith)
  · change 0 < 17 / c ∧ 17 / c ≤ 31 / b
    exact ⟨div_pos (by norm_num) hc, (div_le_div_iff₀ hc hb).mpr (by linarith)⟩
  · change 0 < 33 / e ∧ 33 / e ≤ 47 / b
    exact ⟨div_pos (by norm_num) hep, (div_le_div_iff₀ hep hb).mpr (by linarith)⟩
  · norm_num [opening, closing, setter]
    exact (le_div_iff₀ hb).mpr (by linarith)

theorem window_endpoints {b c e : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hb7 : b ≤ 7) (he : 101 / 20 ≤ e) (hbc : 1105 * b ≤ 1953 * c)
    (w : Fin 4) :
    0 < opening w / setter c e w ∧ opening w / setter c e w ≤ closing w / b :=
  window_endpoints_of_cross hb hc hb7 he (by linarith) w

/-- The six-readings condition for each whole moving window is linear in
the readings and setters; no small-perturbation bound is used. -/
theorem window_clear (d : Fin 6 → ℝ) {b c e : ℝ}
    (hb : 0 < b) (hc : 0 < c) (he : 0 < e) (hd : ∀ i, 0 < d i)
    (hlo : ∀ w i, (8 * (laps w i : ℝ) + 1) * setter c e w ≤ opening w * d i)
    (hhi : ∀ w i, closing w * d i ≤ (8 * (laps w i : ℝ) + 7) * b)
    (w : Fin 4) {R : ℝ}
    (hL : opening w / setter c e w ≤ R) (hU : R ≤ closing w / b) :
    ∀ i, (8 : ℝ)⁻¹ ≤ circDist (d i * (R / 8)) := by
  have hs : 0 < setter c e w := by
    fin_cases w
    · norm_num [setter]
    · exact hc
    · exact he
    · norm_num [setter]
  intro i
  have hl : 8 * (laps w i : ℝ) + 1 ≤ d i * (opening w / setter c e w) := by
    rw [← mul_div_assoc, le_div_iff₀ hs]
    nlinarith [hlo w i]
  have hu : d i * (closing w / b) ≤ 8 * (laps w i : ℝ) + 7 := by
    rw [← mul_div_assoc, div_le_iff₀ hb]
    nlinarith [hhi w i]
  have hlR := mul_le_mul_of_nonneg_left hL (hd i).le
  have huR := mul_le_mul_of_nonneg_left hU (hd i).le
  apply TwoPinner.clear_of_band (N := laps w i) <;> nlinarith

/-- The joint obstruction labels remain (1,4,6) throughout the ratio region.
All six capture-edge inequalities are retained, with denominators cleared. -/
theorem obstruction_labels_of_cross {b c e V : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hb7 : b ≤ 7) (he : 101 / 20 ≤ e)
    (hcross : 51 * b ≤ 91 * c) (hV : b ≤ V)
    (K₁ K₂ K₃ : ℤ)
    (h1l : 8 * (K₁ : ℝ) - 1 < V)
    (h1u : 7 * V < (8 * (K₁ : ℝ) + 1) * b)
    (h2l : (8 * (K₂ : ℝ) - 1) * c < 17 * V)
    (h2u : 31 * V < (8 * (K₂ : ℝ) + 1) * b)
    (h3l : (8 * (K₃ : ℝ) - 1) * e < 33 * V)
    (h3u : 47 * V < (8 * (K₃ : ℝ) + 1) * b) :
    K₁ = 1 ∧ K₂ = 4 ∧ K₃ = 6 ∧ 31 * c / 17 < V ∧ V < 49 * b / 47 := by
  have h3a : (5 : ℝ) < K₃ := by nlinarith
  have hx : 0 < 8 * (K₃ : ℝ) - 1 := by linarith
  have hy : 0 < 8 * (K₃ : ℝ) + 1 := by linarith
  have h3lo := mul_le_mul_of_nonneg_left he hx.le
  have h3hi := mul_le_mul_of_nonneg_left hb7 hy.le
  have hv15 : V < 15 := by nlinarith
  have h1a : (0 : ℝ) < K₁ := by nlinarith
  have h1b : (K₁ : ℝ) < 2 := by linarith
  have h1ai : (0 : ℤ) < K₁ := by exact_mod_cast h1a
  have h1bi : K₁ < 2 := by exact_mod_cast h1b
  have hk1 : K₁ = 1 := by omega
  subst K₁
  norm_num at h1l h1u
  have h2a : (3 : ℝ) < K₂ := by nlinarith
  have h2b : (K₂ : ℝ) < 5 := by nlinarith
  have h2ai : (3 : ℤ) < K₂ := by exact_mod_cast h2a
  have h2bi : K₂ < 5 := by exact_mod_cast h2b
  have hk2 : K₂ = 4 := by omega
  subst K₂
  norm_num at h2l h2u
  have hecross : 1089 * b ≤ 1705 * e := by linarith
  have h3b : (K₃ : ℝ) < 7 := by nlinarith
  have h3ai : (5 : ℤ) < K₃ := by exact_mod_cast h3a
  have h3bi : K₃ < 7 := by exact_mod_cast h3b
  have hk3 : K₃ = 6 := by omega
  subst K₃
  norm_num at h3l h3u
  exact ⟨rfl, rfl, rfl, by linarith, by linarith⟩

theorem obstruction_labels {b c e V : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hb7 : b ≤ 7) (he : 101 / 20 ≤ e)
    (hbc : 1105 * b ≤ 1953 * c) (hV : b ≤ V)
    (K₁ K₂ K₃ : ℤ)
    (h1l : 8 * (K₁ : ℝ) - 1 < V)
    (h1u : 7 * V < (8 * (K₁ : ℝ) + 1) * b)
    (h2l : (8 * (K₂ : ℝ) - 1) * c < 17 * V)
    (h2u : 31 * V < (8 * (K₂ : ℝ) + 1) * b)
    (h3l : (8 * (K₃ : ℝ) - 1) * e < 33 * V)
    (h3u : 47 * V < (8 * (K₃ : ℝ) + 1) * b) :
    K₁ = 1 ∧ K₂ = 4 ∧ K₃ = 6 ∧ 31 * c / 17 < V ∧ V < 49 * b / 47 :=
  obstruction_labels_of_cross hb hc hb7 he (by linarith) hV
    K₁ K₂ K₃ h1l h1u h2l h2u h3l h3u

/-- The late window rescues every speed in the forced obstruction interval. -/
theorem rescue {b c V : ℝ} (hb : 0 < b) (_hc : 0 < c) (hb7 : b ≤ 7)
    (hbc : 1105 * b ≤ 1953 * c)
    (hlo : 31 * c / 17 < V) (hhi : V < 49 * b / 47) :
    ∃ R : ℝ, (R = 9 ∨ R = 65 / V) ∧ 9 ≤ R ∧ R ≤ 63 / b ∧
      65 ≤ V * R ∧ V * R ≤ 71 := by
  have hV : 0 < V := by linarith
  by_cases h : 65 ≤ V * 9
  · refine ⟨9, Or.inl rfl, le_rfl, (le_div_iff₀ hb).mpr (by linarith), h, ?_⟩
    linarith
  · have heq : V * (65 / V) = 65 := mul_div_cancel₀ _ hV.ne'
    refine ⟨65 / V, Or.inr rfl, (le_div_iff₀ hV).mpr (by linarith), ?_, heq.ge, ?_⟩
    · apply (div_le_div_iff₀ hV hb).mpr
      linarith
    · linarith

/-- Reduce this core region to the forced residual interval. This extraction
does not itself prove replacement: the caller must discharge `hres`.
The weaker cross inequality allows different replacements on either side
of the original rescue boundary. -/
theorem family_isolated_of_residual (d : Fin 6 → ℝ) {b c e V : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hb7 : b ≤ 7) (he : 101 / 20 ≤ e)
    (hbc : 51 * b ≤ 91 * c) (hV : b ≤ V) (hd : ∀ i, 0 < d i)
    (hlo : ∀ w i, (8 * (laps w i : ℝ) + 1) * setter c e w ≤ opening w * d i)
    (hhi : ∀ w i, closing w * d i ≤ (8 * (laps w i : ℝ) + 7) * b)
    (hres : 31 * c / 17 < V → V < 49 * b / 47 →
      ∃ t : ℝ, 0 < t ∧ (8 : ℝ)⁻¹ ≤ circDist (V * t) ∧
        ∀ i, (8 : ℝ)⁻¹ ≤ circDist (d i * t)) :
    ∃ t : ℝ, 0 < t ∧ (8 : ℝ)⁻¹ ≤ circDist (V * t) ∧
      ∀ i, (8 : ℝ)⁻¹ ≤ circDist (d i * t) := by
  have hVp : 0 < V := hb.trans_le hV
  have hep : 0 < e := by linarith
  by_cases h : ∃ w : Fin 3, ∃ R : ℝ,
      opening w.castSucc / setter c e w.castSucc ≤ R ∧
      R ≤ closing w.castSucc / b ∧ (8 : ℝ)⁻¹ ≤ circDist (V * (R / 8))
  · obtain ⟨w, R, hl, hu, hf⟩ := h
    have hp := (window_endpoints_of_cross hb hc hb7 he hbc w.castSucc).1
    exact ⟨R / 8, by linarith, hf, window_clear d hb hc hep hd hlo hhi w.castSucc hl hu⟩
  · have hcap : ∀ w : Fin 3, ∃ K : ℤ,
        (8 * (K : ℝ) - 1) * setter c e w.castSucc < opening w.castSucc * V ∧
        closing w.castSucc * V < (8 * (K : ℝ) + 1) * b := by
      intro w
      have hs : 0 < setter c e w.castSucc := by
        fin_cases w
        · norm_num [setter]
        · exact hc
        · exact hep
      have hw := window_endpoints_of_cross hb hc hb7 he hbc w.castSucc
      have hn : ∀ t,
          (opening w.castSucc / setter c e w.castSucc) / 8 ≤ t →
          t ≤ (closing w.castSucc / b) / 8 → circDist (V * t) < (8 : ℝ)⁻¹ := by
        intro t hl hu
        apply lt_of_not_ge
        intro ht
        apply h
        exact ⟨w, 8 * t, by linarith, by linarith, by simpa using ht⟩
      obtain ⟨K, hl, hu⟩ := (CoreWindowInsertion.swallowed_iff hVp
        (show (opening w.castSucc / setter c e w.castSucc) / 8 ≤
          (closing w.castSucc / b) / 8 by linarith)).mp hn
      have hl' : (K : ℝ) - 1 / 8 <
          (V * opening w.castSucc / 8) / setter c e w.castSucc := by
        convert hl using 1
        ring
      have hu' : (V * closing w.castSucc / 8) / b < (K : ℝ) + 1 / 8 := by
        convert hu using 1
        ring
      have hlm := (lt_div_iff₀ hs).mp hl'
      have hum := (div_lt_iff₀ hb).mp hu'
      exact ⟨K, by nlinarith, by nlinarith⟩
    obtain ⟨K₁, h1l, h1u⟩ := hcap 0
    obtain ⟨K₂, h2l, h2u⟩ := hcap 1
    obtain ⟨K₃, h3l, h3u⟩ := hcap 2
    norm_num [opening, closing, setter] at h1l h1u h2l h2u h3l h3u
    obtain ⟨_, _, _, hvlo, hvhi⟩ := obstruction_labels_of_cross hb hc hb7 he hbc hV
      K₁ K₂ K₃ h1l h1u h2l h2u h3l h3u
    exact hres hvlo hvhi

/-- The original late-window replacement, retained with the same interface. -/
theorem family_isolated (d : Fin 6 → ℝ) {b c e V : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hb7 : b ≤ 7) (he : 101 / 20 ≤ e)
    (hbc : 1105 * b ≤ 1953 * c) (hV : b ≤ V) (hd : ∀ i, 0 < d i)
    (hlo : ∀ w i, (8 * (laps w i : ℝ) + 1) * setter c e w ≤ opening w * d i)
    (hhi : ∀ w i, closing w * d i ≤ (8 * (laps w i : ℝ) + 7) * b) :
    ∃ t : ℝ, 0 < t ∧ (8 : ℝ)⁻¹ ≤ circDist (V * t) ∧
      ∀ i, (8 : ℝ)⁻¹ ≤ circDist (d i * t) := by
  apply family_isolated_of_residual d hb hc hb7 he (by linarith) hV hd hlo hhi
  intro hvlo hvhi
  obtain ⟨R, _, hl, hu, hfL, hfU⟩ := rescue hb hc hb7 hbc hvlo hvhi
  refine ⟨R / 8, by linarith, ?_, ?_⟩
  · apply TwoPinner.clear_of_band (N := 8) <;> norm_num <;> nlinarith
  · exact window_clear d hb hc (by linarith) hd hlo hhi 3
      (by simpa [opening, setter] using hl) (by simpa [closing] using hu)

end LRC.MovingCoreWindows
