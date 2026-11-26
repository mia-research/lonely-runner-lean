import Fresh.TranslatedSixAll
import Fresh.TranslatedSixSmall

/-! Worklist G04/G12/A04. The entire translated-six family, every real a>0.
The small branch is an AP-grid shift; three middle and five upper charts
join the recurring mixed-lap flank. [PROVISIONAL: counting tool] inherited
by the integer shift/floor selections; [PROVISIONAL: covering] supports
the exact finite PARAMETER splits, not a covering-rate argument. -/

namespace Fresh.TranslatedSix

theorem middle_0 (a : ℝ) (ha : (1 / 8 : ℝ) ≤ a) (hb : a ≤ (11 / 34 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ train a, (1 / 8 : ℝ) ≤ distInt (d * t) := by
  have hd : (0 : ℝ) < (a + 4) := by linarith
  refine ⟨(49 : ℝ) / (8 * (a + 4)), by positivity, fun d hmem => ?_⟩
  simp only [train, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (3 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (4 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (6 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (7 : ℤ) <;> norm_num <;> nlinarith

theorem middle_1 (a : ℝ) (ha : (3 / 16 : ℝ) ≤ a) (hb : a ≤ (2 / 5 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ train a, (1 / 8 : ℝ) ≤ distInt (d * t) := by
  have hd : (0 : ℝ) < (a + 3) := by linarith
  refine ⟨(17 : ℝ) / (8 * (a + 3)), by positivity, fun d hmem => ?_⟩
  simp only [train, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (3 : ℤ) <;> norm_num <;> nlinarith

theorem middle_2 (a : ℝ) (ha : (3 / 8 : ℝ) ≤ a) (hb : a ≤ 1) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ train a, (1 / 8 : ℝ) ≤ distInt (d * t) := by
  have hd : (0 : ℝ) < (a + 3) := by linarith
  refine ⟨(9 : ℝ) / (8 * (a + 3)), by positivity, fun d hmem => ?_⟩
  simp only [train, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith

/-- [PROVISIONAL: covering] exact finite parameter split, using the
grid-shift and mixed-lap laws for the two unbounded ends. -/
theorem translated_six_positive (a : ℝ) (ha : 0 < a) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ train a, (1 / 8 : ℝ) ≤ distInt (d * t) := by
  by_cases hs : a ≤ 1 / 8
  · exact translated_six_small a ha hs
  by_cases hm0 : a ≤ 3 / 16
  · exact middle_0 a (by linarith) (by linarith)
  by_cases hm1 : a ≤ 3 / 8
  · exact middle_1 a (by linarith) (by linarith)
  by_cases hm2 : a ≤ 1
  · exact middle_2 a (by linarith) hm2
  exact translated_six_all a (by linarith)

-- STANDING: DEFINITION
def TranslatedSixPositiveClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ s a : ℝ, 0 < s ∧ 0 < a ∧
    ∀ d ∈ disparitySet v k, ∃ q ∈ train a, d = s * q

theorem translatedSixPositive_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : TranslatedSixPositiveClass v k) : Isolation v k := by
  obtain ⟨s,a,hs,ha,hmem⟩ := h
  obtain ⟨t,ht,hclear⟩ := translated_six_positive a ha
  refine ⟨t/s,by positivity,?_⟩
  rw [Fresh.Localisation.isolatedAt_iff]
  intro d hd
  obtain ⟨q,hq,rfl⟩ := hmem d hd
  have he : s*q*(t/s)=q*t := by field_simp
  rw [he]
  exact hclear q hq

theorem translatedSixClass_imp_positive {v : Fin 8 → ℝ} {k : Fin 8}
    (h : TranslatedSixClass v k) : TranslatedSixPositiveClass v k := by
  obtain ⟨s,a,hs,ha,h⟩ := h
  exact ⟨s,a,hs,by linarith,h⟩

theorem translatedSixPositiveClass_smul {c : ℝ} (hc : 0 < c)
    {v : Fin 8 → ℝ} {k : Fin 8} :
    TranslatedSixPositiveClass (fun j => c*v j) k ↔ TranslatedSixPositiveClass v k := by
  constructor
  · rintro ⟨s,a,hs,ha,hmem⟩
    refine ⟨s/c,a,by positivity,ha,fun d hd => ?_⟩
    obtain ⟨q,hq,he⟩ := hmem (c*d) ((Fresh.AdmissibleFlank.mem_disp_smul hc v k _).2 ⟨d,hd,rfl⟩)
    refine ⟨q,hq,?_⟩
    have hqdiv : s / c * q = (s*q)/c := by ring
    rw [hqdiv, eq_div_iff hc.ne']
    nlinarith
  · rintro ⟨s,a,hs,ha,hmem⟩
    refine ⟨c*s,a,by positivity,ha,fun d hd => ?_⟩
    obtain ⟨d0,hd0,rfl⟩ := (Fresh.AdmissibleFlank.mem_disp_smul hc v k _).1 hd
    obtain ⟨q,hq,rfl⟩ := hmem d0 hd0
    exact ⟨q,hq,by ring⟩

#print axioms middle_0
#print axioms middle_1
#print axioms middle_2
#print axioms translated_six_positive
#print axioms translatedSixPositive_isolation
#print axioms translatedSixClass_imp_positive
#print axioms translatedSixPositiveClass_smul
end Fresh.TranslatedSix
