import Fresh.TranslatedSix
import Fresh.Framework
import Fresh.Localisation

/-! Five closed parameter charts join the recurring translated-six flank.
Each chart retains all seven exact bands, including equality endpoints.
[PROVISIONAL: covering] supports the parameter split in `translated_six_all`;
no time-window covering or uniform stopping bound is assumed. -/

namespace Fresh.TranslatedSix

theorem small_0 (a : ℝ) (ha : 1 ≤ a) (hb : a ≤ 2) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ train a, (1 / 8 : ℝ) ≤ distInt (d * t) := by
  have hd : (0 : ℝ) < 1 := by linarith
  refine ⟨(1 : ℝ) / (8 * 1), by positivity, fun d hmem => ?_⟩
  simp only [train, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith

theorem small_1 (a : ℝ) (ha : 2 ≤ a) (hb : a ≤ (19 / 8 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ train a, (1 / 8 : ℝ) ≤ distInt (d * t) := by
  have hd : (0 : ℝ) < (a + 1) := by linarith
  refine ⟨(9 : ℝ) / (8 * (a + 1)), by positivity, fun d hmem => ?_⟩
  simp only [train, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith

theorem small_2 (a : ℝ) (ha : (9 / 4 : ℝ) ≤ a) (hb : a ≤ (7 / 2 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ train a, (1 / 8 : ℝ) ≤ distInt (d * t) := by
  have hd : (0 : ℝ) < (a + 4) := by linarith
  refine ⟨(25 : ℝ) / (8 * (a + 4)), by positivity, fun d hmem => ?_⟩
  simp only [train, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (3 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (3 : ℤ) <;> norm_num <;> nlinarith

theorem small_3 (a : ℝ) (ha : (27 / 8 : ℝ) ≤ a) (hb : a ≤ (11 / 2 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ train a, (1 / 8 : ℝ) ≤ distInt (d * t) := by
  have hd : (0 : ℝ) < (a + 3) := by linarith
  refine ⟨(17 : ℝ) / (8 * (a + 3)), by positivity, fun d hmem => ?_⟩
  simp only [train, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (1 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith

theorem small_4 (a : ℝ) (ha : (21 / 4 : ℝ) ≤ a) (hb : a ≤ (115 / 18 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ train a, (1 / 8 : ℝ) ≤ distInt (d * t) := by
  have hd : (0 : ℝ) < (a + 5) := by linarith
  refine ⟨(41 : ℝ) / (8 * (a + 5)), by positivity, fun d hmem => ?_⟩
  simp only [train, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (2 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (3 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (3 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (4 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (4 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (5 : ℤ) <;> norm_num <;> nlinarith

/-- [PROVISIONAL: covering] the five parameter charts and repeated tail
exhaust the one-parameter translated-six family. -/
theorem translated_six_all (a : ℝ) (ha : 1 ≤ a) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ train a, (1 / 8 : ℝ) ≤ distInt (d * t) := by
  by_cases h0 : a ≤ 2
  · exact small_0 a ha h0
  by_cases h1 : a ≤ 19 / 8
  · exact small_1 a (by linarith) h1
  by_cases h2 : a ≤ 7 / 2
  · exact small_2 a (by linarith) h2
  by_cases h3 : a ≤ 11 / 2
  · exact small_3 a (by linarith) h3
  by_cases h4 : a ≤ 115 / 18
  · exact small_4 a (by linarith) h4
  exact repeated_tail a (by linarith)

-- STANDING: DEFINITION
def TranslatedSixClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ s a : ℝ, 0 < s ∧ 1 ≤ a ∧
    ∀ d ∈ disparitySet v k, ∃ q ∈ train a, d = s * q

theorem translatedSix_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : TranslatedSixClass v k) : Isolation v k := by
  obtain ⟨s, a, hs, ha, hmem⟩ := h
  obtain ⟨t, ht, hclear⟩ := translated_six_all a ha
  refine ⟨t / s, by positivity, ?_⟩
  rw [Fresh.Localisation.isolatedAt_iff]
  intro d hd
  obtain ⟨q, hq, rfl⟩ := hmem d hd
  have he : s * q * (t / s) = q * t := by field_simp
  rw [he]
  exact hclear q hq

#print axioms small_0
#print axioms small_1
#print axioms small_2
#print axioms small_3
#print axioms small_4
#print axioms translated_six_all
#print axioms translatedSix_isolation

end Fresh.TranslatedSix
