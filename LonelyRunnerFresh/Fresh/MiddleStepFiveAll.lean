import Fresh.MiddleStepFiveLarge

/-!
Rules:1–4,8–18. All step ratios b≥6/7 for a two-reading AP core and a
five-reading AP packet with x≥6b. Two middle-anchor phase bands and the
whole-cycle repeat join the previously separate ratio intervals.
[PROVISIONAL: counting tool] exact opening/cycle ceilings;
[PROVISIONAL: covering] finite step-parameter split, named in middle_five_all.
-/
namespace Fresh.MiddleStepFiveAll
open Fresh Fresh.Localisation Fresh.OpeningClump Fresh.MiddleStepFive Fresh.MiddleStepFiveLarge

theorem middle_second_bands {x b T : ℝ} (N : ℤ)
    (hlo : (1/8 : ℝ) ≤ T) (hhi : T ≤ 7/16)
    (hpLo : (5/8 : ℝ) ≤ b*T) (hpHi : b*T ≤ 3/4)
    (hopen : (x+2*b)*T=(N : ℝ)+1/8) :
    ∀ d∈middleTrain x b, (1/8 : ℝ) ≤ distInt (d*T) := by
  intro d hd
  simp only [middleTrain,Finset.mem_insert,Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_of_window 0 <;> norm_num <;> nlinarith
  · apply clear_of_window 0 <;> norm_num <;> nlinarith
  · apply clear_of_window (N-2) <;> push_cast <;> nlinarith
  · apply clear_of_window (N-1) <;> push_cast <;> nlinarith
  · apply clear_of_window N <;> nlinarith
  · apply clear_of_window N <;> nlinarith
  · apply clear_of_window (N+1) <;> push_cast <;> nlinarith

theorem middle_five_second {x b : ℝ} (hblo : (12/7 : ℝ) ≤ b) (hbhi : b ≤ 5)
    (hx : 6*b ≤ x) :
    ∃ T : ℝ, 0<T ∧ ∀ d∈middleTrain x b, (1/8 : ℝ) ≤ distInt (d*T) := by
  have hb : 0<b := by linarith
  have hz : 0<x+2*b := by linarith
  obtain ⟨hlo,hhi,hopen⟩ := openingAfter_spec (lo := 5/(8*b)) hz
  have ht : 0<openingAfter (x+2*b) (5/(8*b)) := lt_of_lt_of_le (by positivity) hlo
  have he : b*(5/(8*b))=(5/8 : ℝ) := by field_simp
  have hphaseLo : (5/8 : ℝ) ≤ b*openingAfter (x+2*b) (5/(8*b)) := by
    have hh := mul_le_mul_of_nonneg_left hlo hb.le
    rwa [he] at hh
  have hbound : b*(5/(8*b)+1/(x+2*b)) ≤ 3/4 := by
    have hfrac : b/(x+2*b) ≤ (1/8 : ℝ) := by
      apply (div_le_iff₀ hz).2
      nlinarith
    have he' : b*(5/(8*b)+1/(x+2*b))=5/8+b/(x+2*b) := by field_simp
    rw [he']
    linarith
  have hphaseHi : b*openingAfter (x+2*b) (5/(8*b)) ≤ 3/4 :=
    (mul_le_mul_of_nonneg_left hhi.le hb.le).trans hbound
  have htimeLo : (1/8 : ℝ) ≤ openingAfter (x+2*b) (5/(8*b)) := by
    have hh : (1/8 : ℝ) ≤ 5/(8*b) := by
      apply (le_div_iff₀ (by positivity : 0<8*b)).2
      nlinarith
    exact hh.trans hlo
  have htimeHi : openingAfter (x+2*b) (5/(8*b)) ≤ (7/16 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hblo ht.le
    nlinarith
  exact ⟨_,ht,middle_second_bands _ htimeLo htimeHi hphaseLo hphaseHi hopen⟩

theorem middle_five_all {x b : ℝ} (hb : (6/7 : ℝ) ≤ b) (hx : 6*b ≤ x) :
    ∃ T : ℝ, 0<T ∧ ∀ d∈middleTrain x b, (1/8 : ℝ) ≤ distInt (d*T) := by
  by_cases h2 : b ≤ 2
  · exact middle_five_lower hb h2 hx
  by_cases h5 : b ≤ 5
  · exact middle_five_second (by linarith) h5 hx
  · exact middle_five_large (by linarith) hx

theorem middle_five_all_readings {x b : ℝ} (hb : (6/7 : ℝ) ≤ b) (hx : 6*b ≤ x) :
    ∃ T : ℝ, 0<T ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ 2 → (1/8 : ℝ) ≤ distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j ≤ 4 → (1/8 : ℝ) ≤ distInt ((x+(j : ℝ)*b)*T) := by
  obtain ⟨T,ht,hclear⟩ := middle_five_all hb hx
  refine ⟨T,ht,?_,?_⟩
  · intro j hj1 hj2
    interval_cases j <;> apply hclear <;> norm_num [middleTrain]
  · intro j hj4
    interval_cases j <;> apply hclear <;> norm_num [middleTrain]

#print axioms middle_second_bands
#print axioms middle_five_second
#print axioms middle_five_all
#print axioms middle_five_all_readings
end Fresh.MiddleStepFiveAll
