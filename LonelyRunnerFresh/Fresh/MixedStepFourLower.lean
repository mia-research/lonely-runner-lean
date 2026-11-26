import Fresh.MixedStepFour

/-!
Rules:1–4,8–18. Same mixed-wrap packet law with its core-time band separated
from the step parameter. For8/7≤b≤2 the reference opening is selected after
1/(4b), keeping bT between1/4 and1/3 while all three frozen AP readings clear.
[PROVISIONAL: counting tool] inherited ceiling selects the named boundary.
-/
namespace Fresh.MixedStepFourLower
open Fresh Fresh.Localisation Fresh.OpeningClump Fresh.MixedStepFour

theorem mixed_at_upper_band {x b T : ℝ} (N : ℤ)
    (hlo : (1/8 : ℝ) ≤ T) (hhi : T ≤ 7/24)
    (hphaseLo : (1/4 : ℝ) ≤ b*T) (hphaseHi : b*T ≤ 1/3)
    (hopen : (x+3*b)*T=(N : ℝ)+1/8) :
    ∀ d∈mixedTrain x b, (1/8 : ℝ) ≤ distInt (d*T) := by
  intro d hd
  simp only [mixedTrain,Finset.mem_insert,Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_of_window 0 <;> norm_num <;> nlinarith
  · apply clear_of_window 0 <;> norm_num <;> nlinarith
  · apply clear_of_window 0 <;> norm_num <;> nlinarith
  · apply clear_of_window (N-1) <;> push_cast <;> nlinarith
  · apply clear_of_window (N-1) <;> push_cast <;> nlinarith
  · apply clear_of_window (N-1) <;> push_cast <;> nlinarith
  · apply clear_of_window N <;> nlinarith

theorem mixed_four_lower_family {x b : ℝ} (hblo : (8/7 : ℝ) ≤ b) (hbhi : b ≤ 2)
    (hx : 9*b ≤ x) :
    ∃ T : ℝ, 0<T ∧ ∀ d∈mixedTrain x b, (1/8 : ℝ) ≤ distInt (d*T) := by
  have hb : 0<b := by linarith
  have hz : 0<x+3*b := by linarith
  obtain ⟨hlo,hhi,hopen⟩ := openingAfter_spec (lo := 1/(4*b)) hz
  have ht : 0<openingAfter (x+3*b) (1/(4*b)) := lt_of_lt_of_le (by positivity) hlo
  have he : b*(1/(4*b))=(1/4 : ℝ) := by field_simp
  have hphaseLo : (1/4 : ℝ) ≤ b*openingAfter (x+3*b) (1/(4*b)) := by
    have hh := mul_le_mul_of_nonneg_left hlo hb.le
    rw [he] at hh
    exact hh
  have hbound : b*(1/(4*b)+1/(x+3*b)) ≤ 1/3 := by
    have hfrac : b/(x+3*b) ≤ (1/12 : ℝ) := by
      apply (div_le_iff₀ hz).2
      nlinarith
    have he' : b*(1/(4*b)+1/(x+3*b))=1/4+b/(x+3*b) := by field_simp
    rw [he']
    linarith
  have hphaseHi : b*openingAfter (x+3*b) (1/(4*b)) ≤ 1/3 :=
    (mul_le_mul_of_nonneg_left hhi.le hb.le).trans hbound
  have htimeLo : (1/8 : ℝ) ≤ openingAfter (x+3*b) (1/(4*b)) := by
    have hh : (1/8 : ℝ) ≤ 1/(4*b) := by
      apply (le_div_iff₀ (by positivity : 0<4*b)).2
      nlinarith
    exact hh.trans hlo
  have htimeHi : openingAfter (x+3*b) (1/(4*b)) ≤ (7/24 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hblo ht.le
    nlinarith
  exact ⟨_,ht,mixed_at_upper_band _ htimeLo htimeHi hphaseLo hphaseHi hopen⟩

theorem mixed_four_lower_family_readings {x b : ℝ} (hblo : (8/7 : ℝ) ≤ b) (hbhi : b ≤ 2)
    (hx : 9*b ≤ x) :
    ∃ T : ℝ, 0<T ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ 3 → (1/8 : ℝ) ≤ distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j ≤ 3 → (1/8 : ℝ) ≤ distInt ((x+(j : ℝ)*b)*T) := by
  obtain ⟨T,ht,hclear⟩ := mixed_four_lower_family hblo hbhi hx
  refine ⟨T,ht,?_,?_⟩
  · intro j hj1 hj3
    interval_cases j <;> apply hclear <;> norm_num [mixedTrain]
  · intro j hj3
    interval_cases j <;> apply hclear <;> norm_num [mixedTrain]

#print axioms mixed_at_upper_band
#print axioms mixed_four_lower_family
#print axioms mixed_four_lower_family_readings
end Fresh.MixedStepFourLower
