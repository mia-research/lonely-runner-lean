import Fresh.OpeningClump

/-!
Rules:1–4,8–18. A five-reading AP packet carried by its MIDDLE opening.
The signed phase offsets are -2bT,-bT,0,bT,2bT from1/8. Exact band
1/4≤bT≤3/8 clears two readings on the preceding lap and three on the
anchor lap, while frozen AP readings1,2 retain their first bands.
[PROVISIONAL: counting tool] inherited ceiling selects the explicit opening.
-/
open Classical
namespace Fresh.MiddleStepFive
open Fresh Fresh.Localisation Fresh.OpeningClump

noncomputable def middleTrain (x b : ℝ) : Finset ℝ :=
  {1,2,x,x+b,x+2*b,x+3*b,x+4*b}

theorem middle_at_opening {x b T : ℝ} (N : ℤ)
    (hlo : (1/8 : ℝ) ≤ T) (hhi : T ≤ 7/16)
    (hphaseLo : (1/4 : ℝ) ≤ b*T) (hphaseHi : b*T ≤ 3/8)
    (hopen : (x+2*b)*T=(N : ℝ)+1/8) :
    ∀ d∈middleTrain x b, (1/8 : ℝ) ≤ distInt (d*T) := by
  intro d hd
  simp only [middleTrain,Finset.mem_insert,Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_of_window 0 <;> norm_num <;> nlinarith
  · apply clear_of_window 0 <;> norm_num <;> nlinarith
  · apply clear_of_window (N-1) <;> push_cast <;> nlinarith
  · apply clear_of_window (N-1) <;> push_cast <;> nlinarith
  · apply clear_of_window N <;> nlinarith
  · apply clear_of_window N <;> nlinarith
  · apply clear_of_window N <;> nlinarith

theorem middle_five_lower {x b : ℝ} (hblo : (6/7 : ℝ) ≤ b) (hbhi : b ≤ 2)
    (hx : 6*b ≤ x) :
    ∃ T : ℝ, 0<T ∧ ∀ d∈middleTrain x b, (1/8 : ℝ) ≤ distInt (d*T) := by
  have hb : 0<b := by linarith
  have hz : 0<x+2*b := by linarith
  obtain ⟨hlo,hhi,hopen⟩ := openingAfter_spec (lo := 1/(4*b)) hz
  have ht : 0<openingAfter (x+2*b) (1/(4*b)) := lt_of_lt_of_le (by positivity) hlo
  have he : b*(1/(4*b))=(1/4 : ℝ) := by field_simp
  have hphaseLo : (1/4 : ℝ) ≤ b*openingAfter (x+2*b) (1/(4*b)) := by
    have hh := mul_le_mul_of_nonneg_left hlo hb.le
    rwa [he] at hh
  have hbound : b*(1/(4*b)+1/(x+2*b)) ≤ 3/8 := by
    have hfrac : b/(x+2*b) ≤ (1/8 : ℝ) := by
      apply (div_le_iff₀ hz).2
      nlinarith
    have he' : b*(1/(4*b)+1/(x+2*b))=1/4+b/(x+2*b) := by field_simp
    rw [he']
    linarith
  have hphaseHi : b*openingAfter (x+2*b) (1/(4*b)) ≤ 3/8 :=
    (mul_le_mul_of_nonneg_left hhi.le hb.le).trans hbound
  have htimeLo : (1/8 : ℝ) ≤ openingAfter (x+2*b) (1/(4*b)) := by
    have hh : (1/8 : ℝ) ≤ 1/(4*b) := by
      apply (le_div_iff₀ (by positivity : 0<4*b)).2
      nlinarith
    exact hh.trans hlo
  have htimeHi : openingAfter (x+2*b) (1/(4*b)) ≤ (7/16 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hblo ht.le
    nlinarith
  exact ⟨_,ht,middle_at_opening _ htimeLo htimeHi hphaseLo hphaseHi hopen⟩

theorem middle_five_upper {x b : ℝ} (hx : 0<x) (hb : 2 ≤ b)
    (hpoly : 2*b*(b+1) ≤ x*(3-b)) :
    ∃ T : ℝ, 0<T ∧ ∀ d∈middleTrain x b, (1/8 : ℝ) ≤ distInt (d*T) := by
  have hbpos : 0<b := by linarith
  have hz : 0<x+2*b := by linarith
  obtain ⟨hlo,hhi,hopen⟩ := openingAfter_spec (lo := (1/8 : ℝ)) hz
  have ht : 0<openingAfter (x+2*b) (1/8) := by linarith
  have hphaseLo : (1/4 : ℝ) ≤ b*openingAfter (x+2*b) (1/8) := by
    have hh := mul_le_mul_of_nonneg_left hlo hbpos.le
    nlinarith
  have hbound : b*(1/8+1/(x+2*b)) ≤ 3/8 := by
    have he : b*(1/8+1/(x+2*b))=(b*x+2*b^2+8*b)/(8*(x+2*b)) := by field_simp
    rw [he,div_le_iff₀ (by positivity : 0<8*(x+2*b))]
    nlinarith
  have hphaseHi : b*openingAfter (x+2*b) (1/8) ≤ 3/8 :=
    (mul_le_mul_of_nonneg_left hhi.le hbpos.le).trans hbound
  have htimeHi : openingAfter (x+2*b) (1/8) ≤ (7/16 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hb ht.le
    nlinarith
  exact ⟨_,ht,middle_at_opening _ hlo htimeHi hphaseLo hphaseHi hopen⟩

theorem middle_five_lower_readings {x b : ℝ} (hblo : (6/7 : ℝ) ≤ b) (hbhi : b ≤ 2)
    (hx : 6*b ≤ x) :
    ∃ T : ℝ, 0<T ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ 2 → (1/8 : ℝ) ≤ distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j ≤ 4 → (1/8 : ℝ) ≤ distInt ((x+(j : ℝ)*b)*T) := by
  obtain ⟨T,ht,hclear⟩ := middle_five_lower hblo hbhi hx
  refine ⟨T,ht,?_,?_⟩
  · intro j hj1 hj2
    interval_cases j <;> apply hclear <;> norm_num [middleTrain]
  · intro j hj4
    interval_cases j <;> apply hclear <;> norm_num [middleTrain]

theorem middle_five_upper_readings {x b : ℝ} (hx : 0<x) (hb : 2 ≤ b)
    (hpoly : 2*b*(b+1) ≤ x*(3-b)) :
    ∃ T : ℝ, 0<T ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ 2 → (1/8 : ℝ) ≤ distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j ≤ 4 → (1/8 : ℝ) ≤ distInt ((x+(j : ℝ)*b)*T) := by
  obtain ⟨T,ht,hclear⟩ := middle_five_upper hx hb hpoly
  refine ⟨T,ht,?_,?_⟩
  · intro j hj1 hj2
    interval_cases j <;> apply hclear <;> norm_num [middleTrain]
  · intro j hj4
    interval_cases j <;> apply hclear <;> norm_num [middleTrain]

#print axioms middle_at_opening
#print axioms middle_five_lower
#print axioms middle_five_upper
#print axioms middle_five_lower_readings
#print axioms middle_five_upper_readings
end Fresh.MiddleStepFive
