import Fresh.OpeningClump

/-!
Rules1–4,8–18. Actual width-boundary source: core{1,2,3} and four fast
readings x,x+2,x+4,x+6. At x=161±1/64 distinct first openings merge
at the UPPER packet opening, whereas openingAfter x(1/8) fails.
The upper reading uses wrapN and the lower three use wrapN−1.
[PROVISIONAL: counting tool] selects the explicit upper opening/floor lap;
no covering, uniform cascade cap or future-isolation premise is used.
-/
namespace Fresh.MixedStepFour
open Fresh Fresh.Localisation Fresh.OpeningClump

noncomputable def mixedTrain (x b : ℝ) : Finset ℝ :=
  {1,2,3,x,x+b,x+2*b,x+3*b}

theorem mixed_at_upper {x b T : ℝ} (N : ℤ) (hb : 2≤b)
    (hlo : (1/8 : ℝ)≤T) (hhi : b*T≤1/3)
    (hopen : (x+3*b)*T=(N : ℝ)+1/8) :
    ∀d∈mixedTrain x b, (1/8 : ℝ)≤distInt (d*T) := by
  have ht : 0<T := by linarith
  have hphase : (1/4 : ℝ)≤b*T := by nlinarith
  have htupper : T≤1/6 := by nlinarith
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

theorem mixed_four_upper_family {x b : ℝ} (hx : 0<x) (hb : 2≤b)
    (hsep : 9*b^2≤x*(8-3*b)) :
    ∃T : ℝ, 0<T ∧ ∀d∈mixedTrain x b, (1/8 : ℝ)≤distInt (d*T) := by
  have hz : 0<x+3*b := by linarith
  obtain ⟨hlo,hhi,hopen⟩ := openingAfter_spec (lo:=(1/8 : ℝ)) hz
  have hbound : b*(1/8+1/(x+3*b))≤1/3 := by
    have he : b*(1/8+1/(x+3*b))=(b*x+3*b^2+8*b)/(8*(x+3*b)) := by field_simp
    rw [he,div_le_iff₀ (by positivity : 0<8*(x+3*b))]
    nlinarith
  have hphase : b*openingAfter (x+3*b) (1/8)≤1/3 :=
    (mul_le_mul_of_nonneg_left hhi.le (by linarith : 0≤b)).trans hbound
  exact ⟨openingAfter (x+3*b) (1/8),by linarith,
    mixed_at_upper _ hb hlo hphase hopen⟩

theorem mixed_four_upper_family_readings {x b : ℝ} (hx : 0<x) (hb : 2≤b)
    (hsep : 9*b^2≤x*(8-3*b)) :
    ∃T : ℝ, 0<T ∧
      (∀j : ℕ, 1≤j → j≤3 → (1/8 : ℝ)≤distInt ((j : ℝ)*T)) ∧
      ∀j : ℕ, j≤3 → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  obtain ⟨T,ht,hclear⟩ := mixed_four_upper_family hx hb hsep
  refine ⟨T,ht,?_,?_⟩
  · intro j hj1 hj3
    interval_cases j <;> apply hclear <;> norm_num [mixedTrain]
  · intro j hj3
    interval_cases j <;> apply hclear <;> norm_num [mixedTrain]

#print axioms mixed_four_upper_family_readings

/-- The top-opening lap intervals overlap for every n≥3. -/
theorem mixed_four_two_repeated (n : ℤ) (hn : 3≤n) (x : ℝ)
    (hlo : 6*(n : ℝ)-21/4≤x) (hhi : x≤8*(n : ℝ)-5) :
    ∃T : ℝ, 0<T ∧ ∀d∈mixedTrain x 2, (1/8 : ℝ)≤distInt (d*T) := by
  have hnR : (3 : ℝ)≤n := by exact_mod_cast hn
  have hx : 0<x+6 := by linarith
  let T : ℝ := (8*(n : ℝ)+1)/(8*(x+6))
  have htlo : (1/8 : ℝ)≤T := by
    dsimp [T]
    rw [le_div_iff₀ (by positivity : 0<8*(x+6))]
    nlinarith
  have hthi : T≤1/6 := by
    dsimp [T]
    rw [div_le_iff₀ (by positivity : 0<8*(x+6))]
    nlinarith
  have hopen : (x+3*2)*T=(n : ℝ)+1/8 := by dsimp [T]; field_simp; ring
  exact ⟨T,by linarith,mixed_at_upper n (by norm_num) htlo (by nlinarith) hopen⟩

/-- Unbounded real base, with no supplied opening lap. -/
theorem mixed_four_two_tail (x : ℝ) (hx : 51/4≤x) :
    ∃T : ℝ, 0<T ∧ ∀d∈mixedTrain x 2, (1/8 : ℝ)≤distInt (d*T) := by
  let n : ℤ := ⌊(x+21/4)/6⌋
  have hn : (3 : ℤ)≤n := by
    apply Int.le_floor.mpr
    norm_num
    linarith
  have h1 : (n : ℝ)≤(x+21/4)/6 := Int.floor_le _
  have h2 : (x+21/4)/6<(n : ℝ)+1 := Int.lt_floor_add_one _
  have hnR : (3 : ℝ)≤n := by exact_mod_cast hn
  exact mixed_four_two_repeated n hn x (by linarith) (by linarith)

theorem mixed_four_two_tail_readings (x : ℝ) (hx : 51/4≤x) :
    ∃T : ℝ, 0<T ∧
      (∀j : ℕ, 1≤j → j≤3 → (1/8 : ℝ)≤distInt ((j : ℝ)*T)) ∧
      ∀j : ℕ, j≤3 → (1/8 : ℝ)≤distInt ((x+2*(j : ℝ))*T) := by
  obtain ⟨T,ht,hclear⟩ := mixed_four_two_tail x hx
  refine ⟨T,ht,?_,?_⟩
  · intro j hj1 hj3
    interval_cases j <;> apply hclear <;> norm_num [mixedTrain]
  · intro j hj3
    interval_cases j <;> apply hclear <;> norm_num [mixedTrain]

#print axioms mixed_at_upper
#print axioms mixed_four_upper_family
#print axioms mixed_four_two_repeated
#print axioms mixed_four_two_tail
#print axioms mixed_four_two_tail_readings
end Fresh.MixedStepFour
