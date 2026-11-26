import Fresh.MixedStepFour

/-!
Rules1–4,8–18. Tested actual cascade before formalisation:
large_step_four_v1.py gives72 exact full-cascade controls, including both
sides of ceiling jumps, b=15/2 and x=b, no exception.
The common packet cycle q retains every independent lap N−j(q+1).
[PROVISIONAL: counting tool] the two ceilings place a named upper opening
inside its derived AP/grid phase interval. No density or cascade cap.
-/
namespace Fresh.LargeStepFour
open Fresh Fresh.Localisation Fresh.OpeningClump Fresh.MixedStepFour

theorem upper_cycle_bands {x b T : ℝ} (q N : ℤ)
    (htlo : (1/8 : ℝ)≤T) (hthi : T≤7/24)
    (hlo : (q : ℝ)+3/4≤b*T) (hhi : b*T≤(q : ℝ)+1)
    (hopen : (x+3*b)*T=(N : ℝ)+1/8) :
    ∀d∈mixedTrain x b, (1/8 : ℝ)≤distInt (d*T) := by
  intro d hd
  simp only [mixedTrain,Finset.mem_insert,Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_of_window 0 <;> norm_num <;> nlinarith
  · apply clear_of_window 0 <;> norm_num <;> nlinarith
  · apply clear_of_window 0 <;> norm_num <;> nlinarith
  · apply clear_of_window (N-3*(q+1)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N-2*(q+1)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N-(q+1)) <;> push_cast <;> nlinarith
  · apply clear_of_window N <;> nlinarith

theorem large_step_four {x b : ℝ} (hb : 15/2≤b) (hx : b≤x) :
    ∃T : ℝ, 0<T ∧ ∀d∈mixedTrain x b, (1/8 : ℝ)≤distInt (d*T) := by
  have hbpos : 0<b := by linarith
  have hX : 0<x+3*b := by linarith
  let q : ℤ := ⌈b/8-3/4⌉
  let lo : ℝ := ((q : ℝ)+3/4)/b
  let hi : ℝ := ((q : ℝ)+1)/b
  have hq1 : b/8-3/4≤(q : ℝ) := Int.le_ceil _
  have hq2 : (q : ℝ)<b/8-3/4+1 := Int.ceil_lt_add_one _
  have hlo : (1/8 : ℝ)≤lo := by
    dsimp [lo]
    rw [le_div_iff₀ hbpos]
    linarith
  have hhi : hi≤7/24 := by
    dsimp [hi]
    rw [div_le_iff₀ hbpos]
    linarith
  have hfit : lo+1/(x+3*b)≤hi := by
    have hrecip : 1/(x+3*b)≤1/(4*b) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have he : hi=lo+1/(4*b) := by dsimp [hi,lo]; ring
    rw [he]
    linarith
  obtain ⟨hTlo,hThi,hopen⟩ := openingAfter_spec (lo:=lo) hX
  have htlo : (1/8 : ℝ)≤openingAfter (x+3*b) lo := hlo.trans hTlo
  have hthi : openingAfter (x+3*b) lo≤hi := hThi.le.trans hfit
  have hp1 : (q : ℝ)+3/4≤b*openingAfter (x+3*b) lo := by
    have hh : ((q : ℝ)+3/4)/b≤openingAfter (x+3*b) lo := hTlo
    have := (div_le_iff₀ hbpos).mp hh
    nlinarith
  have hp2 : b*openingAfter (x+3*b) lo≤(q : ℝ)+1 := by
    have hh : openingAfter (x+3*b) lo≤((q : ℝ)+1)/b := hthi
    have := (le_div_iff₀ hbpos).mp hh
    nlinarith
  exact ⟨openingAfter (x+3*b) lo,by linarith,
    upper_cycle_bands q _ htlo (hthi.trans hhi) hp1 hp2 hopen⟩

theorem large_step_four_readings {x b : ℝ} (hb : 15/2≤b) (hx : b≤x) :
    ∃T : ℝ, 0<T ∧
      (∀j : ℕ, 1≤j → j≤3 → (1/8 : ℝ)≤distInt ((j : ℝ)*T)) ∧
      ∀j : ℕ, j≤3 → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  obtain ⟨T,ht,hclear⟩ := large_step_four hb hx
  refine ⟨T,ht,?_,?_⟩
  · intro j hj1 hj3
    interval_cases j <;> apply hclear <;> norm_num [mixedTrain]
  · intro j hj3
    interval_cases j <;> apply hclear <;> norm_num [mixedTrain]

#print axioms upper_cycle_bands
#print axioms large_step_four
#print axioms large_step_four_readings
end Fresh.LargeStepFour
