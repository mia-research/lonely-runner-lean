import Fresh.MixedStepFourLower
import Fresh.LargeStepFour

/-!
Rules1–4,8–18. Actual cascade controls preceded formalisation:
step_four_all_v1.py checks144 parameter cases/all1152 physical subjects,
including both sides of phase cuts and the closed x=21b boundary.
[PROVISIONAL: counting tool] the upper opening lies within one revolution;
[PROVISIONAL: covering] the finite STEP-PARAMETER split joins the exact
phase bands. No time-window covering, density or uniform stopping cap.
-/
namespace Fresh.StepFourAll
open Fresh Fresh.Localisation Fresh.OpeningClump Fresh.MixedStepFour
open Fresh.MixedStepFourLower Fresh.LargeStepFour

theorem short_phase_opening {x b α : ℝ} (hb : 0<b) (hx : 21*b≤x)
    (hlo : b≤8*α) (hhi : 24*α+1≤7*b) :
    ∃T : ℝ, ∃N : ℤ, 0<T ∧ (1/8 : ℝ)≤T ∧ T≤7/24 ∧
      α≤b*T ∧ b*T≤α+1/24 ∧ (x+3*b)*T=(N : ℝ)+1/8 := by
  have hX : 0<x+3*b := by linarith
  let lo : ℝ := α/b
  obtain ⟨h1,h2,h3⟩ := openingAfter_spec (lo:=lo) hX
  have hlow : (1/8 : ℝ)≤lo := by
    dsimp [lo]; rw [le_div_iff₀ hb]; linarith
  have hfit : lo+1/(x+3*b)≤(α+1/24)/b := by
    have hh : 1/(x+3*b)≤1/(24*b) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have he : (α+1/24)/b=lo+1/(24*b) := by dsimp [lo]; ring
    rw [he]; linarith
  have htlo : (1/8 : ℝ)≤openingAfter (x+3*b) lo := hlow.trans h1
  have htphasehi : openingAfter (x+3*b) lo≤(α+1/24)/b := h2.le.trans hfit
  have htcorehi : (α+1/24)/b≤7/24 := by rw [div_le_iff₀ hb]; linarith
  refine ⟨openingAfter (x+3*b) lo,_,by linarith,htlo,htphasehi.trans htcorehi,?_,?_,h3⟩
  · have hh : α/b≤openingAfter (x+3*b) lo := h1
    have := (div_le_iff₀ hb).mp hh
    nlinarith
  · have := (le_div_iff₀ hb).mp htphasehi
    nlinarith

theorem quarter_cycle_bands {x b T : ℝ} (q N : ℤ)
    (htlo : (1/8 : ℝ)≤T) (hthi : T≤7/24)
    (hlo : (q : ℝ)+1/4≤b*T) (hhi : b*T≤(q : ℝ)+1/3)
    (hopen : (x+3*b)*T=(N : ℝ)+1/8) :
    ∀d∈mixedTrain x b, (1/8 : ℝ)≤distInt (d*T) := by
  intro d hd
  simp only [mixedTrain,Finset.mem_insert,Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_of_window 0 <;> norm_num <;> nlinarith
  · apply clear_of_window 0 <;> norm_num <;> nlinarith
  · apply clear_of_window 0 <;> norm_num <;> nlinarith
  · apply clear_of_window (N-3*q-1) <;> push_cast <;> nlinarith
  · apply clear_of_window (N-2*q-1) <;> push_cast <;> nlinarith
  · apply clear_of_window (N-q-1) <;> push_cast <;> nlinarith
  · apply clear_of_window N <;> nlinarith

theorem five_twelfths_bands {x b T : ℝ} (N : ℤ)
    (htlo : (1/8 : ℝ)≤T) (hthi : T≤7/24)
    (hlo : (5/12 : ℝ)≤b*T) (hhi : b*T≤1/2)
    (hopen : (x+3*b)*T=(N : ℝ)+1/8) :
    ∀d∈mixedTrain x b, (1/8 : ℝ)≤distInt (d*T) := by
  intro d hd
  simp only [mixedTrain,Finset.mem_insert,Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_of_window 0 <;> norm_num <;> nlinarith
  · apply clear_of_window 0 <;> norm_num <;> nlinarith
  · apply clear_of_window 0 <;> norm_num <;> nlinarith
  · apply clear_of_window (N-2) <;> push_cast <;> nlinarith
  · apply clear_of_window (N-1) <;> push_cast <;> nlinarith
  · apply clear_of_window (N-1) <;> push_cast <;> nlinarith
  · apply clear_of_window N <;> nlinarith

theorem five_eighths_bands {x b T : ℝ} (N : ℤ)
    (htlo : (1/8 : ℝ)≤T) (hthi : T≤7/24)
    (hlo : (5/8 : ℝ)≤b*T) (hhi : b*T≤2/3)
    (hopen : (x+3*b)*T=(N : ℝ)+1/8) :
    ∀d∈mixedTrain x b, (1/8 : ℝ)≤distInt (d*T) := by
  intro d hd
  simp only [mixedTrain,Finset.mem_insert,Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_of_window 0 <;> norm_num <;> nlinarith
  · apply clear_of_window 0 <;> norm_num <;> nlinarith
  · apply clear_of_window 0 <;> norm_num <;> nlinarith
  · apply clear_of_window (N-2) <;> push_cast <;> nlinarith
  · apply clear_of_window (N-2) <;> push_cast <;> nlinarith
  · apply clear_of_window (N-1) <;> push_cast <;> nlinarith
  · apply clear_of_window N <;> nlinarith

/-- All step ratios at least1, with one arrangement separation inequality. -/
theorem step_four_all {x b : ℝ} (hb : 1≤b) (hx : 21*b≤x) :
    ∃T : ℝ, 0<T ∧ ∀d∈mixedTrain x b, (1/8 : ℝ)≤distInt (d*T) := by
  have hbpos : 0<b := by linarith
  by_cases hlarge : 15/2≤b
  · exact large_step_four hlarge (by linarith)
  by_cases h0 : b≤2
  · obtain ⟨T,N,ht,htlo,hthi,hp1,hp2,hopen⟩ :=
      short_phase_opening (α:=1/4) hbpos hx (by linarith) (by linarith)
    exact ⟨T,ht,mixed_at_upper_band N htlo hthi hp1 (by linarith) hopen⟩
  by_cases h1 : b≤10/3
  · obtain ⟨T,N,ht,htlo,hthi,hp1,hp2,hopen⟩ :=
      short_phase_opening (α:=5/12) hbpos hx (by linarith) (by linarith)
    exact ⟨T,ht,five_twelfths_bands N htlo hthi hp1 (by linarith) hopen⟩
  by_cases h2 : b≤5
  · obtain ⟨T,N,ht,htlo,hthi,hp1,hp2,hopen⟩ :=
      short_phase_opening (α:=5/8) hbpos hx (by linarith) (by linarith)
    exact ⟨T,ht,five_eighths_bands N htlo hthi hp1 (by linarith) hopen⟩
  by_cases h3 : b≤6
  · obtain ⟨T,N,ht,htlo,hthi,hp1,hp2,hopen⟩ :=
      short_phase_opening (α:=3/4) hbpos hx (by linarith) (by linarith)
    exact ⟨T,ht,upper_cycle_bands 0 N htlo hthi (by norm_num; exact hp1) (by norm_num; linarith) hopen⟩
  · obtain ⟨T,N,ht,htlo,hthi,hp1,hp2,hopen⟩ :=
      short_phase_opening (α:=5/4) hbpos hx (by linarith) (by linarith)
    exact ⟨T,ht,quarter_cycle_bands 1 N htlo hthi (by norm_num; exact hp1) (by norm_num; linarith) hopen⟩

theorem step_four_all_readings {x b : ℝ} (hb : 1≤b) (hx : 21*b≤x) :
    ∃T : ℝ, 0<T ∧
      (∀j : ℕ, 1≤j → j≤3 → (1/8 : ℝ)≤distInt ((j : ℝ)*T)) ∧
      ∀j : ℕ, j≤3 → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  obtain ⟨T,ht,hclear⟩ := step_four_all hb hx
  refine ⟨T,ht,?_,?_⟩
  · intro j hj1 hj3
    interval_cases j <;> apply hclear <;> norm_num [mixedTrain]
  · intro j hj3
    interval_cases j <;> apply hclear <;> norm_num [mixedTrain]

#print axioms short_phase_opening
#print axioms quarter_cycle_bands
#print axioms five_twelfths_bands
#print axioms five_eighths_bands
#print axioms step_four_all
#print axioms step_four_all_readings
end Fresh.StepFourAll
