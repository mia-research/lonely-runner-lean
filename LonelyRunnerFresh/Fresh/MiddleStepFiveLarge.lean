import Fresh.MiddleStepFive

/-!
Rules:1–4,8–18. The middle five-packet law repeats on every integer
step-phase cycle. A derived cycle retains independent packet lap labels;
this removes a bounded step-ratio restriction without changing the anchor.
[PROVISIONAL: counting tool] the two ceilings locate the named middle opening.
-/
namespace Fresh.MiddleStepFiveLarge
open Fresh Fresh.Localisation Fresh.OpeningClump Fresh.MiddleStepFive

theorem middle_cycle_bands {x b T : ℝ} (q N : ℤ)
    (hlo : (1/8 : ℝ) ≤ T) (hhi : T ≤ 7/16)
    (hpLo : (q : ℝ)+1/4 ≤ b*T) (hpHi : b*T ≤ (q : ℝ)+3/8)
    (hopen : (x+2*b)*T=(N : ℝ)+1/8) :
    ∀ d∈middleTrain x b, (1/8 : ℝ) ≤ distInt (d*T) := by
  intro d hd
  simp only [middleTrain,Finset.mem_insert,Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_of_window 0 <;> norm_num <;> nlinarith
  · apply clear_of_window 0 <;> norm_num <;> nlinarith
  · apply clear_of_window (N-2*q-1) <;> push_cast <;> nlinarith
  · apply clear_of_window (N-q-1) <;> push_cast <;> nlinarith
  · apply clear_of_window N <;> nlinarith
  · apply clear_of_window (N+q) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+2*q) <;> push_cast <;> nlinarith

theorem middle_five_large {x b : ℝ} (hb : (18/5 : ℝ) ≤ b) (hx : 6*b ≤ x) :
    ∃ T : ℝ, 0<T ∧ ∀ d∈middleTrain x b, (1/8 : ℝ) ≤ distInt (d*T) := by
  have hbpos : 0<b := by linarith
  have hX : 0<x+2*b := by linarith
  let q : ℤ := ⌈b/8-1/4⌉
  let lo : ℝ := ((q : ℝ)+1/4)/b
  let hi : ℝ := ((q : ℝ)+3/8)/b
  have hq1 : b/8-1/4 ≤ (q : ℝ) := Int.le_ceil _
  have hq2 : (q : ℝ)<b/8-1/4+1 := Int.ceil_lt_add_one _
  have hlo : (1/8 : ℝ) ≤ lo := by
    dsimp [lo]
    rw [le_div_iff₀ hbpos]
    linarith
  have hhi : hi ≤ (7/16 : ℝ) := by
    dsimp [hi]
    rw [div_le_iff₀ hbpos]
    linarith
  have hfit : lo+1/(x+2*b) ≤ hi := by
    have hh : 1/(x+2*b) ≤ 1/(8*b) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have he : hi=lo+1/(8*b) := by dsimp [hi,lo]; ring
    rw [he]
    linarith
  obtain ⟨hTlo,hThi,hopen⟩ := openingAfter_spec (lo := lo) hX
  have htlo : (1/8 : ℝ) ≤ openingAfter (x+2*b) lo := hlo.trans hTlo
  have hthi : openingAfter (x+2*b) lo ≤ hi := hThi.le.trans hfit
  have hp1 : (q : ℝ)+1/4 ≤ b*openingAfter (x+2*b) lo := by
    have hh : ((q : ℝ)+1/4)/b ≤ openingAfter (x+2*b) lo := hTlo
    have := (div_le_iff₀ hbpos).mp hh
    nlinarith
  have hp2 : b*openingAfter (x+2*b) lo ≤ (q : ℝ)+3/8 := by
    have hh : openingAfter (x+2*b) lo ≤ ((q : ℝ)+3/8)/b := hthi
    have := (le_div_iff₀ hbpos).mp hh
    nlinarith
  exact ⟨_,by linarith,middle_cycle_bands q _ htlo (hthi.trans hhi) hp1 hp2 hopen⟩

theorem middle_five_large_readings {x b : ℝ} (hb : (18/5 : ℝ) ≤ b) (hx : 6*b ≤ x) :
    ∃ T : ℝ, 0<T ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ 2 → (1/8 : ℝ) ≤ distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j ≤ 4 → (1/8 : ℝ) ≤ distInt ((x+(j : ℝ)*b)*T) := by
  obtain ⟨T,ht,hclear⟩ := middle_five_large hb hx
  refine ⟨T,ht,?_,?_⟩
  · intro j hj1 hj2
    interval_cases j <;> apply hclear <;> norm_num [middleTrain]
  · intro j hj4
    interval_cases j <;> apply hclear <;> norm_num [middleTrain]

#print axioms middle_cycle_bands
#print axioms middle_five_large
#print axioms middle_five_large_readings
end Fresh.MiddleStepFiveLarge
