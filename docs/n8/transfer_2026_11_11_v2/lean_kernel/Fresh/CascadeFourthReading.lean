import Fresh.CascadeReplacementCell

namespace Fresh.Cascade

open Set

private theorem fourth_retains_adjusted_core {a v t : ℝ}
    (hv : v ∈ Icc (27/7:ℝ) (31/7))
    (ha : (9/32:ℝ) ≤ a) (hva : (9/8:ℝ) ≤ v*a)
    (ht : AdjustedCoreTime a t) :
    LonelyAt ({1,2,v,5} : Finset ℝ) t := by
  have hfixed := retained_four (adjustedCoreTime_subset ha ht)
  intro d hd
  simp only [Finset.mem_insert,Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | he | rfl
  · exact hfixed _ (by simp)
  · exact hfixed _ (by simp)
  · subst d
    have lower {u l : ℝ} (hu : u ≤ t) (hl : 0 ≤ l) (h : l ≤ v) (ht0 : 0 ≤ t) :
        l*u ≤ v*t :=
      (mul_le_mul_of_nonneg_left hu hl).trans (mul_le_mul_of_nonneg_right h ht0)
    have upper {u l : ℝ} (hu : t ≤ u) (hl : 0 ≤ l) (h : v ≤ l) (ht0 : 0 ≤ t) :
        v*t ≤ l*u :=
      (mul_le_mul_of_nonneg_right h ht0).trans (mul_le_mul_of_nonneg_left hu hl)
    have hv0 : 0 ≤ v := by linarith [hv.1]
    rcases ht with ht | ht | rfl | rfl | ht
    · apply Fresh.Localisation.clear_of_window 0 <;> norm_num
      · have h := lower ht.1 (by norm_num) hv.1 (by linarith [ht.1])
        linarith
      · have h := upper ht.2 (by norm_num) hv.2 (by linarith [ht.1])
        linarith
    · apply Fresh.Localisation.clear_of_window 1 <;> norm_num
      · exact hva.trans (mul_le_mul_of_nonneg_left ht.1 hv0)
      · have h := upper ht.2 (by norm_num) hv.2 (by linarith [ht.1,ha])
        linarith
    · apply Fresh.Localisation.clear_of_window 1 <;> norm_num <;> linarith [hv.1,hv.2]
    · apply Fresh.Localisation.clear_of_window 2 <;> norm_num <;> linarith [hv.1,hv.2]
    · apply Fresh.Localisation.clear_of_window 3 <;> norm_num
      · have h := lower ht.1 (by norm_num) hv.1 (by linarith [ht.1])
        linarith
      · have h := upper ht.2 (by norm_num) hv.2 (by linarith [ht.1])
        linarith
  · exact hfixed _ (by simp)

/-- Move both readings that delimit the second cell. The two fast
readings still vary independently throughout the initial span. -/
theorem third_fourth_readings_replacement {s v x y : ℝ}
    (hs : s ∈ Icc (17/7:ℝ) (23/7))
    (hv : v ∈ Icc (27/7:ℝ) (31/7))
    (hx : x ∈ Icc (1:ℝ) 15) (hy : y ∈ Icc (1:ℝ) 15) :
    ∃ t ∈ Icc (1/8:ℝ) (7/8),
      LonelyAt (({1,2,v,5} : Finset ℝ) ∪ {s,x,y}) t := by
  let a : ℝ := max (9/32) (9/(8*v))
  have hv0 : 0 < v := by linarith [hv.1]
  have hden : 0 < 8*v := by positivity
  have ha : a ∈ Icc (9/32:ℝ) (7/24) := by
    refine ⟨le_max_left _ _,max_le (by norm_num) ?_⟩
    rw [div_le_iff₀ hden]
    linarith [hv.1]
  have hbackup (_ : 7/8 < s*a) :
      LonelyAt ({1,2,v,5} : Finset ℝ) (17/40) ∨
        LonelyAt ({1,2,v,5} : Finset ℝ) (9/16) := by
    by_cases hv75 : v ≤ 75/17
    · left
      intro d hd
      simp only [Finset.mem_insert,Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | he | rfl
      · exact Fresh.Localisation.clear_of_window 0 (by norm_num) (by norm_num)
      · exact Fresh.Localisation.clear_of_window 0 (by norm_num) (by norm_num)
      · subst d
        apply Fresh.Localisation.clear_of_window 1 <;> norm_num <;> linarith [hv.1]
      · exact Fresh.Localisation.clear_of_window 2 (by norm_num) (by norm_num)
    · right
      intro d hd
      simp only [Finset.mem_insert,Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | he | rfl
      · exact Fresh.Localisation.clear_of_window 0 (by norm_num) (by norm_num)
      · exact Fresh.Localisation.clear_of_window 1 (by norm_num) (by norm_num)
      · subst d
        apply Fresh.Localisation.clear_of_window 2 <;> norm_num <;> linarith [hv.1,hv.2]
      · exact Fresh.Localisation.clear_of_window 2 (by norm_num) (by norm_num)
  have hva : (9/8:ℝ) ≤ v*a := by
    have h : 9/(8*v) ≤ a := le_max_right _ _
    have hh := (div_le_iff₀ hden).mp h
    linarith
  exact replacement_of_adjusted_core ha hbackup
    (fun _ => fourth_retains_adjusted_core hv ha.1 hva) hs hx hy

#print axioms third_fourth_readings_replacement

end Fresh.Cascade
