import Fresh.CascadeRadiusGrowth

namespace Fresh.Cascade

open Set

/-- Rejection of the first slow cell forces overlapping blocked
intervals. This records both possible roles of the right blocker. -/
theorem first_slow_cell_at_moving_close {p q w : ℝ}
    (hw : w ∈ Icc (49/10:ℝ) (46/9))
    (hp : p ∈ Icc (1:ℝ) 15) (hq : q ∈ Icc (1:ℝ) 15)
    (h : InWay p (1/8)) :
    (∃ t ∈ Icc (1/8:ℝ) (7/(8*w)), ¬ InWay p t ∧ ¬ InWay q t) ∨
      (7 < p ∧ p < 9 ∧
        ((w < q ∧ 7*q < 9*w ∧ 7*p < 9*q) ∨
          (15*w < 7*q ∧ 7*q < 17*w ∧ 5*p < 3*q))) := by
  have h7 : 7 < p := by
    by_contra! hle
    apply (not_inWay_iff.mpr _) h
    apply Fresh.Localisation.clear_of_window 0 <;> norm_num <;> linarith [hp.1]
  have h9 : p < 9 := by
    by_contra! hge
    exact (first_opening_after_rollover (m := 1) (by norm_num)
      (by linarith) (by linarith [hp.2])) (by simpa using h)
  have hp0 : 0 < p := by linarith
  have hw0 : 0 < w := by linarith [hw.1]
  have hden : 0 < 8*w := by positivity
  let u := 9/(8*p)
  have hu : u ∈ Icc (1/8:ℝ) (7/(8*w)) := by
    constructor
    · dsimp [u]
      rw [le_div_iff₀ (by positivity)]
      linarith [hw.1]
    · dsimp [u]
      rw [div_le_div_iff₀ (by positivity) hden]
      linarith [hw.2]
  have hpu : ¬ InWay p u := by
    apply not_inWay_iff.mpr
    have he : p*u = 9/8 := by dsimp [u]; field_simp
    rw [he]
    exact Fresh.Localisation.clear_of_window 1 (by norm_num) (by norm_num)
  have hpb : ¬ InWay p (7/(8*w)) := by
    apply not_inWay_iff.mpr
    apply Fresh.Localisation.clear_of_window 1 <;>
      rw [← mul_div_assoc] <;> norm_num
    · rw [le_div_iff₀ hden]
      linarith [hw.2]
    · rw [div_le_iff₀ hden]
      linarith [hw.1]
  by_cases hqu : InWay q u
  swap
  · exact Or.inl ⟨u,hu,hpu,hqu⟩
  by_cases hqb : InWay q (7/(8*w))
  swap
  · exact Or.inl ⟨7/(8*w),⟨hu.1.trans hu.2,le_rfl⟩,hpb,hqb⟩
  have hqcases : (w < q ∧ 7*q < 9*w) ∨ (15*w < 7*q ∧ 7*q < 17*w) := by
    by_cases hlow : 7*q < 9*w
    · left
      refine ⟨?_,hlow⟩
      by_contra! hle
      apply (not_inWay_iff.mpr _) hqb
      apply Fresh.Localisation.clear_of_window 0 <;> rw [← mul_div_assoc] <;> norm_num
      · rw [le_div_iff₀ hden]
        linarith [hq.1,hw.2]
      · rw [div_le_iff₀ hden]
        linarith
    right
    constructor
    · by_contra! hhi
      apply (not_inWay_iff.mpr _) hqb
      apply Fresh.Localisation.clear_of_window 1 <;> rw [← mul_div_assoc] <;> norm_num
      · rw [le_div_iff₀ hden]
        linarith
      · rw [div_le_iff₀ hden]
        linarith
    · by_contra! hhi
      apply (not_inWay_iff.mpr _) hqb
      apply Fresh.Localisation.clear_of_window 2 <;> rw [← mul_div_assoc] <;> norm_num
      · rw [le_div_iff₀ hden]
        linarith
      · rw [div_le_iff₀ hden]
        linarith [hq.2,hw.1]
  right
  refine ⟨h7,h9,?_⟩
  rcases hqcases with ⟨hL,hU⟩ | ⟨hL,hU⟩
  · left
    refine ⟨hL,hU,?_⟩
    by_contra! hle
    apply (not_inWay_iff.mpr _) hqu
    apply Fresh.Localisation.clear_of_window 0 <;> norm_num
    · dsimp [u]
      rw [← mul_div_assoc,le_div_iff₀ (by positivity)]
      linarith [hw.1]
    · dsimp [u]
      rw [← mul_div_assoc,div_le_iff₀ (by positivity)]
      linarith
  · right
    refine ⟨hL,hU,?_⟩
    by_contra! hle
    apply (not_inWay_iff.mpr _) hqu
    apply Fresh.Localisation.clear_of_window 1 <;> norm_num
    · dsimp [u]
      rw [← mul_div_assoc,le_div_iff₀ (by positivity)]
      linarith [hw.1]
    · dsimp [u]
      rw [← mul_div_assoc,div_le_iff₀ (by positivity)]
      linarith

/-- Specialization to the original first slow cell. -/
theorem first_slow_cell_dispatch {p q : ℝ}
    (hp : p ∈ Icc (1:ℝ) 15) (hq : q ∈ Icc (1:ℝ) 15)
    (h : InWay p (1/8)) :
    (∃ t ∈ Icc (1/8:ℝ) (7/40), ¬ InWay p t ∧ ¬ InWay q t) ∨
      (7 < p ∧ p < 9 ∧
        ((5 < q ∧ q < 45/7 ∧ 7*p < 9*q) ∨
          (75/7 < q ∧ q < 85/7 ∧ 5*p < 3*q))) := by
  rcases first_slow_cell_at_moving_close (w := 5) (by constructor <;> norm_num) hp hq h
    with h | ⟨h7,h9,hq'⟩
  · have he : (7:ℝ)/(8*5) = 7/40 := by norm_num
    exact Or.inl (by simpa only [he] using h)
  · right
    refine ⟨h7,h9,?_⟩
    rcases hq' with ⟨hL,hU,hO⟩ | ⟨hL,hU,hO⟩
    · exact Or.inl ⟨hL,by linarith,hO⟩
    · exact Or.inr ⟨by linarith,by linarith,hO⟩

/-- The two rates can vary independently. If the first slow cell
rejects them, one of three later times clears both. -/
theorem two_rates_clear_cells {x y : ℝ}
    (hx : x ∈ Icc (1:ℝ) 15) (hy : y ∈ Icc (1:ℝ) 15) :
    (∃ t ∈ Icc (1/8:ℝ) (7/40), ¬ InWay x t ∧ ¬ InWay y t) ∨
      (¬ InWay x (7/24) ∧ ¬ InWay y (7/24)) ∨
      (¬ InWay x (3/8) ∧ ¬ InWay y (3/8)) ∨
      ((x < 17/3 ∨ y < 17/3) ∧ ¬ InWay x (5/8) ∧ ¬ InWay y (5/8)) := by
  have dispatch {p q : ℝ} (hp : p ∈ Icc (1:ℝ) 15) (hq : q ∈ Icc (1:ℝ) 15)
      (h : InWay p (1/8)) :
      (∃ t ∈ Icc (1/8:ℝ) (7/40), ¬ InWay p t ∧ ¬ InWay q t) ∨
        (¬ InWay p (7/24) ∧ ¬ InWay q (7/24)) ∨
        (¬ InWay p (3/8) ∧ ¬ InWay q (3/8)) ∨
        ((p < 17/3 ∨ q < 17/3) ∧ ¬ InWay p (5/8) ∧ ¬ InWay q (5/8)) := by
    rcases first_slow_cell_dispatch hp hq h with hfirst | ⟨h7,h9,hqcases⟩
    · exact Or.inl hfirst
    by_cases h51 : (51/7:ℝ) ≤ p
    · right
      left
      refine ⟨not_inWay_iff.mpr ?_,not_inWay_iff.mpr ?_⟩
      · apply Fresh.Localisation.clear_of_window 2 <;> norm_num <;> linarith
      rcases hqcases with ⟨hqL,hqU,hqo⟩ | ⟨hqL,hqU,hqo⟩
      · apply Fresh.Localisation.clear_of_window 1 <;> norm_num <;> linarith
      · apply Fresh.Localisation.clear_of_window 3 <;> norm_num <;> linarith
    · right
      right
      have hp3 : ¬ InWay p (3/8) := by
        apply not_inWay_iff.mpr
        apply Fresh.Localisation.clear_of_window 2 <;> norm_num <;> linarith
      rcases hqcases with ⟨hqL,hqU,hqo⟩ | ⟨hqL,hqU,hqo⟩
      · by_cases hq17 : (17/3:ℝ) ≤ q
        · refine Or.inl ⟨hp3,not_inWay_iff.mpr ?_⟩
          apply Fresh.Localisation.clear_of_window 2 <;> norm_num <;> linarith
        right
        refine ⟨Or.inr (lt_of_not_ge hq17),not_inWay_iff.mpr ?_,not_inWay_iff.mpr ?_⟩
        · apply Fresh.Localisation.clear_of_window 4 <;> norm_num <;> linarith
        · apply Fresh.Localisation.clear_of_window 3 <;> norm_num <;> linarith
      · refine Or.inl ⟨hp3,not_inWay_iff.mpr ?_⟩
        apply Fresh.Localisation.clear_of_window 4 <;> norm_num <;> linarith
  by_cases h : InWay x (1/8)
  · exact dispatch hx hy h
  by_cases h' : InWay y (1/8)
  · rcases dispatch hy hx h' with ⟨t,ht,hy',hx'⟩ | ⟨hy',hx'⟩ | ⟨hy',hx'⟩ | ⟨hl,hy',hx'⟩
    · exact Or.inl ⟨t,ht,hx',hy'⟩
    · exact Or.inr (Or.inl ⟨hx',hy'⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hx',hy'⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hl.symm,hx',hy'⟩))
  exact Or.inl ⟨1/8,⟨le_rfl,by norm_num⟩,h,h'⟩

/-- The result applies to any slow block retaining the three
specified clear cells, without a condition on its internal spacing. -/
theorem two_rates_of_retained_cells {S : Finset ℝ} {x y : ℝ}
    (hx : x ∈ Icc (1:ℝ) 15) (hy : y ∈ Icc (1:ℝ) 15)
    (hfirst : ∀ t ∈ Icc (1/8:ℝ) (7/40), LonelyAt S t)
    (hsecond : LonelyAt S (7/24)) (hthird : LonelyAt S (3/8))
    (hfourth : x < 17/3 ∨ y < 17/3 → LonelyAt S (5/8)) :
    ∃ t ∈ Icc (1/8:ℝ) (5/8), LonelyAt (S ∪ {x,y}) t := by
  have join {t : ℝ} (hs : LonelyAt S t) (hx' : ¬ InWay x t) (hy' : ¬ InWay y t) :
      LonelyAt (S ∪ {x,y}) t := by
    intro d hd
    rcases Finset.mem_union.mp hd with h | h
    · exact hs d h
    · simp only [Finset.mem_insert,Finset.mem_singleton] at h
      rcases h with rfl | rfl
      · exact not_inWay_iff.mp hx'
      · exact not_inWay_iff.mp hy'
  rcases two_rates_clear_cells hx hy with ⟨t,ht,hx',hy'⟩ | ⟨hx',hy'⟩ | ⟨hx',hy'⟩ | ⟨hl,hx',hy'⟩
  · exact ⟨t,⟨ht.1,ht.2.trans (by norm_num)⟩,join (hfirst t ht) hx' hy'⟩
  · exact ⟨7/24,by constructor <;> norm_num,join hsecond hx' hy'⟩
  · exact ⟨3/8,by constructor <;> norm_num,join hthird hx' hy'⟩
  · exact ⟨5/8,by constructor <;> norm_num,join (hfourth hl) hx' hy'⟩

/-- These three bands of slow rates retain all the clear cells used
by the two-reading argument. Rates within each band may vary independently. -/
theorem two_deviations_with_slow_bands {S : Finset ℝ} {x y : ℝ}
    (hx : x ∈ Icc (1:ℝ) 15) (hy : y ∈ Icc (1:ℝ) 15)
    (hS : ∀ d ∈ S, d ∈ Icc (1:ℝ) (7/3) ∨ d = 3 ∨ d ∈ Icc (27/7:ℝ) 5)
    (hfourth : x < 17/3 ∨ y < 17/3 → LonelyAt S (5/8)) :
    ∃ t ∈ Icc (1/8:ℝ) (5/8), LonelyAt (S ∪ {x,y}) t := by
  apply two_rates_of_retained_cells hx hy _ _ _ hfourth
  · intro t ht d hd
    have hd1 : 1 ≤ d := by
      rcases hS d hd with h | rfl | h
      · exact h.1
      · norm_num
      · linarith [h.1]
    have hd5 : d ≤ 5 := by
      rcases hS d hd with h | rfl | h
      · linarith [h.2]
      · norm_num
      · exact h.2
    apply Fresh.Localisation.clear_of_window 0
    · norm_num
      calc
        (1/8:ℝ) ≤ t := ht.1
        _ = 1*t := by ring
        _ ≤ d*t := mul_le_mul_of_nonneg_right hd1 (by linarith [ht.1])
    · norm_num
      calc
        d*t ≤ 5*t := mul_le_mul_of_nonneg_right hd5 (by linarith [ht.1])
        _ ≤ 7/8 := by linarith [ht.2]
  · intro d hd
    rcases hS d hd with h | rfl | h
    · apply Fresh.Localisation.clear_of_window 0 <;> norm_num <;> linarith [h.1,h.2]
    · exact Fresh.Localisation.clear_of_window 0 (by norm_num) (by norm_num)
    · apply Fresh.Localisation.clear_of_window 1 <;> norm_num <;> linarith [h.1,h.2]
  · intro d hd
    rcases hS d hd with h | rfl | h
    · apply Fresh.Localisation.clear_of_window 0 <;> norm_num <;> linarith [h.1,h.2]
    · exact Fresh.Localisation.clear_of_window 1 (by norm_num) (by norm_num)
    · apply Fresh.Localisation.clear_of_window 1 <;> norm_num <;> linarith [h.1,h.2]

/-- Two independent deviations of the AP, over the whole initial-lap
span permitted by radius one sixteenth. -/
theorem five_ap_two_deviations {x y : ℝ}
    (hx : x ∈ Icc (1:ℝ) 15) (hy : y ∈ Icc (1:ℝ) 15) :
    ∃ t ∈ Icc (1/8:ℝ) (5/8), LonelyAt (({1,2,3,4,5} : Finset ℝ) ∪ {x,y}) t := by
  apply two_deviations_with_slow_bands hx hy
  · intro d hd
    simp only [Finset.mem_insert,Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · intro _ d hd
    simp only [Finset.mem_insert,Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact Fresh.Localisation.clear_of_window 0 (by norm_num) (by norm_num)
    · exact Fresh.Localisation.clear_of_window 1 (by norm_num) (by norm_num)
    · exact Fresh.Localisation.clear_of_window 1 (by norm_num) (by norm_num)
    · exact Fresh.Localisation.clear_of_window 2 (by norm_num) (by norm_num)
    · exact Fresh.Localisation.clear_of_window 3 (by norm_num) (by norm_num)

#print axioms first_slow_cell_at_moving_close
#print axioms first_slow_cell_dispatch
#print axioms two_rates_clear_cells
#print axioms two_rates_of_retained_cells
#print axioms two_deviations_with_slow_bands
#print axioms five_ap_two_deviations

end Fresh.Cascade
