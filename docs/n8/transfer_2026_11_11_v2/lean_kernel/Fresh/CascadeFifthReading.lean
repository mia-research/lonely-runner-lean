import Fresh.CascadeTwoDeviations

namespace Fresh.Cascade

open Set

private theorem clear_in_box {d t lo hi a b : ℝ} {k : ℤ}
    (hd : d ∈ Icc lo hi) (ht : t ∈ Icc a b)
    (hlo : 0 ≤ lo) (ha : 0 ≤ a)
    (hL : (k:ℝ)+1/8 ≤ lo*a) (hU : hi*b ≤ (k:ℝ)+7/8) :
    ¬ InWay d t := by
  have hd0 := hlo.trans hd.1
  have hb0 := ha.trans (ht.1.trans ht.2)
  exact not_inWay_iff.mpr (Fresh.Localisation.clear_of_window k
    (hL.trans ((mul_le_mul_of_nonneg_left ht.1 hlo).trans
      (mul_le_mul_of_nonneg_right hd.1 (ha.trans ht.1))))
    ((mul_le_mul_of_nonneg_left ht.2 hd0).trans
      ((mul_le_mul_of_nonneg_right hd.2 hb0).trans hU)))

set_option maxHeartbeats 600000 in
/-- The first closing and a later opening both move with the fifth reading.
The later opening fits before the third reading closes when (5s \le 3w). -/
theorem fifth_reading_moving_close {s v w x y : ℝ}
    (hs : s ∈ Icc (17/7:ℝ) (23/7)) (hv : v ∈ Icc (27/7:ℝ) (31/7))
    (hw : w ∈ Icc (49/10:ℝ) (46/9))
    (hx : x ∈ Icc (1:ℝ) 15) (hy : y ∈ Icc (1:ℝ) 15) :
    ∃ t ∈ Icc (1/8:ℝ) (7/8), LonelyAt (({1,2,s,v,w} : Finset ℝ) ∪ {x,y}) t := by
  let S : Finset ℝ := {1,2,s,v,w}
  let T : ℝ := 25/(8*w)
  have hw0 : w ≠ 0 := by linarith [hw.1]
  have hden : 0 < 8*w := by linarith [hw.1]
  have hT : T ∈ Icc (225/368:ℝ) (125/196) := by
    constructor
    · dsimp [T]
      rw [le_div_iff₀ hden]
      linarith [hw.2]
    · dsimp [T]
      rw [div_le_iff₀ hden]
      linarith [hw.1]
  have hb : 7/(8*w) ∈ Icc (1/8:ℝ) (7/8) := by
    constructor
    · rw [le_div_iff₀ hden]
      linarith [hw.2]
    · rw [div_le_iff₀ hden]
      linarith [hw.1]
  have first {t : ℝ} (ht : t ∈ Icc (1/8:ℝ) (7/(8*w))) : LonelyAt S t := by
    intro d hd
    have hd' : d ∈ Icc (1:ℝ) w := by
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl <;> constructor <;>
        linarith [hs.1,hs.2,hv.1,hv.2,hw.1]
    have ht0 : 0 ≤ t := by linarith [ht.1]
    apply Fresh.Localisation.clear_of_window 0 <;> norm_num
    · have hdlo := mul_le_mul_of_nonneg_right hd'.1 ht0
      linarith [ht.1]
    · have h := (le_div_iff₀ hden).mp ht.2
      have hmul := mul_le_mul_of_nonneg_right hd'.2 ht0
      linarith
  have middle (hpair : 5*s ≤ 3*w) : LonelyAt S T := by
    intro d hd
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact not_inWay_iff.mp (clear_in_box (lo := 1) (hi := 1) (k := 0)
        ⟨le_rfl,le_rfl⟩ hT (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    · exact not_inWay_iff.mp (clear_in_box (lo := 2) (hi := 2) (k := 1)
        ⟨le_rfl,le_rfl⟩ hT (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    · apply Fresh.Localisation.clear_of_window 1 <;> norm_num
      · have h := (mul_le_mul_of_nonneg_left hT.1 (by norm_num : (0:ℝ) ≤ 17/7)).trans
          (mul_le_mul_of_nonneg_right hs.1 (by linarith [hT.1] : 0 ≤ T))
        linarith
      · dsimp [T]
        rw [← mul_div_assoc,div_le_iff₀ hden]
        linarith
    · exact not_inWay_iff.mp (clear_in_box (k := 2) hv hT
        (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    · have he : d*T = 25/8 := by
        have hw0 : d ≠ 0 := by linarith [hw.1]
        dsimp [T]
        field_simp
      rw [he]
      exact Fresh.Localisation.clear_of_window 3 (by norm_num) (by norm_num)
  have fixed : LonelyAt S (9/16) := by
    intro d hd
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact Fresh.Localisation.clear_of_window 0 (by norm_num) (by norm_num)
    · exact Fresh.Localisation.clear_of_window 1 (by norm_num) (by norm_num)
    · apply Fresh.Localisation.clear_of_window 1 <;> norm_num <;> linarith [hs.1,hs.2]
    · apply Fresh.Localisation.clear_of_window 2 <;> norm_num <;> linarith [hv.1,hv.2]
    · apply Fresh.Localisation.clear_of_window 2 <;> norm_num <;> linarith [hw.1,hw.2]
  have last : LonelyAt S (7/8) := by
    intro d hd
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact Fresh.Localisation.clear_of_window 0 (by norm_num) (by norm_num)
    · exact Fresh.Localisation.clear_of_window 1 (by norm_num) (by norm_num)
    · apply Fresh.Localisation.clear_of_window 2 <;> norm_num <;> linarith [hs.1,hs.2]
    · apply Fresh.Localisation.clear_of_window 3 <;> norm_num <;> linarith [hv.1,hv.2]
    · apply Fresh.Localisation.clear_of_window 4 <;> norm_num <;> linarith [hw.1,hw.2]
  have recover {p q : ℝ} (hp7 : 7 < p) (hpSmall : p < 22/3)
      (hq49 : 49/9 < q) (hq31 : q ≤ 32/5) (hsw : 3*w < 5*s) :
      ∃ t ∈ Icc (1/8:ℝ) (7/8), LonelyAt S t ∧ ¬ InWay p t ∧ ¬ InWay q t := by
    have hsLow : 147/50 ≤ s := by linarith [hw.1]
    have hs' : s ∈ Icc (147/50:ℝ) (23/7) := ⟨hsLow,hs.2⟩
    have hp' : p ∈ Icc (7:ℝ) (22/3) := ⟨hp7.le,hpSmall.le⟩
    have hq' : q ∈ Icc (49/9:ℝ) (32/5) := ⟨hq49.le,hq31⟩
    by_cases hq17 : 17*w ≤ 15*q
    · let t := 15/(8*w)
      have ht : t ∈ Icc (135/368:ℝ) (75/196) := by
        constructor
        · dsimp [t]; rw [le_div_iff₀ hden]; linarith [hw.2]
        · dsimp [t]; rw [div_le_iff₀ hden]; linarith [hw.1]
      refine ⟨t,⟨by linarith [ht.1],by linarith [ht.2]⟩,?_,?_,?_⟩
      · intro d hd
        simp only [S,Finset.mem_insert,Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | he | he | he
        · exact not_inWay_iff.mp (clear_in_box (lo := 1) (hi := 1) (k := 0)
            ⟨le_rfl,le_rfl⟩ ht (by norm_num) (by norm_num) (by norm_num) (by norm_num))
        · exact not_inWay_iff.mp (clear_in_box (lo := 2) (hi := 2) (k := 0)
            ⟨le_rfl,le_rfl⟩ ht (by norm_num) (by norm_num) (by norm_num) (by norm_num))
        · subst d
          apply Fresh.Localisation.clear_of_window 1 <;>
            dsimp [t] <;> rw [← mul_div_assoc] <;> norm_num
          · rw [le_div_iff₀ hden]; linarith
          · rw [div_le_iff₀ hden]; linarith [hw.1,hs.2]
        · subst d
          exact not_inWay_iff.mp (clear_in_box (k := 1) hv ht
            (by norm_num) (by norm_num) (by norm_num) (by norm_num))
        · subst d
          have he : w*t = 15/8 := by dsimp [t]; field_simp
          rw [he]
          exact Fresh.Localisation.clear_of_window 1 (by norm_num) (by norm_num)
      · exact clear_in_box (k := 2) hp' ht
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · apply not_inWay_iff.mpr
        apply Fresh.Localisation.clear_of_window 2 <;>
          dsimp [t] <;> rw [← mul_div_assoc] <;> norm_num
        · rw [le_div_iff₀ hden]; linarith
        · rw [div_le_iff₀ hden]; linarith [hq31,hw.1]
    by_cases hv7 : 9*v ≤ 7*w
    · let t := 9/(8*w)
      have ht : t ∈ Icc (81/368:ℝ) (45/196) := by
        constructor
        · dsimp [t]; rw [le_div_iff₀ hden]; linarith [hw.2]
        · dsimp [t]; rw [div_le_iff₀ hden]; linarith [hw.1]
      refine ⟨t,⟨by linarith [ht.1],by linarith [ht.2]⟩,?_,?_,?_⟩
      · intro d hd
        simp only [S,Finset.mem_insert,Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | he | he | he
        · exact not_inWay_iff.mp (clear_in_box (lo := 1) (hi := 1) (k := 0)
            ⟨le_rfl,le_rfl⟩ ht (by norm_num) (by norm_num) (by norm_num) (by norm_num))
        · exact not_inWay_iff.mp (clear_in_box (lo := 2) (hi := 2) (k := 0)
            ⟨le_rfl,le_rfl⟩ ht (by norm_num) (by norm_num) (by norm_num) (by norm_num))
        · subst d
          exact not_inWay_iff.mp (clear_in_box (k := 0) hs' ht
            (by norm_num) (by norm_num) (by norm_num) (by norm_num))
        · subst d
          apply Fresh.Localisation.clear_of_window 0 <;>
            dsimp [t] <;> rw [← mul_div_assoc] <;> norm_num
          · rw [le_div_iff₀ hden]; linarith [hv.1,hw.2]
          · rw [div_le_iff₀ hden]; linarith
        · subst d
          have he : w*t = 9/8 := by dsimp [t]; field_simp
          rw [he]
          exact Fresh.Localisation.clear_of_window 1 (by norm_num) (by norm_num)
      · exact clear_in_box (k := 1) hp' ht
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact clear_in_box (k := 1) hq' ht
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    let L := 33/(8*w)
    have hL : L ∈ Icc (297/368:ℝ) (7/8) := by
      constructor
      · dsimp [L]; rw [le_div_iff₀ hden]; linarith [hw.2]
      · dsimp [L]; rw [div_le_iff₀ hden]; linarith [hw.1]
    have late {t : ℝ} (ht : t ∈ Icc L (7/8)) : LonelyAt S t := by
      have ht' : t ∈ Icc (297/368:ℝ) (7/8) := ⟨hL.1.trans ht.1,ht.2⟩
      intro d hd
      simp only [S,Finset.mem_insert,Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | he | he | he
      · exact not_inWay_iff.mp (clear_in_box (lo := 1) (hi := 1) (k := 0)
          ⟨le_rfl,le_rfl⟩ ht' (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      · exact not_inWay_iff.mp (clear_in_box (lo := 2) (hi := 2) (k := 1)
          ⟨le_rfl,le_rfl⟩ ht' (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      · subst d
        exact not_inWay_iff.mp (clear_in_box (k := 2) hs' ht'
          (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      · subst d
        apply Fresh.Localisation.clear_of_window 3 <;> norm_num
        · have hvt : v*L ≤ v*t :=
            mul_le_mul_of_nonneg_left ht.1 (by linarith [hv.1])
          suffices (25/8:ℝ) ≤ v*L from this.trans hvt
          dsimp [L]; rw [← mul_div_assoc,le_div_iff₀ hden]
          linarith
        · have hvt := mul_le_mul_of_nonneg_left ht.2 (by linarith [hv.1] : 0 ≤ v)
          linarith [hv.2]
      · subst d
        apply Fresh.Localisation.clear_of_window 4 <;> norm_num
        · have h := (div_le_iff₀ hden).mp ht.1
          linarith
        · have h := mul_le_mul_of_nonneg_left ht.2 (by linarith [hw.1] : 0 ≤ w)
          linarith [hw.2]
    have qL : q*L ≤ 39/8 := by
      dsimp [L]; rw [← mul_div_assoc,div_le_iff₀ hden]
      linarith [hw.1]
    have qLower {t : ℝ} (ht : L ≤ t) : (33/8:ℝ) ≤ q*t := by
      have h := (mul_le_mul_of_nonneg_left (hL.1.trans ht)
        (by norm_num : (0:ℝ) ≤ 49/9)).trans
        (mul_le_mul_of_nonneg_right hq49.le (by linarith [hL.1.trans ht] : 0 ≤ t))
      linarith
    by_cases hp47 : 33*p ≤ 47*w
    · refine ⟨L,⟨by linarith [hL.1],hL.2⟩,late ⟨le_rfl,hL.2⟩,
        not_inWay_iff.mpr ?_,not_inWay_iff.mpr ?_⟩
      · apply Fresh.Localisation.clear_of_window 5 <;>
          dsimp [L] <;> rw [← mul_div_assoc] <;> norm_num
        · rw [le_div_iff₀ hden]; linarith [hw.2]
        · rw [div_le_iff₀ hden]; linarith
      · exact Fresh.Localisation.clear_of_window 4 (by norm_num; linarith [qLower (le_refl L)])
          (by norm_num; linarith)
    let u := 49/(8*p)
    let t := max L u
    have hpden : 0 < 8*p := by linarith
    have hu : u ≤ 7/8 := by
      dsimp [u]; rw [div_le_iff₀ hpden]; linarith
    have ht : t ∈ Icc L (7/8) := ⟨le_max_left _ _,max_le hL.2 hu⟩
    refine ⟨t,⟨by linarith [hL.1.trans ht.1],ht.2⟩,late ht,
      not_inWay_iff.mpr ?_,not_inWay_iff.mpr ?_⟩
    · apply Fresh.Localisation.clear_of_window 6 <;> norm_num
      · have h := (div_le_iff₀ hpden).mp (le_max_right L u)
        linarith
      · have h := mul_le_mul_of_nonneg_left ht.2 (by linarith : 0 ≤ p)
        linarith
    · apply Fresh.Localisation.clear_of_window 4 <;> norm_num
      · exact qLower ht.1
      · have qu : q*u ≤ 39/8 := by
          dsimp [u]; rw [← mul_div_assoc,div_le_iff₀ hpden]
          linarith
        dsimp [t]
        rcases le_total L u with h | h
        · simpa only [max_eq_right h] using qu
        · simpa only [max_eq_left h] using qL
  have dispatch {p q : ℝ} (hp : p ∈ Icc (1:ℝ) 15) (hq : q ∈ Icc (1:ℝ) 15)
      (h : InWay p (1/8)) :
      ∃ t ∈ Icc (1/8:ℝ) (7/8), LonelyAt S t ∧ ¬ InWay p t ∧ ¬ InWay q t := by
    rcases first_slow_cell_at_moving_close hw hp hq h with ⟨t,ht,hp',hq'⟩ | ⟨h7,h9,hq'⟩
    · exact ⟨t,⟨ht.1,ht.2.trans hb.2⟩,first ht,hp',hq'⟩
    rcases hq' with ⟨hL,hU,hO⟩ | ⟨hL,hU,hO⟩
    · by_cases hpLarge : (22/3:ℝ) ≤ p
      · refine ⟨9/16,by constructor <;> norm_num,fixed,not_inWay_iff.mpr ?_,not_inWay_iff.mpr ?_⟩
        · apply Fresh.Localisation.clear_of_window 4 <;> norm_num <;> linarith [hw.2]
        · apply Fresh.Localisation.clear_of_window 3 <;> norm_num <;> linarith [hw.2]
      by_cases hqLarge : 31*w < 25*q
      · refine ⟨7/8,by constructor <;> norm_num,last,not_inWay_iff.mpr ?_,not_inWay_iff.mpr ?_⟩
        · apply Fresh.Localisation.clear_of_window 6 <;> norm_num <;> linarith
        · apply Fresh.Localisation.clear_of_window 5 <;> norm_num <;> linarith [hw.1,hw.2]
      by_cases hpair : 5*s ≤ 3*w
      swap
      · exact recover h7 (lt_of_not_ge hpLarge) (by linarith)
          (by linarith [hw.2]) (lt_of_not_ge hpair)
      refine ⟨T,⟨by linarith [hT.1],by linarith [hT.2]⟩,middle hpair,?_,?_⟩
      · exact clear_in_box (lo := 7) (hi := 22/3) (k := 4)
          ⟨h7.le,le_of_not_ge hpLarge⟩ hT (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · apply not_inWay_iff.mpr
        apply Fresh.Localisation.clear_of_window 3 <;>
          dsimp [T] <;> rw [← mul_div_assoc] <;> norm_num
        · rw [le_div_iff₀ hden]; linarith [hw.2]
        · rw [div_le_iff₀ hden]; linarith
    · refine ⟨7/8,by constructor <;> norm_num,last,not_inWay_iff.mpr ?_,not_inWay_iff.mpr ?_⟩
      · apply Fresh.Localisation.clear_of_window 6 <;> norm_num <;> linarith [hw.2]
      · apply Fresh.Localisation.clear_of_window 10 <;> norm_num <;> linarith [hw.2]
  have join {t : ℝ} (ht : LonelyAt S t) (hx' : ¬ InWay x t) (hy' : ¬ InWay y t) :
      LonelyAt (S ∪ {x,y}) t := by
    intro d hd
    rcases Finset.mem_union.mp hd with h | h
    · exact ht d h
    · simp only [Finset.mem_insert,Finset.mem_singleton] at h
      rcases h with rfl | rfl
      · exact not_inWay_iff.mp hx'
      · exact not_inWay_iff.mp hy'
  by_cases h : InWay x (1/8)
  · obtain ⟨t,ht,hS,hx',hy'⟩ := dispatch hx hy h
    exact ⟨t,ht,join hS hx' hy'⟩
  by_cases h' : InWay y (1/8)
  · obtain ⟨t,ht,hS,hy',hx'⟩ := dispatch hy hx h'
    exact ⟨t,ht,join hS hx' hy'⟩
  exact ⟨1/8,⟨le_rfl,by norm_num⟩,join (first ⟨le_rfl,hb.1⟩) h h'⟩

end Fresh.Cascade

#print axioms Fresh.Cascade.fifth_reading_moving_close
