import Fresh.CascadeTwoDeviations

namespace Fresh.Cascade

open Set

/-- Cells of the retained slow block used by the replacement rule. -/
def ReplacementCoreTime (t : ℝ) : Prop :=
  t ∈ Icc (1/8:ℝ) (7/40) ∨ t ∈ Icc (9/32:ℝ) (17/56) ∨
    t = 3/8 ∨ t ∈ Icc (5/8:ℝ) (23/32) ∨ t ∈ Icc (33/40:ℝ) (7/8)

theorem retained_four {t : ℝ} (h : ReplacementCoreTime t) :
    LonelyAt ({1,2,4,5} : Finset ℝ) t := by
  unfold ReplacementCoreTime at h
  intro d hd
  simp only [Finset.mem_insert,Finset.mem_singleton] at hd
  rcases h with ht | ht | rfl | ht | ht
  · rcases hd with rfl | rfl | rfl | rfl <;>
      apply Fresh.Localisation.clear_of_window 0 <;> norm_num <;> linarith [ht.1,ht.2]
  · rcases hd with rfl | rfl | rfl | rfl
    all_goals first
      | apply Fresh.Localisation.clear_of_window 0 <;> norm_num <;> linarith [ht.1,ht.2]
      | apply Fresh.Localisation.clear_of_window 1 <;> norm_num <;> linarith [ht.1,ht.2]
  · rcases hd with rfl | rfl | rfl | rfl
    · exact Fresh.Localisation.clear_of_window 0 (by norm_num) (by norm_num)
    · exact Fresh.Localisation.clear_of_window 0 (by norm_num) (by norm_num)
    · exact Fresh.Localisation.clear_of_window 1 (by norm_num) (by norm_num)
    · exact Fresh.Localisation.clear_of_window 1 (by norm_num) (by norm_num)
  · rcases hd with rfl | rfl | rfl | rfl
    · apply Fresh.Localisation.clear_of_window 0 <;> norm_num <;> linarith [ht.1,ht.2]
    · apply Fresh.Localisation.clear_of_window 1 <;> norm_num <;> linarith [ht.1,ht.2]
    · apply Fresh.Localisation.clear_of_window 2 <;> norm_num <;> linarith [ht.1,ht.2]
    · apply Fresh.Localisation.clear_of_window 3 <;> norm_num <;> linarith [ht.1,ht.2]
  · rcases hd with rfl | rfl | rfl | rfl
    · apply Fresh.Localisation.clear_of_window 0 <;> norm_num <;> linarith [ht.1,ht.2]
    · apply Fresh.Localisation.clear_of_window 1 <;> norm_num <;> linarith [ht.1,ht.2]
    · apply Fresh.Localisation.clear_of_window 3 <;> norm_num <;> linarith [ht.1,ht.2]
    · apply Fresh.Localisation.clear_of_window 4 <;> norm_num <;> linarith [ht.1,ht.2]

/-- In the low right-blocker branch, the late slow cell accepts either
at its start or at the first reading's opening. -/
theorem low_blockers_recover_late {p q : ℝ}
    (hp : p ∈ Ioo (7:ℝ) (51/7)) (hq : q ∈ Ioo (5:ℝ) (17/3)) :
    ∃ t ∈ Icc (33/40:ℝ) (7/8), ¬ InWay p t ∧ ¬ InWay q t := by
  by_cases h : p ≤ 235/33
  · refine ⟨33/40,⟨le_rfl,by norm_num⟩,not_inWay_iff.mpr ?_,not_inWay_iff.mpr ?_⟩
    · apply Fresh.Localisation.clear_of_window 5 <;> norm_num <;> linarith [hp.1]
    · apply Fresh.Localisation.clear_of_window 4 <;> norm_num <;> linarith [hq.1,hq.2]
  have hp0 : 0 < p := (by norm_num : (0:ℝ) < 7).trans hp.1
  let t := 49/(8*p)
  have ht : t ∈ Icc (33/40:ℝ) (7/8) := by
    constructor
    · dsimp [t]
      rw [le_div_iff₀ (by positivity)]
      linarith [hp.2]
    · dsimp [t]
      rw [div_le_iff₀ (by positivity)]
      linarith [hp.1]
  refine ⟨t,ht,not_inWay_iff.mpr ?_,not_inWay_iff.mpr ?_⟩
  · have he : p*t = 49/8 := by dsimp [t]; field_simp
    rw [he]
    exact Fresh.Localisation.clear_of_window 6 (by norm_num) (by norm_num)
  · apply Fresh.Localisation.clear_of_window 4 <;> norm_num
    · have hl := mul_le_mul_of_nonneg_left ht.1 (by linarith [hq.1] : 0 ≤ q)
      linarith [hq.1]
    · dsimp [t]
      rw [← mul_div_assoc,div_le_iff₀ (by positivity)]
      linarith [hq.2,lt_of_not_ge h]

/-- The moving reading can reopen before the late cell. These are
the tests at its opening, expressed directly in the three rates. -/
theorem low_blockers_moving_opening {s p q : ℝ}
    (hs : s ∈ Icc (3:ℝ) (23/7)) (hp : p ∈ Ioo (7:ℝ) (51/7))
    (hq : q ∈ Ioo (5:ℝ) (17/3)) (hq' : 17*q ≤ 31*s)
    (hp' : 17*p ≤ 39*s ∨ 41*s ≤ 17*p) :
    let t : ℝ := 17/(8*s)
    t ∈ Icc (5/8:ℝ) (23/32) ∧ ¬ InWay s t ∧ ¬ InWay p t ∧ ¬ InWay q t := by
  dsimp only
  have hs0 : 0 < s := by linarith [hs.1]
  have hden : 0 < 8*s := by positivity
  have hphase (d : ℝ) : d*(17/(8*s)) = (17*d)/(8*s) := by ring
  refine ⟨⟨?_,?_⟩,not_inWay_iff.mpr ?_,not_inWay_iff.mpr ?_,not_inWay_iff.mpr ?_⟩
  · rw [le_div_iff₀ hden]
    linarith [hs.2]
  · rw [div_le_iff₀ hden]
    linarith [hs.1]
  · have he : s*(17/(8*s)) = 17/8 := by field_simp
    rw [he]
    exact Fresh.Localisation.clear_of_window 2 (by norm_num) (by norm_num)
  · rcases hp' with h | h
    · apply Fresh.Localisation.clear_of_window 4 <;> rw [hphase] <;> norm_num
      · rw [le_div_iff₀ hden]
        linarith [hp.1,hs.2]
      · rw [div_le_iff₀ hden]
        linarith
    · apply Fresh.Localisation.clear_of_window 5 <;> rw [hphase] <;> norm_num
      · rw [le_div_iff₀ hden]
        linarith
      · rw [div_le_iff₀ hden]
        linarith [hp.2,hs.1]
  · apply Fresh.Localisation.clear_of_window 3 <;> rw [hphase] <;> norm_num
    · rw [le_div_iff₀ hden]
      linarith [hq.1,hs.2]
    · rw [div_le_iff₀ hden]
      linarith

/-- Lowering the third reading extends the second slow cell to the
fast opening as soon as the moving closing edge reaches it. -/
theorem lowered_reading_second_opening {s p : ℝ}
    (hs : s ∈ Icc (17/7:ℝ) 3) (hp : p ∈ Ioo (7:ℝ) (51/7))
    (h : 17*s ≤ 7*p) :
    let t : ℝ := 17/(8*p)
    t ∈ Icc (9/32:ℝ) (17/56) ∧ ¬ InWay s t ∧ ¬ InWay p t := by
  dsimp only
  have hp0 : 0 < p := by linarith [hp.1]
  have hden : 0 < 8*p := by positivity
  refine ⟨⟨?_,?_⟩,not_inWay_iff.mpr ?_,not_inWay_iff.mpr ?_⟩
  · rw [le_div_iff₀ hden]
    linarith [hp.2]
  · rw [div_le_iff₀ hden]
    linarith [hp.1]
  · apply Fresh.Localisation.clear_of_window 0 <;>
      rw [← mul_div_assoc] <;> norm_num
    · rw [le_div_iff₀ hden]
      linarith [hs.1,hp.2]
    · rw [div_le_iff₀ hden]
      linarith
  · have he : p*(17/(8*p)) = 17/8 := by field_simp
    rw [he]
    exact Fresh.Localisation.clear_of_window 2 (by norm_num) (by norm_num)

/-- The cells used after allowing the second opening to move.
The moving candidate in the middle of the window is tested separately. -/
def AdjustedCoreTime (a t : ℝ) : Prop :=
  t ∈ Icc (1/8:ℝ) (7/40) ∨ t ∈ Icc a (17/56) ∨
    t = 3/8 ∨ t = 5/8 ∨ t ∈ Icc (33/40:ℝ) (7/8)

/-- The old singleton can disappear on either side of the deformation.
The same left/right blocker comparison supplies replacement witnesses
throughout the stated interval of slow readings. -/
theorem replacement_of_adjusted_core {S : Finset ℝ} {a s x y : ℝ}
    (ha : a ∈ Icc (9/32:ℝ) (7/24))
    (hbackup : 7/8 < s*a → LonelyAt S (17/40) ∨ LonelyAt S (9/16))
    (hcore : ∀ t, AdjustedCoreTime a t → LonelyAt S t)
    (hs : s ∈ Icc (17/7:ℝ) (23/7))
    (hx : x ∈ Icc (1:ℝ) 15) (hy : y ∈ Icc (1:ℝ) 15) :
    ∃ t ∈ Icc (1/8:ℝ) (7/8),
      LonelyAt (S ∪ {s,x,y}) t := by
  classical
  let good (t : ℝ) : Prop :=
    t ∈ Icc (1/8:ℝ) (7/8) ∧ LonelyAt S t ∧ ¬ InWay s t
  have first {t : ℝ} (ht : t ∈ Icc (1/8:ℝ) (7/40)) : good t := by
    refine ⟨⟨ht.1,ht.2.trans (by norm_num)⟩,hcore _ (Or.inl ht),not_inWay_iff.mpr ?_⟩
    apply Fresh.Localisation.clear_of_window 0 <;> norm_num
    · have h := mul_le_mul_of_nonneg_right hs.1 (by linarith [ht.1] : 0 ≤ t)
      have h' := mul_le_mul_of_nonneg_left ht.1 (by norm_num : (0:ℝ) ≤ 17/7)
      linarith
    · have h := mul_le_mul_of_nonneg_right hs.2 (by linarith [ht.1] : 0 ≤ t)
      have h' := mul_le_mul_of_nonneg_left ht.2 (by norm_num : (0:ℝ) ≤ 28/9)
      linarith
  have late {t : ℝ} (ht : t ∈ Icc (33/40:ℝ) (7/8)) (hs3 : 3 ≤ s) : good t := by
    refine ⟨⟨(by norm_num : (1/8:ℝ) ≤ 33/40).trans ht.1,ht.2⟩,
      hcore _ (Or.inr (Or.inr (Or.inr (Or.inr ht)))),not_inWay_iff.mpr ?_⟩
    apply Fresh.Localisation.clear_of_window 2 <;> norm_num
    · have h := mul_le_mul_of_nonneg_right hs3 (by linarith [ht.1] : 0 ≤ t)
      have h' := mul_le_mul_of_nonneg_left ht.1 (by norm_num : (0:ℝ) ≤ 3)
      linarith
    · have h := mul_le_mul_of_nonneg_right hs.2 (by linarith [ht.1] : 0 ≤ t)
      have h' := mul_le_mul_of_nonneg_left ht.2 (by norm_num : (0:ℝ) ≤ 28/9)
      linarith
  have upper : (3:ℝ) ≤ s → good (3/8) := by
    intro h
    refine ⟨by constructor <;> norm_num,hcore _ (Or.inr (Or.inr (Or.inl rfl))),
      not_inWay_iff.mpr ?_⟩
    apply Fresh.Localisation.clear_of_window 1 <;> norm_num <;> linarith [hs.2]
  have down_end : s ≤ 3 → good (7/8) := by
    intro h
    refine ⟨by constructor <;> norm_num,hcore _ (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨by norm_num,le_rfl⟩)))),not_inWay_iff.mpr ?_⟩
    apply Fresh.Localisation.clear_of_window 2 <;> norm_num <;> linarith [hs.1]
  have dispatch {p q : ℝ} (hp : p ∈ Icc (1:ℝ) 15) (hq : q ∈ Icc (1:ℝ) 15)
      (hw : InWay p (1/8)) : ∃ t, good t ∧ ¬ InWay p t ∧ ¬ InWay q t := by
    rcases first_slow_cell_dispatch hp hq hw with ⟨t,ht,hp',hq'⟩ | ⟨hp7,hp9,hr⟩
    · exact ⟨t,first ht,hp',hq'⟩
    by_cases hdown : s ≤ 3
    · by_cases hp51 : (51/7:ℝ) ≤ p
      · refine ⟨7/24,⟨by constructor <;> norm_num,
          hcore _ (Or.inr (Or.inl ⟨ha.2,by norm_num⟩)),not_inWay_iff.mpr ?_⟩,
          not_inWay_iff.mpr ?_,not_inWay_iff.mpr ?_⟩
        · apply Fresh.Localisation.clear_of_window 0 <;> norm_num <;> linarith [hs.1]
        · apply Fresh.Localisation.clear_of_window 2 <;> norm_num <;> linarith
        · rcases hr with ⟨hl,hu,ho⟩ | ⟨hl,hu,ho⟩
          · apply Fresh.Localisation.clear_of_window 1 <;> norm_num <;> linarith
          · apply Fresh.Localisation.clear_of_window 3 <;> norm_num <;> linarith
      have hp51' : p < 51/7 := lt_of_not_ge hp51
      by_cases hstretch : 17*s ≤ 7*p ∧ (17*q ≤ 15*p ∨ 75/7 < q)
      · obtain ⟨ht,hs',hp'⟩ := lowered_reading_second_opening ⟨hs.1,hdown⟩
          ⟨hp7,hp51'⟩ hstretch.1
        have h7 : (7/24:ℝ) ≤ 17/(8*p) := by
          rw [le_div_iff₀ (by positivity)]
          linarith
        refine ⟨_,⟨⟨(by norm_num : (1/8:ℝ) ≤ 9/32).trans ht.1,
          ht.2.trans (by norm_num)⟩,hcore _ (Or.inr (Or.inl ⟨ha.2.trans h7,ht.2⟩)),hs'⟩,
          hp',not_inWay_iff.mpr ?_⟩
        have hden : 0 < 8*p := by linarith
        rcases hr with ⟨hl,hu,ho⟩ | ⟨hl,hu,ho⟩
        · have hq15 : 17*q ≤ 15*p := hstretch.2.resolve_right (by linarith)
          apply Fresh.Localisation.clear_of_window 1 <;>
            rw [← mul_div_assoc] <;> norm_num
          · rw [le_div_iff₀ hden]
            linarith
          · rw [div_le_iff₀ hden]
            linarith
        · apply Fresh.Localisation.clear_of_window 3 <;>
            rw [← mul_div_assoc] <;> norm_num
          · rw [le_div_iff₀ hden]
            linarith
          · rw [div_le_iff₀ hden]
            linarith
      have hpLate : ¬ InWay p (7/8) := by
        apply not_inWay_iff.mpr
        apply Fresh.Localisation.clear_of_window 6 <;> norm_num <;> linarith
      rcases hr with ⟨hl,hu,ho⟩ | ⟨hl,hu,ho⟩
      · by_cases hq31 : q ≤ 31/5
        · refine ⟨5/8,⟨by constructor <;> norm_num,
            hcore _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),not_inWay_iff.mpr ?_⟩,
            not_inWay_iff.mpr ?_,not_inWay_iff.mpr ?_⟩
          · apply Fresh.Localisation.clear_of_window 1 <;> norm_num <;> linarith [hs.1]
          · apply Fresh.Localisation.clear_of_window 4 <;> norm_num <;> linarith
          · apply Fresh.Localisation.clear_of_window 3 <;> norm_num <;> linarith
        · refine ⟨7/8,down_end hdown,hpLate,not_inWay_iff.mpr ?_⟩
          apply Fresh.Localisation.clear_of_window 5 <;> norm_num <;> linarith
      · refine ⟨7/8,down_end hdown,hpLate,not_inWay_iff.mpr ?_⟩
        apply Fresh.Localisation.clear_of_window 10 <;> norm_num <;> linarith
    · have hs3 : 3 ≤ s := (lt_of_not_ge hdown).le
      rcases hr with ⟨hl,hu,ho⟩ | ⟨hl,hu,ho⟩
      · by_cases hp68 : (68/9:ℝ) ≤ p
        · by_cases hsa : s*a ≤ 7/8
          · refine ⟨a,⟨⟨(by norm_num : (1/8:ℝ) ≤ 9/32).trans ha.1,
              ha.2.trans (by norm_num)⟩,
              hcore _ (Or.inr (Or.inl ⟨le_rfl,ha.2.trans (by norm_num)⟩)),
              not_inWay_iff.mpr ?_⟩,not_inWay_iff.mpr ?_,not_inWay_iff.mpr ?_⟩
            · apply Fresh.Localisation.clear_of_window 0
              · have h := mul_le_mul_of_nonneg_right hs.1
                  (by linarith [ha.1] : 0 ≤ a)
                have h' := mul_le_mul_of_nonneg_left ha.1 (by norm_num : (0:ℝ) ≤ 17/7)
                norm_num
                linarith
              · simpa using hsa
            · apply Fresh.Localisation.clear_of_window 2 <;> norm_num
              · have h := mul_le_mul_of_nonneg_right hp68 (by linarith [ha.1] : 0 ≤ a)
                have h' := mul_le_mul_of_nonneg_left ha.1 (by norm_num : (0:ℝ) ≤ 68/9)
                linarith
              · have h := mul_le_mul_of_nonneg_right hp9.le (by linarith [ha.1] : 0 ≤ a)
                have h' := mul_le_mul_of_nonneg_left ha.2 (by norm_num : (0:ℝ) ≤ 9)
                linarith
            · apply Fresh.Localisation.clear_of_window 1 <;> norm_num
              · have h := mul_le_mul_of_nonneg_right hl.le (by linarith [ha.1] : 0 ≤ a)
                have h' := mul_le_mul_of_nonneg_left ha.1 (by norm_num : (0:ℝ) ≤ 5)
                linarith
              · have h := mul_le_mul_of_nonneg_right hu.le (by linarith [ha.1] : 0 ≤ a)
                have h' := mul_le_mul_of_nonneg_left ha.2 (by norm_num : (0:ℝ) ≤ 45/7)
                linarith
          · rcases hbackup (lt_of_not_ge hsa) with h17 | h9
            · refine ⟨17/40,⟨by constructor <;> norm_num,h17,not_inWay_iff.mpr ?_⟩,
                not_inWay_iff.mpr ?_,not_inWay_iff.mpr ?_⟩
              · apply Fresh.Localisation.clear_of_window 1 <;> norm_num <;> linarith [hs.2]
              · apply Fresh.Localisation.clear_of_window 3 <;> norm_num <;> linarith
              · apply Fresh.Localisation.clear_of_window 2 <;> norm_num <;> linarith
            · refine ⟨9/16,⟨by constructor <;> norm_num,h9,not_inWay_iff.mpr ?_⟩,
                not_inWay_iff.mpr ?_,not_inWay_iff.mpr ?_⟩
              · apply Fresh.Localisation.clear_of_window 1 <;> norm_num <;> linarith [hs.2]
              · apply Fresh.Localisation.clear_of_window 4 <;> norm_num <;> linarith
              · apply Fresh.Localisation.clear_of_window 3 <;> norm_num <;> linarith
        by_cases hq17 : (17/3:ℝ) ≤ q
        · refine ⟨3/8,upper hs3,not_inWay_iff.mpr ?_,not_inWay_iff.mpr ?_⟩
          · apply Fresh.Localisation.clear_of_window 2 <;> norm_num <;> linarith
          · apply Fresh.Localisation.clear_of_window 2 <;> norm_num <;> linarith
        have hp51 : p < 51/7 := by linarith
        by_cases he : (17*q ≤ 31*s ∧ (17*p ≤ 39*s ∨ 41*s ≤ 17*p)) ∧
            LonelyAt S (17/(8*s))
        · obtain ⟨ht,hs',hp',hq'⟩ := low_blockers_moving_opening ⟨hs3,hs.2⟩
            ⟨hp7,hp51⟩ ⟨hl,lt_of_not_ge hq17⟩ he.1.1 he.1.2
          exact ⟨_,⟨⟨(by norm_num : (1/8:ℝ) ≤ 5/8).trans ht.1,
            ht.2.trans (by norm_num)⟩,
            he.2,hs'⟩,hp',hq'⟩
        obtain ⟨t,ht,hp',hq'⟩ := low_blockers_recover_late ⟨hp7,by linarith⟩ ⟨hl,lt_of_not_ge hq17⟩
        exact ⟨t,late ht hs3,hp',hq'⟩
      · refine ⟨3/8,upper hs3,not_inWay_iff.mpr ?_,not_inWay_iff.mpr ?_⟩
        · apply Fresh.Localisation.clear_of_window 2 <;> norm_num <;> linarith
        · apply Fresh.Localisation.clear_of_window 4 <;> norm_num <;> linarith
  have hw : ∃ t, good t ∧ ¬ InWay x t ∧ ¬ InWay y t := by
    by_cases h : InWay x (1/8)
    · exact dispatch hx hy h
    by_cases h' : InWay y (1/8)
    · obtain ⟨t,ht,hy',hx'⟩ := dispatch hy hx h'
      exact ⟨t,ht,hx',hy'⟩
    · exact ⟨1/8,first ⟨le_rfl,by norm_num⟩,h,h'⟩
  obtain ⟨t,⟨ht,hcore,hs'⟩,hx',hy'⟩ := hw
  refine ⟨t,ht,fun d hd => ?_⟩
  rcases Finset.mem_union.mp hd with hd | hd
  · exact hcore d hd
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact not_inWay_iff.mp hs'
    · exact not_inWay_iff.mp hx'
    · exact not_inWay_iff.mp hy'

theorem adjustedCoreTime_subset {a t : ℝ} (ha : (9/32:ℝ) ≤ a)
    (ht : AdjustedCoreTime a t) : ReplacementCoreTime t := by
  rcases ht with h | h | h | rfl | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨ha.trans h.1,h.2⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨le_rfl,by norm_num⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- The original retained-core theorem uses the fixed second opening. -/
theorem replacement_of_retained_core {S : Finset ℝ} {s x y : ℝ}
    (hcore : ∀ t, ReplacementCoreTime t → LonelyAt S t)
    (hs : s ∈ Icc (17/7:ℝ) (28/9))
    (hx : x ∈ Icc (1:ℝ) 15) (hy : y ∈ Icc (1:ℝ) 15) :
    ∃ t ∈ Icc (1/8:ℝ) (7/8), LonelyAt (S ∪ {s,x,y}) t := by
  apply replacement_of_adjusted_core (a := 9/32) (by constructor <;> norm_num)
    (fun h => (by linarith [hs.2] : False).elim) _ ⟨hs.1,by linarith [hs.2]⟩ hx hy
  exact fun t ht => hcore t (adjustedCoreTime_subset (by norm_num) ht)

/-- A displaced third reading and two independent deviations,
with the four other normalized readings fixed. -/
theorem third_reading_replacement {s x y : ℝ}
    (hs : s ∈ Icc (17/7:ℝ) (28/9))
    (hx : x ∈ Icc (1:ℝ) 15) (hy : y ∈ Icc (1:ℝ) 15) :
    ∃ t ∈ Icc (1/8:ℝ) (7/8),
      LonelyAt (({1,2,4,5} : Finset ℝ) ∪ {s,x,y}) t :=
  replacement_of_retained_core (fun _ h => retained_four h) hs hx hy

#print axioms low_blockers_recover_late
#print axioms low_blockers_moving_opening
#print axioms lowered_reading_second_opening
#print axioms replacement_of_adjusted_core
#print axioms replacement_of_retained_core
#print axioms third_reading_replacement

end Fresh.Cascade
