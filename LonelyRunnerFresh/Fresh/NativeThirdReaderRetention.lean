import Fresh.NativeOpeningReversalArrangement

/-! A third-reader pair tail retains an earlier reader's own clear window
under a native homogeneous face. Failure by recapture forces a slower third
reader. These are local displacement faces, not a global move/time budget. -/
open Classical
namespace Fresh.NativeThirdReaderRetention
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeOneReaderDeformation Fresh.NativeCoalescedCaptureRelay
  Fresh.NativeOpeningReversal Fresh.FastestCaptureRetention

theorem captured_labelled_advance (d C : ℝ) (hd : 0<d) (hw : InWay d C) :
    0<labelledOpening d C-C ∧ d*(labelledOpening d C-C)<1/4 := by
  have hb := capture_at_label d C hw
  exact Fresh.NativeOpeningRetention.capture_advance d C _ _ hd
    (labelled_opening_identity d C hd) hb.1 hb.2

theorem pair_end_after (a c E : ℝ) (ha : 0<a) (hc : 0<c) (N : ℤ)
    (ho : a*E=(N : ℝ)+1/8) (hw : InWay c E) : E<partnerEnd a c E := by
  obtain ⟨U,hEU,hUT,hm⟩ := (pair_last_move_and_clear a c E N ha hc ho hw).1
  exact hEU.trans_lt hUT

-- Sum of the actual captured-opening displacements in this local pair tail.
theorem pair_tail_weighted (a c E : ℝ) (ha : 0<a) (hc : 0<c)
    (hw : InWay c E) : a*c*(partnerEnd a c E-E)<(a+c)/4 := by
  let F := labelledOpening c E
  have hfirst := captured_labelled_advance c E hc hw
  have hf := mul_lt_mul_of_pos_left hfirst.2 ha
  by_cases hr : InWay a F
  · have hlast := captured_labelled_advance a F ha hr
    have hl := mul_lt_mul_of_pos_left hlast.2 hc
    have he : partnerEnd a c E=labelledOpening a F := by
      change (if InWay a F then labelledOpening a F else F)=labelledOpening a F
      rw [if_pos hr]
    rw [he]
    dsimp [F] at hl ⊢
    nlinarith only [hf,hl]
  · have he : partnerEnd a c E=F := by
      change (if InWay a F then labelledOpening a F else F)=F
      rw [if_neg hr]
    rw [he]
    dsimp [F]
    nlinarith only [hf,hc]

noncomputable def thirdEnd (a c C : ℝ) : ℝ := partnerEnd a c (labelledOpening a C)

theorem composed_displacement (a c C : ℝ) (ha : 0<a) (hc : 0<c)
    (hw : InWay a C) (hthird : InWay c (labelledOpening a C)) :
    a*c*(thirdEnd a c C-C)<(a+2*c)/4 := by
  have hfirst := captured_labelled_advance a C ha hw
  have hf := mul_lt_mul_of_pos_left hfirst.2 hc
  have ht := pair_tail_weighted a c (labelledOpening a C) ha hc hthird
  dsimp [thirdEnd]
  nlinarith only [hf,ht]

theorem old_opening_retained (a b c C : ℝ) (M : ℤ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (ho : b*C=(M : ℝ)+1/8) (hw : InWay a C)
    (hthird : InWay c (labelledOpening a C)) (hfit : a*b+2*b*c ≤ 3*a*c) :
    (M : ℝ)+1/8 ≤ b*thirdEnd a c C ∧ b*thirdEnd a c C<(M : ℝ)+7/8 := by
  have hfirst := captured_labelled_advance a C ha hw
  have hE := labelled_opening_identity a C ha
  have hET := pair_end_after a c (labelledOpening a C) ha hc _ hE hthird
  have hCT : C<thirdEnd a c C := by dsimp [thirdEnd]; linarith only [hfirst.1,hET]
  have hlow := mul_nonneg hb.le (sub_nonneg.mpr hCT.le)
  have ht := composed_displacement a c C ha hc hw hthird
  have hscaled := mul_lt_mul_of_pos_left ht hb
  have hupper : b*(thirdEnd a c C-C)<3/4 := by
    have hp := mul_pos ha hc
    by_contra hn
    have hh := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hp.le
    nlinarith only [hh,hscaled,hfit]
  constructor <;> nlinarith only [ho,hlow,hupper]

theorem triple_clear (a b c C : ℝ) (M : ℤ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (ho : b*C=(M : ℝ)+1/8) (hw : InWay a C)
    (hthird : InWay c (labelledOpening a C)) (hfit : a*b+2*b*c ≤ 3*a*c) :
    LonelyAt ({a,b,c} : Finset ℝ) (thirdEnd a c C) := by
  have hpair := (pair_last_move_and_clear a c (labelledOpening a C) (label (a*C)) ha hc
    (labelled_opening_identity a C ha) hthird).2
  have hbclear := old_opening_retained a b c C M ha hb hc ho hw hthird hfit
  intro d hd
  rcases Finset.mem_insert.mp hd with he|hd
  · subst d; exact hpair _ (Finset.mem_insert_self _ _)
  · rcases Finset.mem_insert.mp hd with he|hd
    · subst d; exact clear_of_window M hbclear.1 hbclear.2.le
    · rw [Finset.mem_singleton.mp hd]
      exact hpair _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

theorem simple_seven_three_fit (a b c : ℝ) (ha : 0<a) (hc : 0<c)
    (hab : 3*b<a) (hbc : 3*b ≤ 7*c) : a*b+2*b*c ≤ 3*a*c := by
  have h1 := mul_le_mul_of_nonneg_left hbc ha.le
  have h2 := mul_lt_mul_of_pos_right hab hc
  nlinarith only [h1,h2]

theorem recaptured_old_forces_slow_third (a b c C : ℝ) (M : ℤ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hab : 3*b<a)
    (ho : b*C=(M : ℝ)+1/8) (hw : InWay a C)
    (hthird : InWay c (labelledOpening a C)) (hret : InWay b (thirdEnd a c C)) : 7*c<3*b := by
  by_contra hn
  have hfit := simple_seven_three_fit a b c ha hc hab (le_of_not_gt hn)
  have hh := old_opening_retained a b c C M ha hb hc ho hw hthird hfit
  exact not_lt_of_ge (clear_of_window M hh.1 hh.2.le) hret

-- The face is monotone in the old reader: one upper endpoint guards a band.
theorem old_speed_interval_fit (a b hi c : ℝ) (ha : 0<a) (hc : 0<c)
    (hbh : b ≤ hi) (hfit : a*hi+2*hi*c ≤ 3*a*c) : a*b+2*b*c ≤ 3*a*c := by
  have hh := mul_le_mul_of_nonneg_right hbh (show 0 ≤ a+2*c by linarith only [ha,hc])
  nlinarith only [hh,hfit]

#print axioms captured_labelled_advance
#print axioms pair_end_after
#print axioms pair_tail_weighted
#print axioms composed_displacement
#print axioms old_opening_retained
#print axioms triple_clear
#print axioms simple_seven_three_fit
#print axioms recaptured_old_forces_slow_third
#print axioms old_speed_interval_fit
end Fresh.NativeThirdReaderRetention
