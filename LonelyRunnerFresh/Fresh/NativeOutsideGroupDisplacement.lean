import Fresh.NativeResidualReturnArrangement

/-! Native displacement of the forced triple tail from the outside setter's
entry. A whole captured packet with ordered lower openings and disparities
in the7/4 strip retains its original clear windows through every rebound.
This is a local captured-opening calculation, not a global time budget. -/
open Classical
namespace Fresh.NativeOutsideGroupDisplacement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeOneReaderDeformation Fresh.NativeOpeningReversal
  Fresh.NativeThirdReaderRetention Fresh.NativeThirdReaderRebound Fresh.NativeResidualReturn
  Fresh.NativeCoalescedCaptureRelay Fresh.NativeFixedPrefixTransport

theorem own_pair_compact_end (d s P : ℝ) (N : ℤ) (hd : 0<d) (hs : 0<s)
    (ho : s*P=(N : ℝ)+1/8) (hw : InWay d P) (hr : s ≤ 3*d) :
    partnerEnd s d P=labelledOpening d P := by
  have hh := own_opening_retained d s P (labelledOpening d P) (label (d*P)) N hd hs.le hr ho hw
    (labelled_opening_identity d P hd) rfl
  have hn : ¬InWay s (labelledOpening d P) := not_lt.mpr (clear_of_window N hh.1 hh.2.le)
  unfold partnerEnd
  rw [if_neg hn]

theorem direct_tail_displacement (a c E : ℝ) (N : ℤ) (ha : 0<a) (hc : 0<c)
    (ho : a*E=(N : ℝ)+1/8) (hw : InWay c E) :
    labelledOpening c E ≤ partnerEnd a c E ∧ c*(partnerEnd a c E-E)<1/3 := by
  let F := labelledOpening c E
  by_cases hr : InWay a F
  · have he : partnerEnd a c E=labelledOpening a F := by
      change (if InWay a F then labelledOpening a F else F)=labelledOpening a F
      rw [if_pos hr]
    have hstep := captured_labelled_advance a F ha hr
    have hgap := recapture_forces_three a c E F N (label (c*E)) ha hc ho hw
      (labelled_opening_identity c E hc) rfl hr
    have htail := pair_tail_weighted a c E ha hc hw
    constructor
    · rw [he]; linarith only [hstep.1]
    · by_contra hn
      have hh := mul_le_mul_of_nonneg_left (le_of_not_gt hn) ha.le
      nlinarith only [hh,htail,hgap]
  · have he : partnerEnd a c E=F := by
      change (if InWay a F then labelledOpening a F else F)=F
      rw [if_neg hr]
    rw [he]
    exact ⟨le_rfl,lt_trans (captured_labelled_advance c E hc hw).2 (by norm_num)⟩

theorem rebound_tail_displacement (a b c C : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hab : 3*b<a) (hthird : InWay c (labelledOpening a C))
    (hret : InWay b (thirdEnd a c C)) :
    labelledOpening c (labelledOpening a C) ≤ reboundEnd a b c C ∧
      a*b*c*(reboundEnd a b c C-labelledOpening a C)<(a*b+a*c+2*b*c)/4 := by
  let E := labelledOpening a C
  let F := labelledOpening c E
  let T := thirdEnd a c C
  have hF := labelled_opening_identity c E hc
  by_cases hr : InWay a F
  · have hT : T=labelledOpening a F := by
      change (if InWay a F then labelledOpening a F else F)=labelledOpening a F
      rw [if_pos hr]
    have hR : reboundEnd a b c C=partnerEnd a b T := by
      change (if InWay a F then partnerEnd a b T else _)=partnerEnd a b T
      rw [if_pos hr]
    have hFT := (captured_labelled_advance a F ha hr).1
    have hTR := pair_end_after a b T ha hb (label (a*F)) (by rw [hT]; exact labelled_opening_identity a F ha) hret
    have h1 := mul_lt_mul_of_pos_left (pair_tail_weighted a c E ha hc hthird) hb
    have h2 := mul_lt_mul_of_pos_left (pair_tail_weighted a b T ha hb hret) hc
    rw [hR]
    constructor
    · change F ≤ partnerEnd a b T
      have hFT' : F ≤ T := by rw [hT]; linarith only [hFT]
      exact hFT'.trans hTR.le
    · change a*b*c*(partnerEnd a b T-E)<_
      dsimp [T,thirdEnd] at h2 ⊢
      nlinarith only [h1,h2]
  · have hT : T=F := by
      change (if InWay a F then labelledOpening a F else F)=F
      rw [if_neg hr]
    let U := labelledOpening b T
    have hfirst := captured_labelled_advance c E hc hthird
    have hmid := captured_labelled_advance b T hb hret
    have hTU : T<U := by dsimp [U]; linarith only [hmid.1]
    have hFU : F ≤ U := by simpa only [hT] using hTU.le
    have h1 := mul_lt_mul_of_pos_left hfirst.2 (mul_pos ha hb)
    have h2 := mul_lt_mul_of_pos_left hmid.2 (mul_pos ha hc)
    have hbc := mul_pos hb hc
    by_cases hA : InWay a U
    · have hU := labelled_opening_identity b T hb
      have he := own_pair_compact_end a b U (label (b*T)) ha hb hU hA (by nlinarith only [hab,hb])
      have hR : reboundEnd a b c C=labelledOpening a U := by
        change (if InWay a F then _ else if InWay a U then partnerEnd b a U else U)=labelledOpening a U
        rw [if_neg hr,if_pos hA,he]
      have hlast := captured_labelled_advance a U ha hA
      have hUV : U<labelledOpening a U := by linarith only [hlast.1]
      have h3 := mul_lt_mul_of_pos_left hlast.2 hbc
      rw [hR]
      constructor
      · change F ≤ labelledOpening a U
        exact hFU.trans hUV.le
      · change a*b*c*(labelledOpening a U-E)<_
        dsimp [U] at h2 h3 ⊢
        rw [hT] at h2 h3 ⊢
        nlinarith only [h1,h2,h3,hbc]
    · have hR : reboundEnd a b c C=U := by
        change (if InWay a F then _ else if InWay a U then _ else U)=U
        rw [if_neg hr,if_neg hA]
      rw [hR]
      constructor
      · change F ≤ U
        exact hFU
      · change a*b*c*(U-E)<_
        dsimp [U] at h2 ⊢
        rw [hT] at h2 ⊢
        nlinarith only [h1,h2,hbc]

theorem forced_tail_displacement (a b c C : ℝ) (M : ℤ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hab : 3*b<a) (ho : b*C=(M : ℝ)+1/8) (hw : InWay a C)
    (hthird : InWay c (labelledOpening a C)) :
    labelledOpening c (labelledOpening a C) ≤ forcedEnd a b c C ∧
      c*(forcedEnd a b c C-labelledOpening a C)<3/7 := by
  by_cases hret : InWay b (thirdEnd a c C)
  · have hh := rebound_tail_displacement a b c C ha hb hc hab hthird hret
    have hslow := recaptured_old_forces_slow_third a b c C M ha hb hc hab ho hw hthird hret
    have hca : 7*c<a := hslow.trans hab
    have h1 := mul_lt_mul_of_pos_left hslow ha
    have h2 := mul_lt_mul_of_pos_right hca hb
    have hpoly : 7*(a*b+a*c+2*b*c)<12*a*b := by nlinarith only [h1,h2]
    rw [forcedEnd,if_pos hret]
    refine ⟨hh.1,?_⟩
    by_contra hn
    have hscale := mul_le_mul_of_nonneg_left (le_of_not_gt hn) (mul_pos ha hb).le
    nlinarith only [hscale,hh.2,hpoly]
  · have hh := direct_tail_displacement a c (labelledOpening a C) (label (a*C)) ha hc
      (labelled_opening_identity a C ha) hthird
    rw [forcedEnd,if_neg hret]
    exact ⟨hh.1,lt_trans hh.2 (by norm_num)⟩

theorem captured_group_window (a b c s C : ℝ) (M : ℤ) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hs : 0<s)
    (hab : 3*b<a) (ho : b*C=(M : ℝ)+1/8) (hw : InWay a C)
    (hthird : InWay c (labelledOpening a C)) (hcap : InWay s (labelledOpening a C))
    (hstrip : 4*s ≤ 7*c)
    (horder : labelledOpening s (labelledOpening a C) ≤ labelledOpening c (labelledOpening a C)) :
    (label (s*labelledOpening a C) : ℝ)+1/8 ≤ s*forcedEnd a b c C ∧
      s*forcedEnd a b c C<(label (s*labelledOpening a C) : ℝ)+7/8 := by
  have ht := forced_tail_displacement a b c C M ha hb hc hab ho hw hthird
  have hcstep := captured_labelled_advance c (labelledOpening a C) hc hthird
  have hEW : labelledOpening a C ≤ forcedEnd a b c C := by linarith only [hcstep.1,ht.1]
  have hlow := mul_le_mul_of_nonneg_left (horder.trans ht.1) hs.le
  rw [labelled_opening_identity s _ hs] at hlow
  have hbound := mul_le_mul_of_nonneg_right hstrip (sub_nonneg.mpr hEW)
  have hstart := (capture_at_label s (labelledOpening a C) hcap).2
  constructor
  · exact hlow
  · nlinarith only [hbound,ht.2,hstart]

theorem captured_group_zero (a b c s C : ℝ) (M : ℤ) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hs : 0<s)
    (hab : 3*b<a) (ho : b*C=(M : ℝ)+1/8) (hw : InWay a C)
    (hthird : InWay c (labelledOpening a C)) (hcap : InWay s (labelledOpening a C))
    (hstrip : 4*s ≤ 7*c)
    (horder : labelledOpening s (labelledOpening a C) ≤ labelledOpening c (labelledOpening a C)) :
    advance s (labelledOpening a C) (forcedEnd a b c C)=0 := by
  have hh := captured_group_window a b c s C M ha hb hc hs hab ho hw hthird hcap hstrip horder
  have hl := (entry_iff_label s (forcedEnd a b c C) (label (s*labelledOpening a C))).1 (Or.inl ⟨hh.1,hh.2.le⟩)
  simp only [advance,hl,sub_self,Int.toNat_zero]

theorem captured_group_segment (a b c s C U : ℝ) (M : ℤ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hs : 0<s)
    (hab : 3*b<a) (ho : b*C=(M : ℝ)+1/8) (hw : InWay a C)
    (hthird : InWay c (labelledOpening a C)) (hcap : InWay s (labelledOpening a C))
    (hstrip : 4*s ≤ 7*c)
    (horder : labelledOpening s (labelledOpening a C) ≤ labelledOpening c (labelledOpening a C))
    (hFU : labelledOpening c (labelledOpening a C) ≤ U) (hUW : U ≤ forcedEnd a b c C) :
    ¬InWay s U ∧ label (s*U)=label (s*labelledOpening a C) := by
  have hwindow := captured_group_window a b c s C M ha hb hc hs hab ho hw hthird hcap hstrip horder
  have hlo := mul_le_mul_of_nonneg_left horder hs.le
  rw [labelled_opening_identity s _ hs] at hlo
  exact band_at_point s (labelledOpening c (labelledOpening a C)) U (forcedEnd a b c C)
    (label (s*labelledOpening a C)) hs.le hFU hUW hlo hwindow.2.le

theorem captured_group_interval (a b c lo s hi C : ℝ) (M K : ℤ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hlo : 0<lo) (hls : lo ≤ s) (hsh : s ≤ hi) (hC : 0<C)
    (hab : 3*b<a) (ho : b*C=(M : ℝ)+1/8) (hw : InWay a C)
    (hthird : InWay c (labelledOpening a C))
    (hlabels : label (lo*labelledOpening a C)=K ∧ label (hi*labelledOpening a C)=K)
    (hcapHi : InWay hi (labelledOpening a C)) (hK : 0 ≤ (K : ℝ)+1/8)
    (hstrip : 4*hi ≤ 7*c)
    (horder : Fresh.FastestCaptureRetention.opening lo K ≤ labelledOpening c (labelledOpening a C)) :
    (K : ℝ)+1/8 ≤ s*forcedEnd a b c C ∧ s*forcedEnd a b c C<(K : ℝ)+7/8 := by
  have hstep := captured_labelled_advance a C ha hw
  have hE : 0<labelledOpening a C := by linarith only [hC,hstep.1]
  have hlabel := speed_interval_label lo s hi (labelledOpening a C) hls hsh hE.le (hlabels.1.trans hlabels.2.symm)
  rw [hlabels.1] at hlabel
  have hcap := speed_interval_capture lo s hi (labelledOpening a C) hls hsh hE.le
    (hlabels.1.trans hlabels.2.symm) hcapHi
  have hopen := (interval_opening_bounds lo s hi K hlo hls hsh hK).2.trans horder
  have horder' : labelledOpening s (labelledOpening a C) ≤ labelledOpening c (labelledOpening a C) := by
    change Fresh.FastestCaptureRetention.opening s (label (s*labelledOpening a C)) ≤ _
    rw [hlabel]
    exact hopen
  have hh := captured_group_window a b c s C M ha hb hc (hlo.trans_le hls) hab ho hw hthird hcap
    (by linarith only [hsh,hstrip]) horder'
  simpa only [hlabel] using hh

#print axioms captured_group_segment
#print axioms captured_group_interval

#print axioms own_pair_compact_end
#print axioms direct_tail_displacement
#print axioms rebound_tail_displacement
#print axioms forced_tail_displacement
#print axioms captured_group_window
#print axioms captured_group_zero
end Fresh.NativeOutsideGroupDisplacement
