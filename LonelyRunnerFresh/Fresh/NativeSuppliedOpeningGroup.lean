import Fresh.NativeOutsideGroupDisplacement
import Fresh.NativeSuppliedOpeningTriple

/-! Native captured-group coalescence at an explicitly supplied incoming
anchor opening, including both closed deviation edges. No shared cohort
opening or bound on the independent current labels is assumed. -/
open Classical
namespace Fresh.NativeSuppliedOpeningGroup
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeOneReaderDeformation Fresh.NativeOpeningReversal
  Fresh.NativeThirdReaderRetention Fresh.NativeResidualReturn
  Fresh.NativeCoalescedCaptureRelay Fresh.NativeFixedPrefixTransport
  Fresh.NativeOutsideGroupDisplacement Fresh.NativeSuppliedOpeningTriple

theorem rebound_tail_displacement (a b c E : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hab : 3*b<a) (hthird : InWay c (E))
    (hret : InWay b (partnerEnd a c E)) :
    labelledOpening c (E) ≤ reboundEnd a b c E ∧
      a*b*c*(reboundEnd a b c E-E)<(a*b+a*c+2*b*c)/4 := by
  let F := labelledOpening c E
  let T := partnerEnd a c E
  have hF := labelled_opening_identity c E hc
  by_cases hr : InWay a F
  · have hT : T=labelledOpening a F := by
      change (if InWay a F then labelledOpening a F else F)=labelledOpening a F
      rw [if_pos hr]
    have hR : reboundEnd a b c E=partnerEnd a b T := by
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
      dsimp [T] at h2 ⊢
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
      have hR : reboundEnd a b c E=labelledOpening a U := by
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
    · have hR : reboundEnd a b c E=U := by
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

theorem forced_tail_displacement (a b c C E : ℝ) (M L : ℤ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hab : 3*b<a)
    (ho : b*C=(M : ℝ)+1/8) (hCE : C≤E) (hquarter : a*(E-C)≤1/4)
    (hE : a*E=(L : ℝ)+1/8) (hthird : InWay c E) :
    labelledOpening c E ≤ exitEnd a b c E ∧ c*(exitEnd a b c E-E)<3/7 := by
  by_cases hret : InWay b (partnerEnd a c E)
  · have hh := rebound_tail_displacement a b c E ha hb hc hab hthird hret
    have hslow := supplied_slow_third a b c C E M L ha hb hc hab ho hCE hquarter hE hthird hret
    have hca : 7*c<a := hslow.trans hab
    have h1 := mul_lt_mul_of_pos_left hslow ha
    have h2 := mul_lt_mul_of_pos_right hca hb
    have hpoly : 7*(a*b+a*c+2*b*c)<12*a*b := by nlinarith only [h1,h2]
    rw [exitEnd,if_pos hret]
    refine ⟨hh.1,?_⟩
    by_contra hn
    have hscale := mul_le_mul_of_nonneg_left (le_of_not_gt hn) (mul_pos ha hb).le
    nlinarith only [hscale,hh.2,hpoly]
  · have hh := direct_tail_displacement a c E L ha hc hE hthird
    rw [exitEnd,if_neg hret]
    exact ⟨hh.1,lt_trans hh.2 (by norm_num)⟩

theorem captured_group_window (a b c s C E : ℝ) (M L : ℤ) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hs : 0<s)
    (hab : 3*b<a) (ho : b*C=(M : ℝ)+1/8) (hCE : C≤E) (hquarter : a*(E-C)≤1/4) (hE : a*E=(L : ℝ)+1/8)
    (hthird : InWay c (E)) (hcap : InWay s (E))
    (hstrip : 4*s ≤ 7*c)
    (horder : labelledOpening s (E) ≤ labelledOpening c (E)) :
    (label (s*E) : ℝ)+1/8 ≤ s*exitEnd a b c E ∧
      s*exitEnd a b c E<(label (s*E) : ℝ)+7/8 := by
  have ht := forced_tail_displacement a b c C E M L ha hb hc hab ho hCE hquarter hE hthird
  have hcstep := captured_labelled_advance c (E) hc hthird
  have hEW : E ≤ exitEnd a b c E := by linarith only [hcstep.1,ht.1]
  have hlow := mul_le_mul_of_nonneg_left (horder.trans ht.1) hs.le
  rw [labelled_opening_identity s _ hs] at hlow
  have hbound := mul_le_mul_of_nonneg_right hstrip (sub_nonneg.mpr hEW)
  have hstart := (capture_at_label s (E) hcap).2
  constructor
  · exact hlow
  · nlinarith only [hbound,ht.2,hstart]

theorem captured_group_zero (a b c s C E : ℝ) (M L : ℤ) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hs : 0<s)
    (hab : 3*b<a) (ho : b*C=(M : ℝ)+1/8) (hCE : C≤E) (hquarter : a*(E-C)≤1/4) (hE : a*E=(L : ℝ)+1/8)
    (hthird : InWay c (E)) (hcap : InWay s (E))
    (hstrip : 4*s ≤ 7*c)
    (horder : labelledOpening s (E) ≤ labelledOpening c (E)) :
    advance s (E) (exitEnd a b c E)=0 := by
  have hh := captured_group_window a b c s C E M L ha hb hc hs hab ho hCE hquarter hE hthird hcap hstrip horder
  have hl := (entry_iff_label s (exitEnd a b c E) (label (s*E))).1 (Or.inl ⟨hh.1,hh.2.le⟩)
  simp only [advance,hl,sub_self,Int.toNat_zero]

theorem captured_group_segment (a b c s C E U : ℝ) (M L : ℤ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hs : 0<s)
    (hab : 3*b<a) (ho : b*C=(M : ℝ)+1/8) (hCE : C≤E) (hquarter : a*(E-C)≤1/4) (hE : a*E=(L : ℝ)+1/8)
    (hthird : InWay c (E)) (hcap : InWay s (E))
    (hstrip : 4*s ≤ 7*c)
    (horder : labelledOpening s (E) ≤ labelledOpening c (E))
    (hFU : labelledOpening c (E) ≤ U) (hUW : U ≤ exitEnd a b c E) :
    ¬InWay s U ∧ label (s*U)=label (s*E) := by
  have hwindow := captured_group_window a b c s C E M L ha hb hc hs hab ho hCE hquarter hE hthird hcap hstrip horder
  have hlo := mul_le_mul_of_nonneg_left horder hs.le
  rw [labelled_opening_identity s _ hs] at hlo
  exact band_at_point s (labelledOpening c (E)) U (exitEnd a b c E)
    (label (s*E)) hs.le hFU hUW hlo hwindow.2.le

theorem captured_group_interval (a b c lo s hi C E : ℝ) (M L K : ℤ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hlo : 0<lo) (hls : lo ≤ s) (hsh : s ≤ hi) (hEp : 0<E)
    (hab : 3*b<a) (ho : b*C=(M : ℝ)+1/8) (hCE : C≤E) (hquarter : a*(E-C)≤1/4) (hE : a*E=(L : ℝ)+1/8)
    (hthird : InWay c (E))
    (hlabels : label (lo*E)=K ∧ label (hi*E)=K)
    (hcapHi : InWay hi (E)) (hK : 0 ≤ (K : ℝ)+1/8)
    (hstrip : 4*hi ≤ 7*c)
    (horder : Fresh.FastestCaptureRetention.opening lo K ≤ labelledOpening c (E)) :
    (K : ℝ)+1/8 ≤ s*exitEnd a b c E ∧ s*exitEnd a b c E<(K : ℝ)+7/8 := by
  have hlabel := speed_interval_label lo s hi (E) hls hsh hEp.le (hlabels.1.trans hlabels.2.symm)
  rw [hlabels.1] at hlabel
  have hcap := speed_interval_capture lo s hi (E) hls hsh hEp.le
    (hlabels.1.trans hlabels.2.symm) hcapHi
  have hopen := (interval_opening_bounds lo s hi K hlo hls hsh hK).2.trans horder
  have horder' : labelledOpening s (E) ≤ labelledOpening c (E) := by
    change Fresh.FastestCaptureRetention.opening s (label (s*E)) ≤ _
    rw [hlabel]
    exact hopen
  have hh := captured_group_window a b c s C E M L ha hb hc (hlo.trans_le hls) hab ho hCE hquarter hE hthird hcap
    (by linarith only [hsh,hstrip]) horder'
  simpa only [hlabel] using hh

#print axioms rebound_tail_displacement
#print axioms forced_tail_displacement
#print axioms captured_group_window
#print axioms captured_group_zero
#print axioms captured_group_segment
#print axioms captured_group_interval
end Fresh.NativeSuppliedOpeningGroup
