import Fresh.NativeSmallFourthGrid

/-! An initially clear second reader returns at the fourth opening.
When the fourth is above the third, that return forces the second above
it too. The existing pair tail then derives all processed-reader duties. -/
namespace Fresh.NativeLargeFourthTail
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeThirdReaderRebound
  Fresh.NativeOutsideGroupDisplacement Fresh.FastestCaptureRetention

theorem returned_second_above_third (q r s Y : ℝ) (N : ℤ)
    (hq : 0<q) (hr : 0<r) (hs : 0<s) (hrs : r ≤ s)
    (ho : q*Y=(N : ℝ)+1/8) (hrc : InWay r Y)
    (hsc : InWay s (labelledOpening r Y))
    (hqc : InWay q (labelledOpening s (labelledOpening r Y))) : r<q := by
  by_contra hn
  have hqr : q ≤ r := le_of_not_gt hn
  have hqs : q ≤ s := hqr.trans hrs
  have hfit : q*(r+s) ≤ 3*r*s := by
    have h1 := mul_le_mul_of_nonneg_right hqr hs.le
    have h2 := mul_le_mul_of_nonneg_right hqs hr.le
    nlinarith only [h1,h2,mul_pos hr hs]
  have hw := Fresh.NativeClearWindowRebound.own_two_window r s q Y N hr hs hq ho hrc hsc hfit
  exact not_lt.mpr (clear_of_window N hw.1 hw.2.le) hqc

theorem third_window (r s q T : ℝ) (N : ℤ)
    (hr : 0<r) (hs : 0<s) (hq : 0<q) (hrs : r ≤ s) (hrq : r ≤ q)
    (ho : r*T=(N : ℝ)+1/8) (hsc : InWay s T)
    (hqc : InWay q (labelledOpening s T)) :
    (N : ℝ)+1/8 ≤ r*partnerEnd s q (labelledOpening s T) ∧
      r*partnerEnd s q (labelledOpening s T)<(N : ℝ)+7/8 := by
  let G := labelledOpening s T
  let F := partnerEnd s q G
  have h1 := captured_labelled_advance s T hs hsc
  have h2 := captured_labelled_advance q G hq hqc
  have ht := direct_tail_displacement s q G (label (s*T)) hs hq (labelled_opening_identity s T hs) hqc
  have hFG : 0 ≤ F-G := by linarith only [ht.1,h2.1]
  have hb1 := mul_le_mul_of_nonneg_right hrs h1.1.le
  have hb2 := mul_le_mul_of_nonneg_right hrq hFG
  have hlo := mul_nonneg hr.le (show 0 ≤ F-T by linarith only [hFG,h1.1])
  change (N : ℝ)+1/8 ≤ r*F ∧ r*F<(N : ℝ)+7/8
  constructor <;> nlinarith only [ho,hlo,h1.2,ht.2,hb1,hb2]

theorem minimum_window (p q r s Z : ℝ) (M : ℤ)
    (hp : 0<p) (hq : 0<q) (hr : 0<r) (hs : 0<s)
    (hpq : 4*p ≤ q) (hpr : p ≤ r) (hps : p ≤ s)
    (ho : p*Z=(M : ℝ)+1/8) (hqc : InWay q Z)
    (hrc : InWay r (labelledOpening q Z))
    (hsc : InWay s (labelledOpening r (labelledOpening q Z)))
    (hqG : InWay q (labelledOpening s (labelledOpening r (labelledOpening q Z)))) :
    (M : ℝ)+1/8 ≤ p*partnerEnd s q (labelledOpening s (labelledOpening r (labelledOpening q Z))) ∧
      p*partnerEnd s q (labelledOpening s (labelledOpening r (labelledOpening q Z)))<(M : ℝ)+7/8 := by
  let Y := labelledOpening q Z
  let T := labelledOpening r Y
  let G := labelledOpening s T
  let F := partnerEnd s q G
  have h1 := captured_labelled_advance q Z hq hqc
  have h2 := captured_labelled_advance r Y hr hrc
  have h3 := captured_labelled_advance s T hs hsc
  have h4 := captured_labelled_advance q G hq hqG
  have ht := direct_tail_displacement s q G (label (s*T)) hs hq (labelled_opening_identity s T hs) hqG
  have hFG : 0 ≤ F-G := by linarith only [ht.1,h4.1]
  have hb1 := mul_le_mul_of_nonneg_right hpq h1.1.le
  have hb2 := mul_le_mul_of_nonneg_right hpr h2.1.le
  have hb3 := mul_le_mul_of_nonneg_right hps h3.1.le
  have hb4 := mul_le_mul_of_nonneg_right hpq hFG
  have hlo := mul_nonneg hp.le (show 0 ≤ F-Z by linarith only [hFG,h1.1,h2.1,h3.1])
  change (M : ℝ)+1/8 ≤ p*F ∧ p*F<(M : ℝ)+7/8
  constructor <;> nlinarith only [ho,hlo,h1.2,h2.2,h3.2,ht.2,hb1,hb2,hb3,hb4]

theorem local_displacement (d p q r s V : ℝ)
    (hd : 0<d) (hp : 0<p) (hq : 0<q) (hr : 0<r) (hs : 0<s)
    (hfastp : 8*d ≤ p) (hfastq : 32*d ≤ q) (hfastr : 8*d ≤ r) (hfasts : 8*d ≤ s)
    (hpc : InWay p (V+1/(8*d))) (hqc : InWay q (labelledOpening p (V+1/(8*d))))
    (hrc : InWay r (labelledOpening q (labelledOpening p (V+1/(8*d)))))
    (hsc : InWay s (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d))))))
    (hqG : InWay q (labelledOpening s (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d))))))) :
    0<partnerEnd s q (labelledOpening s (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d))))))-V ∧
      d*(partnerEnd s q (labelledOpening s (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d))))))-V)<91/384 := by
  let W := V+1/(8*d)
  let Z := labelledOpening p W
  let Y := labelledOpening q Z
  let T := labelledOpening r Y
  let G := labelledOpening s T
  let F := partnerEnd s q G
  have hpre := Fresh.NativeFastSecondResetTail.fourth_prefix_displacement d p q r s V hd hp hq hr hs hfastp hfastq hfastr hfasts hpc hqc hrc hsc
  have h4 := captured_labelled_advance q G hq hqG
  have ht := direct_tail_displacement s q G (label (s*T)) hs hq (labelled_opening_identity s T hs) hqG
  have hFG : 0 ≤ F-G := by linarith only [ht.1,h4.1]
  have hb := mul_le_mul_of_nonneg_right hfastq hFG
  change 0<F-V ∧ d*(F-V)<91/384
  constructor <;> nlinarith only [hpre.1,hpre.2,hFG,ht.2,hb]

#print axioms returned_second_above_third
#print axioms third_window
#print axioms minimum_window
#print axioms local_displacement
end Fresh.NativeLargeFourthTail
