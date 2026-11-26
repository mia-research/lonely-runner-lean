import Fresh.NativeRecoveredSecondGrid

/-! A fast third reader and an arbitrary fourth reader reuse the native
forced triple tail. Its phase displacement retains the minimum and slow
readers without a third/fourth origin-phase or terminal-clearance premise. -/
namespace Fresh.NativeHierarchicalFourthTail
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeThirdReaderRebound
  Fresh.NativeOutsideGroupDisplacement Fresh.FastestCaptureRetention

theorem prefix_displacement (d p q r V : ℝ) (hd : 0<d) (hp : 0<p) (hq : 0<q) (hr : 0<r)
    (hfastp : 8*d ≤ p) (hfastq : 32*d ≤ q) (hfastr : 96*d ≤ r)
    (hpc : InWay p (V+1/(8*d))) (hqc : InWay q (labelledOpening p (V+1/(8*d))))
    (hrc : InWay r (labelledOpening q (labelledOpening p (V+1/(8*d))))) :
    0<labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d))))-V ∧
      d*(labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d))))-V)<1/6 := by
  let W := V+1/(8*d)
  let Z := labelledOpening p W
  let Y := labelledOpening q Z
  let T := labelledOpening r Y
  have h0 := captured_labelled_advance p W hp hpc
  have h1 := captured_labelled_advance q Z hq hqc
  have h2 := captured_labelled_advance r Y hr hrc
  have hb0 := mul_le_mul_of_nonneg_right hfastp h0.1.le
  have hb1 := mul_le_mul_of_nonneg_right hfastq h1.1.le
  have hb2 := mul_le_mul_of_nonneg_right hfastr h2.1.le
  have hstep : 0<1/(8*d) := by positivity
  have hid : d*(1/(8*d))=1/8 := by field_simp
  change 0<T-V ∧ d*(T-V)<1/6
  change 0<Z-W ∧ p*(Z-W)<1/4 at h0
  change 8*d*(Z-W) ≤ p*(Z-W) at hb0
  dsimp [W] at h0 hb0
  constructor <;> nlinarith only [h0.1,h1.1,h2.1,hstep,hid,h0.2,h1.2,h2.2,hb0,hb1,hb2]

theorem minimum_window (p q r s Z : ℝ) (M : ℤ)
    (hp : 0<p) (hq : 0<q) (hr : 0<r) (hs : 0<s)
    (hfastq : 4*p ≤ q) (hfastr : 12*p ≤ r) (hps : p ≤ s) (hqr : 3*q<r)
    (hown : p*Z=(M : ℝ)+1/8) (hqc : InWay q Z)
    (hrc : InWay r (labelledOpening q Z))
    (hsc : InWay s (labelledOpening r (labelledOpening q Z))) :
    (M : ℝ)+1/8 ≤ p*forcedEnd r q s (labelledOpening q Z) ∧
      p*forcedEnd r q s (labelledOpening q Z)<(M : ℝ)+7/8 := by
  let Y := labelledOpening q Z
  let T := labelledOpening r Y
  let F := forcedEnd r q s Y
  have h1 := captured_labelled_advance q Z hq hqc
  have h2 := captured_labelled_advance r Y hr hrc
  have h3 := captured_labelled_advance s T hs hsc
  have ht := forced_tail_displacement r q s Y (label (q*Z)) hr hq hs hqr
    (labelled_opening_identity q Z hq) hrc hsc
  have hFT : 0 ≤ F-T := by linarith only [ht.1,h3.1]
  have hbound := mul_le_mul_of_nonneg_right hps hFT
  have hb1 := mul_le_mul_of_nonneg_right hfastq h1.1.le
  have hb2 := mul_le_mul_of_nonneg_right hfastr h2.1.le
  have hFZ : 0 ≤ F-Z := by linarith only [hFT,h1.1,h2.1]
  have hlo := mul_nonneg hp.le hFZ
  change (M : ℝ)+1/8 ≤ p*F ∧ p*F<(M : ℝ)+7/8
  constructor <;> nlinarith only [hown,hlo,ht.2,hbound,h1.2,h2.2,hb1,hb2]

theorem forced_displacement (d p q r s V : ℝ)
    (hd : 0<d) (hp : 0<p) (hq : 0<q) (hr : 0<r) (hs : 0<s)
    (hfastp : 8*d ≤ p) (hfastq : 32*d ≤ q) (hfastr : 96*d ≤ r) (hfasts : 8*d ≤ s)
    (hqr : 3*q<r) (hpc : InWay p (V+1/(8*d)))
    (hqc : InWay q (labelledOpening p (V+1/(8*d))))
    (hrc : InWay r (labelledOpening q (labelledOpening p (V+1/(8*d)))))
    (hsc : InWay s (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d)))))) :
    0<forcedEnd r q s (labelledOpening q (labelledOpening p (V+1/(8*d))))-V ∧
      d*(forcedEnd r q s (labelledOpening q (labelledOpening p (V+1/(8*d))))-V)<37/168 := by
  let W := V+1/(8*d)
  let Z := labelledOpening p W
  let Y := labelledOpening q Z
  let T := labelledOpening r Y
  let F := forcedEnd r q s Y
  have hprefix := prefix_displacement d p q r V hd hp hq hr hfastp hfastq hfastr hpc hqc hrc
  change 0<T-V ∧ d*(T-V)<1/6 at hprefix
  have h3 := captured_labelled_advance s T hs hsc
  have ht := forced_tail_displacement r q s Y (label (q*Z)) hr hq hs hqr
    (labelled_opening_identity q Z hq) hrc hsc
  have hFT : 0 ≤ F-T := by linarith only [ht.1,h3.1]
  have hbound := mul_le_mul_of_nonneg_right hfasts hFT
  change 0<F-V ∧ d*(F-V)<37/168
  constructor <;> nlinarith only [hprefix.1,hprefix.2,hFT,hbound,ht.2]

#print axioms prefix_displacement
#print axioms minimum_window
#print axioms forced_displacement
end Fresh.NativeHierarchicalFourthTail
