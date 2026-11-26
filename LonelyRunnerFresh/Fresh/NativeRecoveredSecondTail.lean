import Fresh.NativeFourthReversalArrangement

/-! A recovered second reader and a third reader reversing through the
fourth selection. These are the actual fragment's minimum and slow-tail
windows; the native triple composed fit is reused separately. -/
namespace Fresh.NativeRecoveredSecondTail
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.FastestCaptureRetention

theorem minimum_window (p q r s Z : ℝ) (M : ℤ)
    (hp : 0<p) (hq : 0<q) (hr : 0<r) (hs : 0<s)
    (hfastq : 4*p ≤ q) (hfastr : 3*p ≤ r) (hps : p ≤ s)
    (hown : p*Z=(M : ℝ)+1/8) (hqc : InWay q Z)
    (hrc : InWay r (labelledOpening q Z))
    (hsc : InWay s (labelledOpening r (labelledOpening q Z)))
    (hret : InWay r (labelledOpening s (labelledOpening r (labelledOpening q Z)))) :
    (M : ℝ)+1/8 ≤ p*labelledOpening r (labelledOpening s (labelledOpening r (labelledOpening q Z))) ∧
      p*labelledOpening r (labelledOpening s (labelledOpening r (labelledOpening q Z)))<(M : ℝ)+7/8 := by
  let Y := labelledOpening q Z
  let T := labelledOpening r Y
  let G := labelledOpening s T
  let U := labelledOpening r G
  have h1 := captured_labelled_advance q Z hq hqc
  have h2 := captured_labelled_advance r Y hr hrc
  have h3 := captured_labelled_advance s T hs hsc
  have h4 := captured_labelled_advance r G hr hret
  have hb1 := mul_le_mul_of_nonneg_right hfastq h1.1.le
  have hb2 := mul_le_mul_of_nonneg_right hfastr h2.1.le
  have hb3 := mul_le_mul_of_nonneg_right hps h3.1.le
  have hb4 := mul_le_mul_of_nonneg_right hfastr h4.1.le
  have hUZ : 0 ≤ U-Z := by linarith only [h1.1,h2.1,h3.1,h4.1]
  have hlo := mul_nonneg hp.le hUZ
  change (M : ℝ)+1/8 ≤ p*U ∧ p*U<(M : ℝ)+7/8
  constructor <;> nlinarith only [hown,hlo,h1.2,h2.2,h3.2,h4.2,hb1,hb2,hb3,hb4]

theorem local_displacement (d p q r s V : ℝ)
    (hd : 0<d) (hp : 0<p) (hq : 0<q) (hr : 0<r) (hs : 0<s)
    (hfastp : 8*d ≤ p) (hfastq : 32*d ≤ q) (hfastr : 24*d ≤ r) (hfasts : 8*d ≤ s)
    (hpc : InWay p (V+1/(8*d)))
    (hqc : InWay q (labelledOpening p (V+1/(8*d))))
    (hrc : InWay r (labelledOpening q (labelledOpening p (V+1/(8*d)))))
    (hsc : InWay s (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d))))))
    (hret : InWay r (labelledOpening s (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d))))))) :
    0<labelledOpening r (labelledOpening s (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d))))))-V ∧
      d*(labelledOpening r (labelledOpening s (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d))))))-V)<83/384 := by
  let W := V+1/(8*d)
  let Z := labelledOpening p W
  let Y := labelledOpening q Z
  let T := labelledOpening r Y
  let G := labelledOpening s T
  let U := labelledOpening r G
  have h0 := captured_labelled_advance p W hp hpc
  have h1 := captured_labelled_advance q Z hq hqc
  have h2 := captured_labelled_advance r Y hr hrc
  have h3 := captured_labelled_advance s T hs hsc
  have h4 := captured_labelled_advance r G hr hret
  have hb0 := mul_le_mul_of_nonneg_right hfastp h0.1.le
  have hb1 := mul_le_mul_of_nonneg_right hfastq h1.1.le
  have hb2 := mul_le_mul_of_nonneg_right hfastr h2.1.le
  have hb3 := mul_le_mul_of_nonneg_right hfasts h3.1.le
  have hb4 := mul_le_mul_of_nonneg_right hfastr h4.1.le
  have hstep : 0<1/(8*d) := by positivity
  have hid : d*(1/(8*d))=1/8 := by field_simp
  change 0<U-V ∧ d*(U-V)<83/384
  change 0<Z-W ∧ p*(Z-W)<1/4 at h0
  change 8*d*(Z-W) ≤ p*(Z-W) at hb0
  dsimp [W] at h0 hb0
  constructor <;> nlinarith only [h0.1,h1.1,h2.1,h3.1,h4.1,hstep,hid,h0.2,h1.2,h2.2,h3.2,h4.2,hb0,hb1,hb2,hb3,hb4]

#print axioms minimum_window
#print axioms local_displacement
end Fresh.NativeRecoveredSecondTail
