import Fresh.NativeComparablePair

/-! Actual first/fourth openings and the compact current pair tail force
an exact quarter displacement. This is a local native fragment; strict
capture boundaries retain the closed initial slower-reader windows. -/
namespace Fresh.NativeComparableFourthTail
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.FastestCaptureRetention

theorem prefix_displacement (d p q r V : ℝ) (hd : 0<d) (hp : 0<p) (hq : 0<q) (hr : 0<r)
    (hfastp : 8*d ≤ p) (hfastq : 32*d ≤ q) (hfastr : 32*d ≤ 3*r)
    (hpc : InWay p (V+1/(8*d))) (hqc : InWay q (labelledOpening p (V+1/(8*d))))
    (hrc : InWay r (labelledOpening q (labelledOpening p (V+1/(8*d))))) :
    0<labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d))))-V ∧
      d*(labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d))))-V)<3/16 := by
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
  change 0<T-V ∧ d*(T-V)<3/16
  change 0<Z-W ∧ p*(Z-W)<1/4 at h0
  change 8*d*(Z-W) ≤ p*(Z-W) at hb0
  dsimp [W] at h0 hb0
  constructor <;> nlinarith only [h0.1,h1.1,h2.1,hstep,hid,h0.2,h1.2,h2.2,hb0,hb1,hb2]

theorem minimum_window (p q r s Z F : ℝ) (M : ℤ)
    (hp : 0<p) (hq : 0<q) (hr : 0<r) (hs : 0<s)
    (hfastq : 4*p ≤ q) (hfastr : 4*p ≤ 3*r) (hps : p ≤ s)
    (hown : p*Z=(M : ℝ)+1/8) (hqc : InWay q Z)
    (hrc : InWay r (labelledOpening q Z))
    (hsc : InWay s (labelledOpening r (labelledOpening q Z)))
    (hGF : labelledOpening s (labelledOpening r (labelledOpening q Z)) ≤ F)
    (hpair : F-labelledOpening s (labelledOpening r (labelledOpening q Z))<1/(4*q)+1/(4*r)) :
    (M : ℝ)+1/8 ≤ p*F ∧ p*F<(M : ℝ)+7/8 := by
  let Y := labelledOpening q Z
  let T := labelledOpening r Y
  let G := labelledOpening s T
  have h1 := captured_labelled_advance q Z hq hqc
  have h2 := captured_labelled_advance r Y hr hrc
  have h3 := captured_labelled_advance s T hs hsc
  have hscaled := mul_lt_mul_of_pos_left hpair hp
  have hiq : p/(4*q) ≤ 1/16 := by
    apply (div_le_iff₀ (by positivity : 0<4*q)).2
    nlinarith only [hfastq]
  have hir : p/(4*r) ≤ 3/16 := by
    apply (div_le_iff₀ (by positivity : 0<4*r)).2
    nlinarith only [hfastr]
  have htail : p*(F-G)<1/4 := by
    have he : p*(1/(4*q)+1/(4*r))=p/(4*q)+p/(4*r) := by ring
    rw [he] at hscaled
    linarith only [hscaled,hiq,hir]
  have hb1 := mul_le_mul_of_nonneg_right hfastq h1.1.le
  have hb2 := mul_le_mul_of_nonneg_right hfastr h2.1.le
  have hb3 := mul_le_mul_of_nonneg_right hps h3.1.le
  have hFZ : 0 ≤ F-Z := by linarith only [hGF,h1.1,h2.1,h3.1]
  have hlo := mul_nonneg hp.le hFZ
  constructor <;> nlinarith only [hown,hlo,htail,h1.2,h2.2,h3.2,hb1,hb2,hb3]

theorem local_displacement (d p q r s V F : ℝ)
    (hd : 0<d) (hp : 0<p) (hq : 0<q) (hr : 0<r) (hs : 0<s)
    (hfastp : 8*d ≤ p) (hfastq : 32*d ≤ q) (hfastr : 32*d ≤ 3*r) (hfasts : 8*d ≤ s)
    (hpc : InWay p (V+1/(8*d))) (hqc : InWay q (labelledOpening p (V+1/(8*d))))
    (hrc : InWay r (labelledOpening q (labelledOpening p (V+1/(8*d)))))
    (hsc : InWay s (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d))))))
    (hGF : labelledOpening s (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d))))) ≤ F)
    (hpair : F-labelledOpening s (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d)))))<1/(4*q)+1/(4*r)) :
    0<F-V ∧ d*(F-V)<1/4 := by
  let W := V+1/(8*d)
  let Z := labelledOpening p W
  let Y := labelledOpening q Z
  let T := labelledOpening r Y
  let G := labelledOpening s T
  have h0 := captured_labelled_advance p W hp hpc
  have h1 := captured_labelled_advance q Z hq hqc
  have h2 := captured_labelled_advance r Y hr hrc
  have h3 := captured_labelled_advance s T hs hsc
  have hscaled := mul_lt_mul_of_pos_left hpair hd
  have hiq : d/(4*q) ≤ 1/128 := by
    apply (div_le_iff₀ (by positivity : 0<4*q)).2
    nlinarith only [hfastq]
  have hir : d/(4*r) ≤ 3/128 := by
    apply (div_le_iff₀ (by positivity : 0<4*r)).2
    nlinarith only [hfastr]
  have htail : d*(F-G)<1/32 := by
    have he : d*(1/(4*q)+1/(4*r))=d/(4*q)+d/(4*r) := by ring
    rw [he] at hscaled
    linarith only [hscaled,hiq,hir]
  have hb0 := mul_le_mul_of_nonneg_right hfastp h0.1.le
  have hb1 := mul_le_mul_of_nonneg_right hfastq h1.1.le
  have hb2 := mul_le_mul_of_nonneg_right hfastr h2.1.le
  have hb3 := mul_le_mul_of_nonneg_right hfasts h3.1.le
  have hstep : 0<1/(8*d) := by positivity
  have hid : d*(1/(8*d))=1/8 := by field_simp
  change 0<Z-W ∧ p*(Z-W)<1/4 at h0
  change 8*d*(Z-W) ≤ p*(Z-W) at hb0
  dsimp [W] at h0 hb0
  constructor <;> nlinarith only [hGF,h0.1,h1.1,h2.1,h3.1,hstep,hid,htail,h0.2,h1.2,h2.2,h3.2,hb0,hb1,hb2,hb3]

theorem slow_quarter_window (d x V F : ℝ) (J : ℤ) (hx : 0 ≤ x)
    (hVF : 0 ≤ F-V) (hdis : d*(F-V)<1/4) (hspeed : 2*x ≤ d)
    (hlo : (J : ℝ)+1/8 ≤ x*V) (hhi : x*V ≤ (J : ℝ)+3/4) :
    (J : ℝ)+1/8 ≤ x*F ∧ x*F<(J : ℝ)+7/8 := by
  have h1 := mul_le_mul_of_nonneg_right hspeed hVF
  have h2 := mul_nonneg hx hVF
  constructor <;> nlinarith only [hlo,hhi,h1,h2,hdis]

#print axioms prefix_displacement
#print axioms minimum_window
#print axioms local_displacement
#print axioms slow_quarter_window
end Fresh.NativeComparableFourthTail
