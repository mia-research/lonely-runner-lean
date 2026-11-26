import Fresh.NativeComparableFourthGrid

/-! A fast second reader recaptures the third opening. The fourth reading
is arbitrary above the minimum. Direct clearance and a forced slow-fourth
rebound derive all local minimum and quarter-displacement duties. -/
namespace Fresh.NativeFastSecondResetTail
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeThirdReaderRebound
  Fresh.NativeOutsideGroupDisplacement Fresh.FastestCaptureRetention

theorem minimum_window (p q r s Z : ℝ) (M : ℤ)
    (hp : 0<p) (hq : 0<q) (hr : 0<r) (hs : 0<s)
    (hpq : 4*p ≤ q) (hpr : p ≤ r) (hps : p ≤ s) (hqr : 3*r<q)
    (ho : p*Z=(M : ℝ)+1/8) (hqc : InWay q Z)
    (hrc : InWay r (labelledOpening q Z))
    (hqret : InWay q (labelledOpening r (labelledOpening q Z)))
    (hsc : InWay s (labelledOpening q (labelledOpening r (labelledOpening q Z)))) :
    (M : ℝ)+1/8 ≤ p*forcedEnd q r s (labelledOpening r (labelledOpening q Z)) ∧
      p*forcedEnd q r s (labelledOpening r (labelledOpening q Z))<(M : ℝ)+7/8 := by
  classical
  let Y := labelledOpening q Z
  let T := labelledOpening r Y
  let A := labelledOpening q T
  let F := forcedEnd q r s T
  have h1 := captured_labelled_advance q Z hq hqc
  have h2 := captured_labelled_advance r Y hr hrc
  have h3 := captured_labelled_advance q T hq hqret
  have hS := captured_labelled_advance s A hs hsc
  have ht := forced_tail_displacement q r s T (label (r*Y)) hq hr hs hqr
    (labelled_opening_identity r Y hr) hqret hsc
  have hFA : 0 ≤ F-A := by linarith only [ht.1,hS.1]
  have hFZ : 0 ≤ F-Z := by linarith only [hFA,h1.1,h2.1,h3.1]
  have hlo := mul_nonneg hp.le hFZ
  have hb := mul_le_mul_of_nonneg_right hps hFA
  change (M : ℝ)+1/8 ≤ p*F ∧ p*F<(M : ℝ)+7/8
  by_cases hret : InWay r (thirdEnd q s T)
  · have hslow := recaptured_old_forces_slow_third q r s T (label (r*Y)) hq hr hs hqr
      (labelled_opening_identity r Y hr) hqret hsc hret
    have hqfast : 7*p ≤ q := by linarith only [hslow,hps,hqr]
    have hrfast : 7*p ≤ 3*r := by linarith only [hslow,hps]
    have hb1 := mul_le_mul_of_nonneg_right hqfast h1.1.le
    have hb2 := mul_le_mul_of_nonneg_right hrfast h2.1.le
    have hb3 := mul_le_mul_of_nonneg_right hqfast h3.1.le
    constructor <;> nlinarith only [ho,hlo,hb,ht.2,h1.2,h2.2,h3.2,hb1,hb2,hb3]
  · have heF : F=partnerEnd q s A := by
      change (if InWay r (thirdEnd q s T) then _ else _)=_
      rw [if_neg hret]
      rfl
    have hdir := (direct_tail_displacement q s A (label (q*T)) hq hs
      (labelled_opening_identity q T hq) hsc).2
    rw [←heF] at hdir
    have hb1 := mul_le_mul_of_nonneg_right hpq h1.1.le
    have hb2 := mul_le_mul_of_nonneg_right hpr h2.1.le
    have hb3 := mul_le_mul_of_nonneg_right hpq h3.1.le
    constructor <;> nlinarith only [ho,hlo,hb,hdir,h1.2,h2.2,h3.2,hb1,hb2,hb3]

theorem local_displacement (d p q r s V : ℝ)
    (hd : 0<d) (hp : 0<p) (hq : 0<q) (hr : 0<r) (hs : 0<s)
    (hfastp : 8*d ≤ p) (hfastq : 32*d ≤ q) (hfastr : 8*d ≤ r) (hps : p ≤ s)
    (hqr : 3*r<q) (hpc : InWay p (V+1/(8*d)))
    (hqc : InWay q (labelledOpening p (V+1/(8*d))))
    (hrc : InWay r (labelledOpening q (labelledOpening p (V+1/(8*d)))))
    (hqret : InWay q (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d))))))
    (hsc : InWay s (labelledOpening q (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d))))))) :
    0<forcedEnd q r s (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d)))))-V ∧
      d*(forcedEnd q r s (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d)))))-V)<1/4 := by
  classical
  let W := V+1/(8*d)
  let Z := labelledOpening p W
  let Y := labelledOpening q Z
  let T := labelledOpening r Y
  let A := labelledOpening q T
  let F := forcedEnd q r s T
  have h0 := captured_labelled_advance p W hp hpc
  have h1 := captured_labelled_advance q Z hq hqc
  have h2 := captured_labelled_advance r Y hr hrc
  have h3 := captured_labelled_advance q T hq hqret
  have hS := captured_labelled_advance s A hs hsc
  have ht := forced_tail_displacement q r s T (label (r*Y)) hq hr hs hqr
    (labelled_opening_identity r Y hr) hqret hsc
  have hFA : 0 ≤ F-A := by linarith only [ht.1,hS.1]
  have hfasts : 8*d ≤ s := hfastp.trans hps
  have hb := mul_le_mul_of_nonneg_right hfasts hFA
  have hb0 := mul_le_mul_of_nonneg_right hfastp h0.1.le
  have hstep : 0<1/(8*d) := by positivity
  have hid : d*(1/(8*d))=1/8 := by field_simp
  change 0<F-V ∧ d*(F-V)<1/4
  change 0<Z-W ∧ p*(Z-W)<1/4 at h0
  change 8*d*(Z-W) ≤ p*(Z-W) at hb0
  dsimp [W] at h0 hb0
  by_cases hret : InWay r (thirdEnd q s T)
  · have hslow := recaptured_old_forces_slow_third q r s T (label (r*Y)) hq hr hs hqr
      (labelled_opening_identity r Y hr) hqret hsc hret
    have hqfast : 56*d ≤ q := by linarith only [hslow,hfasts,hqr]
    have hrfast : 56*d ≤ 3*r := by linarith only [hslow,hfasts]
    have hb1 := mul_le_mul_of_nonneg_right hqfast h1.1.le
    have hb2 := mul_le_mul_of_nonneg_right hrfast h2.1.le
    have hb3 := mul_le_mul_of_nonneg_right hqfast h3.1.le
    constructor <;> nlinarith only [hFA,h0.1,h1.1,h2.1,h3.1,hstep,hid,hb,ht.2,h0.2,h1.2,h2.2,h3.2,hb0,hb1,hb2,hb3]
  · have heF : F=partnerEnd q s A := by
      change (if InWay r (thirdEnd q s T) then _ else _)=_
      rw [if_neg hret]
      rfl
    have hdir := (direct_tail_displacement q s A (label (q*T)) hq hs
      (labelled_opening_identity q T hq) hsc).2
    rw [←heF] at hdir
    have hb1 := mul_le_mul_of_nonneg_right hfastq h1.1.le
    have hb2 := mul_le_mul_of_nonneg_right hfastr h2.1.le
    have hb3 := mul_le_mul_of_nonneg_right hfastq h3.1.le
    constructor <;> nlinarith only [hFA,h0.1,h1.1,h2.1,h3.1,hstep,hid,hb,hdir,h0.2,h1.2,h2.2,h3.2,hb0,hb1,hb2,hb3]

theorem reset_minimum_window (p q r Z : ℝ) (M : ℤ)
    (hp : 0<p) (hq : 0<q) (hr : 0<r) (hpq : 4*p ≤ q) (hpr : p ≤ r)
    (ho : p*Z=(M : ℝ)+1/8) (hqc : InWay q Z)
    (hrc : InWay r (labelledOpening q Z))
    (hret : InWay q (labelledOpening r (labelledOpening q Z))) :
    (M : ℝ)+1/8 ≤ p*labelledOpening q (labelledOpening r (labelledOpening q Z)) ∧
      p*labelledOpening q (labelledOpening r (labelledOpening q Z))<(M : ℝ)+1/2 := by
  let Y := labelledOpening q Z
  let T := labelledOpening r Y
  let A := labelledOpening q T
  have h1 := captured_labelled_advance q Z hq hqc
  have h2 := captured_labelled_advance r Y hr hrc
  have h3 := captured_labelled_advance q T hq hret
  have hb1 := mul_le_mul_of_nonneg_right hpq h1.1.le
  have hb2 := mul_le_mul_of_nonneg_right hpr h2.1.le
  have hb3 := mul_le_mul_of_nonneg_right hpq h3.1.le
  have hlo := mul_nonneg hp.le (show 0 ≤ A-Z by linarith only [h1.1,h2.1,h3.1])
  change (M : ℝ)+1/8 ≤ p*A ∧ p*A<(M : ℝ)+1/2
  constructor <;> nlinarith only [ho,hlo,h1.2,h2.2,h3.2,hb1,hb2,hb3]

theorem reset_prefix_displacement (d p q r V : ℝ)
    (hd : 0<d) (hp : 0<p) (hq : 0<q) (hr : 0<r)
    (hfastp : 8*d ≤ p) (hfastq : 32*d ≤ q) (hfastr : 8*d ≤ r)
    (hpc : InWay p (V+1/(8*d))) (hqc : InWay q (labelledOpening p (V+1/(8*d))))
    (hrc : InWay r (labelledOpening q (labelledOpening p (V+1/(8*d)))))
    (hret : InWay q (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d)))))) :
    0<labelledOpening q (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d)))))-V ∧
      d*(labelledOpening q (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d)))))-V)<13/64 := by
  let W := V+1/(8*d)
  let Z := labelledOpening p W
  let Y := labelledOpening q Z
  let T := labelledOpening r Y
  let A := labelledOpening q T
  have h0 := captured_labelled_advance p W hp hpc
  have h1 := captured_labelled_advance q Z hq hqc
  have h2 := captured_labelled_advance r Y hr hrc
  have h3 := captured_labelled_advance q T hq hret
  have hb0 := mul_le_mul_of_nonneg_right hfastp h0.1.le
  have hb1 := mul_le_mul_of_nonneg_right hfastq h1.1.le
  have hb2 := mul_le_mul_of_nonneg_right hfastr h2.1.le
  have hb3 := mul_le_mul_of_nonneg_right hfastq h3.1.le
  have hstep : 0<1/(8*d) := by positivity
  have hid : d*(1/(8*d))=1/8 := by field_simp
  change 0<A-V ∧ d*(A-V)<13/64
  change 0<Z-W ∧ p*(Z-W)<1/4 at h0
  change 8*d*(Z-W) ≤ p*(Z-W) at hb0
  dsimp [W] at h0 hb0
  constructor <;> nlinarith only [h0.1,h1.1,h2.1,h3.1,hstep,hid,h0.2,h1.2,h2.2,h3.2,hb0,hb1,hb2,hb3]

theorem third_prefix_displacement (d p q r V : ℝ)
    (hd : 0<d) (hp : 0<p) (hq : 0<q) (hr : 0<r)
    (hfastp : 8*d ≤ p) (hfastq : 32*d ≤ q) (hfastr : 8*d ≤ r)
    (hpc : InWay p (V+1/(8*d))) (hqc : InWay q (labelledOpening p (V+1/(8*d))))
    (hrc : InWay r (labelledOpening q (labelledOpening p (V+1/(8*d))))) :
    0<labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d))))-V ∧
      d*(labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d))))-V)<25/128 := by
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
  change 0<T-V ∧ d*(T-V)<25/128
  change 0<Z-W ∧ p*(Z-W)<1/4 at h0
  change 8*d*(Z-W) ≤ p*(Z-W) at hb0
  dsimp [W] at h0 hb0
  constructor <;> nlinarith only [h0.1,h1.1,h2.1,hstep,hid,h0.2,h1.2,h2.2,hb0,hb1,hb2]

theorem fourth_prefix_minimum (p q r s Z : ℝ) (M : ℤ)
    (hp : 0<p) (hq : 0<q) (hr : 0<r) (hs : 0<s)
    (hpq : 4*p ≤ q) (hpr : p ≤ r) (hps : p ≤ s)
    (ho : p*Z=(M : ℝ)+1/8) (hqc : InWay q Z)
    (hrc : InWay r (labelledOpening q Z))
    (hsc : InWay s (labelledOpening r (labelledOpening q Z))) :
    (M : ℝ)+1/8 ≤ p*labelledOpening s (labelledOpening r (labelledOpening q Z)) ∧
      p*labelledOpening s (labelledOpening r (labelledOpening q Z))<(M : ℝ)+7/8 := by
  let Y := labelledOpening q Z
  let T := labelledOpening r Y
  let G := labelledOpening s T
  have h1 := captured_labelled_advance q Z hq hqc
  have h2 := captured_labelled_advance r Y hr hrc
  have h3 := captured_labelled_advance s T hs hsc
  have hb1 := mul_le_mul_of_nonneg_right hpq h1.1.le
  have hb2 := mul_le_mul_of_nonneg_right hpr h2.1.le
  have hb3 := mul_le_mul_of_nonneg_right hps h3.1.le
  have hlo := mul_nonneg hp.le (show 0 ≤ G-Z by linarith only [h1.1,h2.1,h3.1])
  change (M : ℝ)+1/8 ≤ p*G ∧ p*G<(M : ℝ)+7/8
  constructor <;> nlinarith only [ho,hlo,h1.2,h2.2,h3.2,hb1,hb2,hb3]

theorem fourth_prefix_displacement (d p q r s V : ℝ)
    (hd : 0<d) (hp : 0<p) (hq : 0<q) (hr : 0<r) (hs : 0<s)
    (hfastp : 8*d ≤ p) (hfastq : 32*d ≤ q) (hfastr : 8*d ≤ r) (hfasts : 8*d ≤ s)
    (hpc : InWay p (V+1/(8*d))) (hqc : InWay q (labelledOpening p (V+1/(8*d))))
    (hrc : InWay r (labelledOpening q (labelledOpening p (V+1/(8*d)))))
    (hsc : InWay s (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d)))))) :
    0<labelledOpening s (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d)))))-V ∧
      d*(labelledOpening s (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d)))))-V)<29/128 := by
  let W := V+1/(8*d)
  let Z := labelledOpening p W
  let Y := labelledOpening q Z
  let T := labelledOpening r Y
  let G := labelledOpening s T
  have hpre := third_prefix_displacement d p q r V hd hp hq hr hfastp hfastq hfastr hpc hqc hrc
  have h3 := captured_labelled_advance s T hs hsc
  have hb3 := mul_le_mul_of_nonneg_right hfasts h3.1.le
  change 0<G-V ∧ d*(G-V)<29/128
  constructor <;> nlinarith only [hpre.1,hpre.2,h3.1,h3.2,hb3]

#print axioms fourth_prefix_minimum
#print axioms fourth_prefix_displacement

#print axioms reset_minimum_window
#print axioms reset_prefix_displacement
#print axioms third_prefix_displacement

#print axioms minimum_window
#print axioms local_displacement
end Fresh.NativeFastSecondResetTail
