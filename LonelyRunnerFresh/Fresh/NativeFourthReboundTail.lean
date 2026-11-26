import Fresh.NativeFourthReturnArrangement
import Fresh.NativeSuppliedOpeningTriple

/-! An old third reader returning through the fourth handoff forces
stronger speed separation. Its native pair tail retains the minimum and
slow readers through this fragment; no full-history budget is used. -/
namespace Fresh.NativeFourthReboundTail
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeFourthReturnGeometry
  Fresh.FastestCaptureRetention

theorem rebound_core (q r s G : ℝ) (M : ℤ) (hq : 0<q) (hr : 0<r) (hs : 0<s)
    (hsq : s ≤ q) (hsr : s ≤ r) (hown : s*G=(M : ℝ)+1/8)
    (hqc : InWay q G) (hrc : InWay r (labelledOpening q G)) :
    LonelyAt ({q,r,s} : Finset ℝ) (partnerEnd q r (labelledOpening q G)) := by
  have hf := Fresh.NativeThirdReaderRebound.small_old_fit q s r hq hr hsq hsr
  have hh := triple_clear q s r G M hq hs hr hown hqc hrc hf
  intro x hx
  apply hh x
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx ⊢
  tauto

theorem minimum_window (p q r s Z : ℝ) (M : ℤ)
    (hp : 0<p) (hq : 0<q) (hr : 0<r) (hs : 0<s)
    (hfastq : 27*p ≤ 4*q) (hfastr : 9*p ≤ 4*r) (hps : p ≤ s)
    (hown : p*Z=(M : ℝ)+1/8) (hqc : InWay q Z)
    (hrc : InWay r (labelledOpening q Z))
    (hsc : InWay s (labelledOpening r (labelledOpening q Z)))
    (hret : InWay q (labelledOpening s (labelledOpening r (labelledOpening q Z))))
    (hrret : InWay r (fourthEnd q r s Z)) :
    (M : ℝ)+1/8 ≤ p*partnerEnd q r (fourthEnd q r s Z) ∧
      p*partnerEnd q r (fourthEnd q r s Z)<(M : ℝ)+7/8 := by
  let Y := labelledOpening q Z
  let T := labelledOpening r Y
  let G := labelledOpening s T
  let U := labelledOpening q G
  let F := partnerEnd q r U
  have h1 := captured_labelled_advance q Z hq hqc
  have h2 := captured_labelled_advance r Y hr hrc
  have h3 := captured_labelled_advance s T hs hsc
  have h4 := captured_labelled_advance q G hq hret
  have hafter := pair_end_after q r U hq hr _ (labelled_opening_identity q G hq) hrret
  have hpair := Fresh.NativeSuppliedOpeningTriple.pair_displacement q r U hq hr hrret
  have hscaled := mul_lt_mul_of_pos_left hpair hp
  have hiq : p/(4*q) ≤ 1/27 := by
    apply (div_le_iff₀ (by positivity : 0<4*q)).2
    nlinarith only [hfastq]
  have hir : p/(4*r) ≤ 1/9 := by
    apply (div_le_iff₀ (by positivity : 0<4*r)).2
    nlinarith only [hfastr]
  have htail : p*(F-U)<4/27 := by
    have he : p*(1/(4*q)+1/(4*r))=p/(4*q)+p/(4*r) := by ring
    rw [he] at hscaled
    linarith only [hscaled,hiq,hir]
  have hb1 := mul_le_mul_of_nonneg_right hfastq h1.1.le
  have hb2 := mul_le_mul_of_nonneg_right hfastr h2.1.le
  have hb3 := mul_le_mul_of_nonneg_right hps h3.1.le
  have hb4 := mul_le_mul_of_nonneg_right hfastq h4.1.le
  have hFZ : 0 ≤ F-Z := by linarith only [hafter,h1.1,h2.1,h3.1,h4.1]
  have hlo := mul_nonneg hp.le hFZ
  change (M : ℝ)+1/8 ≤ p*F ∧ p*F<(M : ℝ)+7/8
  constructor <;> nlinarith only [hown,hlo,htail,h1.2,h2.2,h3.2,h4.2,hb1,hb2,hb3,hb4]

theorem local_displacement (d p q r s V : ℝ)
    (hd : 0<d) (hp : 0<p) (hq : 0<q) (hr : 0<r) (hs : 0<s)
    (hfastp : 8*d ≤ p) (hfastq : 54*d ≤ q) (hfastr : 18*d ≤ r) (hfasts : 8*d ≤ s)
    (hpc : InWay p (V+1/(8*d)))
    (hqc : InWay q (labelledOpening p (V+1/(8*d))))
    (hrc : InWay r (labelledOpening q (labelledOpening p (V+1/(8*d)))))
    (hsc : InWay s (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d))))))
    (hret : InWay q (labelledOpening s (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d)))))))
    (hrret : InWay r (fourthEnd q r s (labelledOpening p (V+1/(8*d))))) :
    0<partnerEnd q r (fourthEnd q r s (labelledOpening p (V+1/(8*d))))-V ∧
      d*(partnerEnd q r (fourthEnd q r s (labelledOpening p (V+1/(8*d))))-V)<11/48 := by
  let W := V+1/(8*d)
  let Z := labelledOpening p W
  let Y := labelledOpening q Z
  let T := labelledOpening r Y
  let G := labelledOpening s T
  let U := labelledOpening q G
  let F := partnerEnd q r U
  have h0 := captured_labelled_advance p W hp hpc
  have h1 := captured_labelled_advance q Z hq hqc
  have h2 := captured_labelled_advance r Y hr hrc
  have h3 := captured_labelled_advance s T hs hsc
  have h4 := captured_labelled_advance q G hq hret
  have hafter := pair_end_after q r U hq hr _ (labelled_opening_identity q G hq) hrret
  have hpair := Fresh.NativeSuppliedOpeningTriple.pair_displacement q r U hq hr hrret
  have hscaled := mul_lt_mul_of_pos_left hpair hd
  have hiq : d/(4*q) ≤ 1/216 := by
    apply (div_le_iff₀ (by positivity : 0<4*q)).2
    nlinarith only [hfastq]
  have hir : d/(4*r) ≤ 1/72 := by
    apply (div_le_iff₀ (by positivity : 0<4*r)).2
    nlinarith only [hfastr]
  have htail : d*(F-U)<1/54 := by
    have he : d*(1/(4*q)+1/(4*r))=d/(4*q)+d/(4*r) := by ring
    rw [he] at hscaled
    linarith only [hscaled,hiq,hir]
  have hb0 := mul_le_mul_of_nonneg_right hfastp h0.1.le
  have hb1 := mul_le_mul_of_nonneg_right hfastq h1.1.le
  have hb2 := mul_le_mul_of_nonneg_right hfastr h2.1.le
  have hb3 := mul_le_mul_of_nonneg_right hfasts h3.1.le
  have hb4 := mul_le_mul_of_nonneg_right hfastq h4.1.le
  have hstep : 0<1/(8*d) := by positivity
  have hid : d*(1/(8*d))=1/8 := by field_simp
  change 0<F-V ∧ d*(F-V)<11/48
  change 0<Z-W ∧ p*(Z-W)<1/4 at h0
  change 8*d*(Z-W) ≤ p*(Z-W) at hb0
  dsimp [W] at h0 hb0
  constructor <;> nlinarith only [hafter,h0.1,h1.1,h2.1,h3.1,h4.1,hstep,hid,htail,h0.2,h1.2,h2.2,h3.2,h4.2,hb0,hb1,hb2,hb3,hb4]

#print axioms rebound_core
#print axioms minimum_window
#print axioms local_displacement
end Fresh.NativeFourthReboundTail
