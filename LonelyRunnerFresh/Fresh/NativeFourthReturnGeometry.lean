import Fresh.NativeUpperTripleArrangement
import Fresh.NativePhaseOriginArrangement
import Fresh.NativePacketTailRetention

/-! Origin-relative levels force a previous own-clear reader's two-opening
face through a fourth-reader reversal. Labels and advances stay unbounded. -/
namespace Fresh.NativeFourthReturnGeometry
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeUpperGridPacket
  Fresh.NativePhaseOriginLevels Fresh.FastestCaptureRetention

theorem own_level_compact (r s W T t : ℝ) (M N : ℤ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hWT : W ≤ T) (ht : 0<t) (ht' : t<1/4)
    (hrW : r*W=(M : ℝ)-1/8+t) (hsW : s*W=(N : ℝ)-1/8+t)
    (hown : r*T=(label (r*T) : ℝ)+1/8) (hcap : InWay s T)
    (hlevel : advance r W T<2*advance s W T) : r<2*s := by
  have hl := (phase_capture_label r W t M ht ht' hrW).1
  have hi := advance_identity r W T hr hWT
  rw [hl] at hi
  have hiR : (label (r*T) : ℝ)=(M : ℝ)+(advance r W T : ℝ) := by exact_mod_cast hi
  rw [hiR] at hown
  have hsT := (displacement s W T t N hs hWT ht ht' hsW hcap).1
  have hn : advance r W T+1 ≤ 2*advance s W T := by omega
  have hnR : (advance r W T : ℝ)+1 ≤ 2*(advance s W T : ℝ) := by exact_mod_cast hn
  by_contra hh
  have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hh) (sub_nonneg.mpr hWT)
  nlinarith only [hown,hrW,hsT,hnR,hm,ht']

theorem ordered_reversal_fast (q s T : ℝ) (hq : 0<q) (hs : 0<s)
    (hqc : InWay q T) (hsc : InWay s T)
    (horder : labelledOpening q T ≤ labelledOpening s T)
    (hret : InWay q (labelledOpening s T)) : 3*s<q := by
  let F := labelledOpening q T
  let G := labelledOpening s T
  have hTF := (captured_labelled_advance q T hq hqc).1
  have hstrict : F<G := by
    apply lt_of_le_of_ne horder
    intro he
    have ho := labelled_opening_identity q T hq
    have hc := clear_of_window (label (q*T)) ho.ge (by linarith only [ho])
    rw [←he] at hret
    exact not_lt_of_ge hc hret
  have hsF : InWay s F := by
    apply inWay_until_opening hs hsc (by linarith only [hTF])
    rw [captured_opening s T hsc]
    exact hstrict
  have hsrecord := Fresh.NativePacketTailRetention.opening_record_until_opening s T F hs
    (by linarith only [hTF]) horder
  have hsG := labelled_opening_identity s F hs
  rw [hsrecord] at hsG
  exact recapture_forces_three q s F G (label (q*T)) (label (s*F)) hq hs
    (labelled_opening_identity q T hq) hsF hsG rfl hret

theorem level_forces_mixed (q r s W T t : ℝ) (M N : ℤ) (hq : 0<q) (hr : 0<r) (hs : 0<s)
    (hWT : W ≤ T) (ht : 0<t) (ht' : t<1/4)
    (hrW : r*W=(M : ℝ)-1/8+t) (hsW : s*W=(N : ℝ)-1/8+t)
    (hown : r*T=(label (r*T) : ℝ)+1/8) (hsc : InWay s T)
    (hlevel : advance r W T<2*advance s W T) (hfast : 3*s<q) :
    r*(s+q) ≤ 3*s*q := by
  have hsmall := own_level_compact r s W T t M N hr.le hs.le hWT ht ht' hrW hsW hown hsc hlevel
  have h1 := mul_lt_mul_of_pos_right hsmall (add_pos hs hq)
  have h2 := mul_lt_mul_of_pos_left hfast hs
  nlinarith only [h1,h2,mul_pos hs hq]

theorem returned_three_clear (q r s W T t : ℝ) (M N : ℤ) (hq : 0<q) (hr : 0<r) (hs : 0<s)
    (hWT : W ≤ T) (ht : 0<t) (ht' : t<1/4)
    (hrW : r*W=(M : ℝ)-1/8+t) (hsW : s*W=(N : ℝ)-1/8+t)
    (hown : r*T=(label (r*T) : ℝ)+1/8)
    (hqc : InWay q T) (hsc : InWay s T)
    (horder : labelledOpening q T ≤ labelledOpening s T)
    (hret : InWay q (labelledOpening s T))
    (hlevel : advance r W T<2*advance s W T) :
    LonelyAt ({q,r,s} : Finset ℝ) (labelledOpening q (labelledOpening s T)) := by
  have hfast := ordered_reversal_fast q s T hq hs hqc hsc horder hret
  have hfit := level_forces_mixed q r s W T t M N hq hr hs hWT ht ht' hrW hsW hown hsc hlevel hfast
  have hrU := Fresh.NativeClearWindowRebound.own_two_window s q r T (label (r*T)) hs hq hr hown hsc hret hfit
  have hsG := labelled_opening_identity s T hs
  have hqU := labelled_opening_identity q (labelledOpening s T) hq
  have hsU := own_opening_retained q s (labelledOpening s T) _ _ (label (s*T)) hq hs.le
    (by linarith only [hfast,hq]) hsG hret hqU rfl
  intro a ha
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with he|he|he
  · subst a; exact clear_of_window _ hqU.ge (by linarith only [hqU])
  · subst a; exact clear_of_window _ hrU.1 hrU.2.le
  · subst a; exact clear_of_window _ hsU.1 hsU.2.le

theorem old_third_forced_gap (q r s T : ℝ) (hq : 0<q) (hr : 0<r) (hs : 0<s)
    (hown : r*T=(label (r*T) : ℝ)+1/8) (hsc : InWay s T)
    (hret : InWay q (labelledOpening s T)) (hfast : 3*s<q)
    (hrret : InWay r (labelledOpening q (labelledOpening s T))) : 9*s<4*r := by
  have hfailed : 3*s*q<r*(s+q) := by
    apply lt_of_not_ge
    intro hf
    have hw := Fresh.NativeClearWindowRebound.own_two_window s q r T (label (r*T)) hs hq hr hown hsc hret hf
    exact not_lt_of_ge (clear_of_window _ hw.1 hw.2.le) hrret
  by_contra hn
  have hbound := mul_le_mul_of_nonneg_right (le_of_not_gt hn) (add_pos hs hq).le
  have hsq := mul_lt_mul_of_pos_left hfast hs
  nlinarith only [hfailed,hbound,hsq]

#print axioms old_third_forced_gap

-- STANDING: DEFINITION
noncomputable def fourthEnd (q r s Z : ℝ) : ℝ :=
  labelledOpening q (labelledOpening s (labelledOpening r (labelledOpening q Z)))

theorem minimum_window (p q r s Z : ℝ) (M : ℤ)
    (hp : 0<p) (hq : 0<q) (hr : 0<r) (hs : 0<s)
    (hfast : 4*p ≤ q) (hpr : p ≤ r) (hps : p ≤ s)
    (hown : p*Z=(M : ℝ)+1/8) (hqc : InWay q Z)
    (hrc : InWay r (labelledOpening q Z))
    (hsc : InWay s (labelledOpening r (labelledOpening q Z)))
    (hret : InWay q (labelledOpening s (labelledOpening r (labelledOpening q Z)))) :
    (M : ℝ)+1/8 ≤ p*fourthEnd q r s Z ∧ p*fourthEnd q r s Z<(M : ℝ)+7/8 := by
  let Y := labelledOpening q Z
  let T := labelledOpening r Y
  let G := labelledOpening s T
  let U := labelledOpening q G
  have h1 := captured_labelled_advance q Z hq hqc
  have h2 := captured_labelled_advance r Y hr hrc
  have h3 := captured_labelled_advance s T hs hsc
  have h4 := captured_labelled_advance q G hq hret
  have hb1 := mul_le_mul_of_nonneg_right hfast h1.1.le
  have hb2 := mul_le_mul_of_nonneg_right hpr h2.1.le
  have hb3 := mul_le_mul_of_nonneg_right hps h3.1.le
  have hb4 := mul_le_mul_of_nonneg_right hfast h4.1.le
  have hUZ : 0 ≤ U-Z := by linarith only [h1.1,h2.1,h3.1,h4.1]
  have hlo := mul_nonneg hp.le hUZ
  change (M : ℝ)+1/8 ≤ p*U ∧ p*U<(M : ℝ)+7/8
  constructor <;> nlinarith only [hown,hlo,h1.2,h2.2,h3.2,h4.2,hb1,hb2,hb3,hb4]

theorem local_displacement (d p q r s V : ℝ)
    (hd : 0<d) (hp : 0<p) (hq : 0<q) (hr : 0<r) (hs : 0<s)
    (hfastp : 8*d ≤ p) (hfastq : 32*d ≤ q) (hfastr : 8*d ≤ r) (hfasts : 8*d ≤ s)
    (hpc : InWay p (V+1/(8*d)))
    (hqc : InWay q (labelledOpening p (V+1/(8*d))))
    (hrc : InWay r (labelledOpening q (labelledOpening p (V+1/(8*d)))))
    (hsc : InWay s (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d))))))
    (hret : InWay q (labelledOpening s (labelledOpening r (labelledOpening q (labelledOpening p (V+1/(8*d))))))) :
    0<fourthEnd q r s (labelledOpening p (V+1/(8*d)))-V ∧
      d*(fourthEnd q r s (labelledOpening p (V+1/(8*d)))-V)<15/64 := by
  let W := V+1/(8*d)
  let Z := labelledOpening p W
  let Y := labelledOpening q Z
  let T := labelledOpening r Y
  let G := labelledOpening s T
  let U := labelledOpening q G
  have h0 := captured_labelled_advance p W hp hpc
  have h1 := captured_labelled_advance q Z hq hqc
  have h2 := captured_labelled_advance r Y hr hrc
  have h3 := captured_labelled_advance s T hs hsc
  have h4 := captured_labelled_advance q G hq hret
  have hb0 := mul_le_mul_of_nonneg_right hfastp h0.1.le
  have hb1 := mul_le_mul_of_nonneg_right hfastq h1.1.le
  have hb2 := mul_le_mul_of_nonneg_right hfastr h2.1.le
  have hb3 := mul_le_mul_of_nonneg_right hfasts h3.1.le
  have hb4 := mul_le_mul_of_nonneg_right hfastq h4.1.le
  have hstep : 0<1/(8*d) := by positivity
  have hid : d*(1/(8*d))=1/8 := by field_simp
  change 0<U-V ∧ d*(U-V)<15/64
  change 0<Z-W ∧ p*(Z-W)<1/4 at h0
  change 8*d*(Z-W) ≤ p*(Z-W) at hb0
  dsimp [W] at h0 hb0
  constructor <;> nlinarith only [h0.1,h1.1,h2.1,h3.1,h4.1,hstep,hid,h0.2,h1.2,h2.2,h3.2,h4.2,hb0,hb1,hb2,hb3,hb4]

theorem slow_window (d x V U : ℝ) (J : ℤ) (hx : 0 ≤ x)
    (hVU : 0 ≤ U-V) (hlocal : d*(U-V)<15/64) (hspeed : 2*x ≤ d)
    (hlo : (J : ℝ)+1/8 ≤ x*V) (hhi : x*V ≤ (J : ℝ)+3/4) :
    (J : ℝ)+1/8 ≤ x*U ∧ x*U<(J : ℝ)+7/8 := by
  have h1 := mul_le_mul_of_nonneg_right hspeed hVU
  have h2 := mul_nonneg hx hVU
  constructor <;> nlinarith only [hlo,hhi,h1,h2,hlocal]

#print axioms minimum_window
#print axioms local_displacement
#print axioms slow_window
#print axioms own_level_compact
#print axioms ordered_reversal_fast
#print axioms level_forces_mixed
#print axioms returned_three_clear
end Fresh.NativeFourthReturnGeometry
