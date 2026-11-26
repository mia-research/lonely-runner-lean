import Fresh.NativeNarrowCaptureBlock

/-! A current common-label group transported through a positive-label own
opening has one possible recaptured speed segment. Clear extreme readers can
still surround a captured middle. This is a local boundary comparison. -/
namespace Fresh.NativeMixedGroupTransport
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels
  Fresh.NativeReturnHandoff Fresh.NativeReturnSurvivors Fresh.NativeRecapturedLabelReset
  Fresh.NativeNarrowCaptureBlock Fresh.NativePacketExtremeRecovery
  Fresh.FastestCaptureRetention

theorem transported_capture_span (p q R T : ℝ) (hR : 0 < R) (hT : 0 ≤ T)
    (hrel : 7*T < 9*R) (hp : InWay p R) (hq : InWay q R)
    (hl : label (p*R)=label (q*R)) : |(p-q)*T| < 9/28 := by
  have hs := same_label_capture_spread p q R hp hq hl
  rw [abs_mul,abs_of_pos hR] at hs
  have hm := mul_le_mul_of_nonneg_left hrel.le (abs_nonneg (p-q))
  rw [abs_mul,abs_of_nonneg hT]
  nlinarith only [hs,hm]

theorem nearby_label_diameter (p q T : ℝ) (hc : |(p-q)*T| < 1) :
    label (p*T) ≤ label (q*T)+1 ∧ label (q*T) ≤ label (p*T)+1 := by
  have hp := (entry_interval p T _).1 (label_entry p T)
  have hq := (entry_interval q T _).1 (label_entry q T)
  have hh := abs_lt.mp hc
  constructor
  · by_contra hn
    have hi : label (q*T)+2 ≤ label (p*T) := by omega
    have hr : (label (q*T) : ℝ)+2 ≤ (label (p*T) : ℝ) := by exact_mod_cast hi
    nlinarith only [hp.1,hq.2,hh.2,hr]
  · by_contra hn
    have hi : label (p*T)+2 ≤ label (q*T) := by omega
    have hr : (label (p*T) : ℝ)+2 ≤ (label (q*T) : ℝ) := by exact_mod_cast hi
    nlinarith only [hq.1,hp.2,hh.1,hr]

theorem transported_label_diameter (p q R T : ℝ) (hR : 0 < R) (hT : 0 ≤ T)
    (hrel : 7*T < 9*R) (hp : InWay p R) (hq : InWay q R)
    (hl : label (p*R)=label (q*R)) :
    label (p*T) ≤ label (q*T)+1 ∧ label (q*T) ≤ label (p*T)+1 :=
  nearby_label_diameter p q T (lt_trans (transported_capture_span p q R T hR hT hrel hp hq hl) (by norm_num))

theorem transported_recapture_segment (p s q R T : ℝ) (hR : 0 < R) (hT : 0 ≤ T)
    (hrel : 7*T < 9*R) (hps : p ≤ s) (hsq : s ≤ q)
    (hp : InWay p R) (hq : InWay q R) (hl : label (p*R)=label (q*R))
    (hpT : InWay p T) (hqT : InWay q T) :
    InWay s T ∧ label (s*T)=label (p*T) := by
  have hs := transported_capture_span p q R T hR hT hrel hp hq hl
  have he := capture_labels_equal_of_close p q T hpT hqT (by linarith only [hs])
  exact captured_between_same_label p s q T hT hps hsq hpT hqT he

theorem transported_clear_extremes (p s q R T : ℝ) (hR : 0 < R) (hT : 0 ≤ T)
    (hrel : 7*T < 9*R) (hps : p ≤ s) (hsq : s ≤ q)
    (hp : InWay p R) (hq : InWay q R) (hl : label (p*R)=label (q*R))
    (hpT : ¬InWay p T) (hqT : ¬InWay q T) (hsT : InWay s T) :
    1/4 ≤ (q-p)*T ∧ (q-p)*T < 9/28 ∧ label (q*T)=label (p*T)+1 := by
  have hspan := transported_capture_span p q R T hR hT hrel hp hq hl
  have hsign : (p-q)*T ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hT
  rw [abs_of_nonpos hsign] at hspan
  have hd := transported_label_diameter p q R T hR hT hrel hp hq hl
  have horder := label_monotone (mul_le_mul_of_nonneg_right (hps.trans hsq) hT)
  have hne : label (p*T)≠label (q*T) := by
    intro he
    have hlo := le_of_not_gt (fun hn=>hpT ((inWay_iff_lower_not_passed p T).2 hn))
    have hu := ((entry_interval q T _).1 (label_entry q T)).2
    rw [←he] at hu
    have hw := extreme_window p s q T _ hT hps hsq hlo hu
    exact not_lt_of_ge (clear_of_window _ hw.1 hw.2) hsT
  exact ⟨hidden_middle_requires_span p s q T hT hps hsq hpT hqT hsT,
    by nlinarith only [hspan],by omega⟩

theorem handoff_group_span {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k a i j : Fin 8) (R : ℝ) (hR : 0 < R) (ha : a≠k)
    (hwa : InWay (reading v k a) R) (hN : 0 < label (reading v k a*R))
    (hwi : InWay (reading v k i) R) (hwj : InWay (reading v k j) R)
    (hl : label (reading v k i*R)=label (reading v k j*R)) :
    |(reading v k i-reading v k j)*handoffOpening v k R a| < 9/28 := by
  have hap : 0 < reading v k a := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hrel := opening_relative_face _ R _ hap hwa hN (handoff_identity hv k a R ha)
  have hRT : R < handoffOpening v k R a := by
    change R < opening (reading v k a) (label (reading v k a*R))
    rw [←next_at_label _ R hwa]
    exact lt_nextOpening hap hwa
  exact transported_capture_span _ _ R _ hR (hR.le.trans hRT.le) hrel hwi hwj hl

theorem transported_frame {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k a p q b : Fin 8) (R : ℝ) (I : Finset (Fin 8)) (hR : 0 < R)
    (ha : a≠k) (hwa : InWay (reading v k a) R) (hN : 0 < label (reading v k a*R))
    (hI : I ⊆ Finset.univ.erase k) (_hp : p∈I) (hq : q∈I) (hb : b∈I)
    (hwp : InWay (reading v k p) R) (hwq : InWay (reading v k q) R)
    (hl : label (reading v k p*R)=label (reading v k q*R))
    (hP : 0 < label (reading v k p*R))
    (hbounds : ∀ i∈I, reading v k p ≤ reading v k i ∧ reading v k i ≤ reading v k q)
    (hinside : ∀ i : Fin 8, i≠k → InWay (reading v k i) (handoffOpening v k R a) → i∈I)
    (hwb : InWay (reading v k b) (handoffOpening v k R a)) :
    ∃ g : Fin 8, Frame v k (handoffOpening v k R a) I (reading v k p) (reading v k q) g := by
  have hap : 0 < reading v k a := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hRT : R < handoffOpening v k R a := by
    change R < opening (reading v k a) (label (reading v k a*R))
    rw [←next_at_label _ R hwa]
    exact lt_nextOpening hap hwa
  have hT := hR.trans hRT
  have hspan := handoff_group_span hv k a p q R hR ha hwa hN hwp hwq hl
  have hsign : (reading v k p-reading v k q)*handoffOpening v k R a ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith only [(hbounds q hq).1]) hT.le
  rw [abs_of_nonpos hsign] at hspan
  have hbentry := captured_between_same_label _ _ _ R hR.le (hbounds b hb).1
    (hbounds b hb).2 hwp hwq hl
  have hmono := label_monotone (mul_le_mul_of_nonneg_left hRT.le (abs_nonneg (v b-v k)))
  change label (reading v k b*R) ≤ label (reading v k b*handoffOpening v k R a) at hmono
  have hBN : 0 < label (reading v k b*handoffOpening v k R a) := by
    rw [hbentry.2] at hmono
    exact hP.trans_le hmono
  exact exists_frame hv k _ I _ _ hT hI hbounds (by nlinarith only [hspan]) hinside b hb hwb hBN

theorem clear_gap_capture_label (p s q T : ℝ) (hT : 0 ≤ T)
    (hps : p ≤ s) (hsq : s ≤ q) (hp : ¬InWay p T)
    (hs : InWay s T) (hl : label (q*T)=label (p*T)+1) :
    label (s*T)=label (q*T) := by
  have hpbound := le_of_not_gt (fun hn=>hp ((inWay_iff_lower_not_passed p T).2 hn))
  have hsbound := (capture_at_label s T hs).2
  have hlo := label_monotone (mul_le_mul_of_nonneg_right hps hT)
  have hhi := label_monotone (mul_le_mul_of_nonneg_right hsq hT)
  have hprod := mul_le_mul_of_nonneg_right hps hT
  have hne : label (s*T)≠label (p*T) := by
    intro he
    rw [he] at hsbound
    linarith only [hpbound,hsbound,hprod]
  omega

theorem transported_hidden_label (p s q R T : ℝ) (hR : 0 < R) (hT : 0 ≤ T)
    (hrel : 7*T < 9*R) (hps : p ≤ s) (hsq : s ≤ q)
    (hp : InWay p R) (hq : InWay q R) (hl : label (p*R)=label (q*R))
    (hpT : ¬InWay p T) (hqT : ¬InWay q T) (hsT : InWay s T) :
    label (s*T)=label (q*T) := by
  have hx := transported_clear_extremes p s q R T hR hT hrel hps hsq hp hq hl hpT hqT hsT
  exact clear_gap_capture_label p s q T hT hps hsq hpT hsT hx.2.2

#print axioms clear_gap_capture_label
#print axioms transported_hidden_label

#print axioms transported_frame

#print axioms transported_capture_span
#print axioms nearby_label_diameter
#print axioms transported_label_diameter
#print axioms transported_recapture_segment
#print axioms transported_clear_extremes
#print axioms handoff_group_span
end Fresh.NativeMixedGroupTransport
