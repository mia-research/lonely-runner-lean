import Fresh.NativePacketExtremeRecovery

/-! A supplied speed band of native phase span at most 3/4 has at most one
captured-label block. Its captured readers form a speed-order segment; the
slowest captured reader sets the next opening when outsiders are clear.
Clear members, including old packet members, retain their re-entry duties.
This is a local arrangement reduction, never a global time or move bound. -/
namespace Fresh.NativeNarrowCaptureBlock
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeCurrentLabelPacket Fresh.NativeRecapturedLabelReset
  Fresh.NativePacketExtremeRecovery Fresh.NativeReturnClosingOrder Fresh.NativeCanonicalReturn
  Fresh.FastestCaptureRetention

theorem separation_in_band (p s d q R : ℝ) (hR : 0 ≤ R)
    (hps : p ≤ s) (hsq : s ≤ q) (hpd : p ≤ d) (hdq : d ≤ q) :
    |(s-d)*R| ≤ (q-p)*R := by
  rw [abs_le]
  have hleft := mul_le_mul_of_nonneg_right (by linarith : d-s ≤ q-p) hR
  have hright := mul_le_mul_of_nonneg_right (by linarith : s-d ≤ q-p) hR
  constructor <;> nlinarith only [hleft,hright]

theorem band_captured_labels_equal (p s d q R : ℝ) (hR : 0 ≤ R)
    (hps : p ≤ s) (hsq : s ≤ q) (hpd : p ≤ d) (hdq : d ≤ q)
    (hspan : (q-p)*R ≤ 3/4) (hs : InWay s R) (hd : InWay d R) :
    label (s*R)=label (d*R) :=
  capture_labels_equal_of_close s d R hs hd
    ((separation_in_band p s d q R hR hps hsq hpd hdq).trans hspan)

theorem captured_between_same_label (p s q R : ℝ) (hR : 0 ≤ R)
    (hps : p ≤ s) (hsq : s ≤ q) (hp : InWay p R) (hq : InWay q R)
    (hl : label (p*R)=label (q*R)) : InWay s R ∧ label (s*R)=label (p*R) := by
  have hlo := (capture_at_label p R hp).1
  have hhi := (capture_at_label q R hq).2
  rw [←hl] at hhi
  have hlower := mul_le_mul_of_nonneg_right hps hR
  have hupper := mul_le_mul_of_nonneg_right hsq hR
  have hb : (label (p*R) : ℝ)-1/8 < s*R ∧ s*R < (label (p*R) : ℝ)+1/8 := by
    constructor <;> linarith only [hlo,hhi,hlower,hupper]
  have hn : |s*R-(label (p*R) : ℝ)| < 1/8 := by
    rw [abs_lt]
    constructor <;> linarith only [hb.1,hb.2]
  exact ⟨lt_of_le_of_lt (Fresh.Cascade.distInt_le _ _) hn,(entry_iff_label s R _).1 (Or.inr hb)⟩

theorem captured_block_convex (p s q R : ℝ) (hR : 0 ≤ R)
    (hps : p ≤ s) (hsq : s ≤ q) (hspan : (q-p)*R ≤ 3/4)
    (hp : InWay p R) (hq : InWay q R) : InWay s R := by
  have he := band_captured_labels_equal p p q q R hR le_rfl (hps.trans hsq)
    (hps.trans hsq) le_rfl hspan hp hq
  exact (captured_between_same_label p s q R hR hps hsq hp hq he).1

theorem hidden_middle_requires_span (p s q R : ℝ) (hR : 0 ≤ R)
    (hps : p ≤ s) (hsq : s ≤ q) (hp : ¬InWay p R) (hq : ¬InWay q R)
    (hs : InWay s R) : 1/4 ≤ (q-p)*R := by
  apply le_of_not_gt
  intro hsmall
  have hsign : (p-q)*R ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hR
  have hclose : |(p-q)*R| < 1/4 := by
    rw [abs_of_nonpos hsign]
    nlinarith only [hsmall]
  exact (clear_between_close_extremes p s q R hR hps hsq hp hq hclose).1 hs

theorem capture_pair_dichotomy (s d R : ℝ) (hs : InWay s R) (hd : InWay d R) :
    (label (s*R)=label (d*R) ∧ |(s-d)*R| < 1/4) ∨
      (label (s*R)≠label (d*R) ∧ 3/4 < |(s-d)*R|) := by
  by_cases he : label (s*R)=label (d*R)
  · exact Or.inl ⟨he,same_label_capture_spread s d R hs hd he⟩
  · refine Or.inr ⟨he,?_⟩
    exact lt_of_not_ge (fun hn=>he (capture_labels_equal_of_close s d R hs hd hn))

-- A geometric band plus a supplied minimum of its captured segment. The
-- existence lemma below derives that minimum from any nonempty capture set.
-- STANDING: DEFINITION
noncomputable def Frame (v : Fin 8 → ℝ) (k : Fin 8) (R : ℝ)
    (I : Finset (Fin 8)) (p q : ℝ) (g : Fin 8) : Prop :=
  0 < R ∧ I ⊆ Finset.univ.erase k ∧ g∈I ∧ InWay (reading v k g) R ∧
    0 < label (reading v k g*R) ∧
    (∀ i∈I, p ≤ reading v k i ∧ reading v k i ≤ q) ∧ (q-p)*R ≤ 3/4 ∧
    (∀ i : Fin 8, i≠k → InWay (reading v k i) R → i∈I) ∧
    (∀ i∈I, InWay (reading v k i) R → reading v k g ≤ reading v k i)

theorem frame_packet {v : Fin 8 → ℝ} (_hv : IsArrangement v) (k : Fin 8)
    (R : ℝ) (I : Finset (Fin 8)) (p q : ℝ) (g : Fin 8) (h : Frame v k R I p q g) :
    Packet v k R g := by
  obtain ⟨hR,hI,hg,hwg,hN,hbounds,hspan,hinside,hmin⟩ := h
  refine same_label_packet (Finset.mem_erase.mp (hI hg)).1 hwg hN ?_
  intro i hi hw
  have him := hinside i hi hw
  exact band_captured_labels_equal p _ _ q R hR.le (hbounds i him).1 (hbounds i him).2
    (hbounds g hg).1 (hbounds g hg).2 hspan hw hwg

theorem frame_move {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (R : ℝ) (I : Finset (Fin 8)) (p q : ℝ) (g : Fin 8) (h : Frame v k R I p q g) :
    IsMove (disparitySet v k) R (handoffOpening v k R g) := by
  obtain ⟨hR,hI,hg,hwg,hN,hbounds,hspan,hinside,hmin⟩ := h
  apply same_label_minimum_move hv k g R (Finset.mem_erase.mp (hI hg)).1 hwg hN
  · intro i hi hw
    have him := hinside i hi hw
    exact band_captured_labels_equal p _ _ q R hR.le (hbounds i him).1 (hbounds i him).2
      (hbounds g hg).1 (hbounds g hg).2 hspan hw hwg
  · intro i hi hw
    exact hmin i (hinside i hi hw) hw

theorem exists_frame {v : Fin 8 → ℝ} (_hv : IsArrangement v) (k : Fin 8)
    (R : ℝ) (I : Finset (Fin 8)) (p q : ℝ) (hR : 0 < R)
    (hI : I ⊆ Finset.univ.erase k)
    (hbounds : ∀ i∈I, p ≤ reading v k i ∧ reading v k i ≤ q)
    (hspan : (q-p)*R ≤ 3/4)
    (hinside : ∀ i : Fin 8, i≠k → InWay (reading v k i) R → i∈I)
    (b : Fin 8) (hb : b∈I) (hwb : InWay (reading v k b) R)
    (hN : 0 < label (reading v k b*R)) : ∃ g : Fin 8, Frame v k R I p q g := by
  classical
  let C := I.filter (fun i=>InWay (reading v k i) R)
  have hbc : b∈C := Finset.mem_filter.mpr ⟨hb,hwb⟩
  obtain ⟨g,hgc,hmin⟩ := Finset.exists_min_image C (reading v k) ⟨b,hbc⟩
  have hg := (Finset.mem_filter.mp hgc).1
  have hwg := (Finset.mem_filter.mp hgc).2
  have he := band_captured_labels_equal p _ _ q R hR.le (hbounds g hg).1 (hbounds g hg).2
    (hbounds b hb).1 (hbounds b hb).2 hspan hwg hwb
  refine ⟨g,hR,hI,hg,hwg,?_,hbounds,hspan,hinside,?_⟩
  · rw [he]; exact hN
  · intro i hi hw
    exact hmin i (Finset.mem_filter.mpr ⟨hi,hw⟩)

theorem frame_next_capture_fresh {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (R : ℝ) (I : Finset (Fin 8)) (p q : ℝ) (g : Fin 8) (h : Frame v k R I p q g)
    (i : Fin 8) (hi : i≠k) (hw : InWay (reading v k i) (handoffOpening v k R g)) :
    ¬InWay (reading v k i) R :=
  packet_capture_outside hv k g R h.1 (frame_packet hv k R I p q g h) (frame_move hv k R I p q g h) i hi hw

theorem later_capture_label_barrier (g s R T : ℝ) (hs : 0 ≤ s) (hRT : R ≤ T)
    (hwg : InWay g R) (hgap : (g-s)*R ≤ 3/4) (hws : InWay s T) :
    label (g*R) ≤ label (s*T) := by
  have hglo := (capture_at_label g R hwg).1
  have hshi := (capture_at_label s T hws).2
  have hinc := mul_le_mul_of_nonneg_left hRT hs
  by_contra hn
  have hi : label (s*T)+1 ≤ label (g*R) := by omega
  have hr : (label (s*T) : ℝ)+1 ≤ (label (g*R) : ℝ) := by exact_mod_cast hi
  nlinarith only [hglo,hshi,hgap,hinc,hr]

theorem opening_capture_ratio (g s T : ℝ) (N : ℤ) (hT : 0 < T) (hN : 0 < N)
    (ho : g*T=(N : ℝ)+1/8) (hws : InWay s T) (hlabel : N ≤ label (s*T)) :
    7*g < 9*s := by
  have hlo := (capture_at_label s T hws).1
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hLreal : (N : ℝ) ≤ (label (s*T) : ℝ) := by exact_mod_cast hlabel
  have hx : 7*(g*T) < 9*(s*T) := by linarith only [hlo,hNreal,hLreal,ho]
  nlinarith only [hx,hT]

theorem frame_next_member_ratio {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (R : ℝ) (I : Finset (Fin 8)) (p q : ℝ) (g : Fin 8) (h : Frame v k R I p q g)
    (j : Fin 8) (hj : j∈I) (hwj : InWay (reading v k j) (handoffOpening v k R g)) :
    7*reading v k g < 9*reading v k j := by
  have hm := frame_move hv k R I p q g h
  obtain ⟨hR,hI,hg,hwg,hN,hbounds,hspan,hinside,hmin⟩ := h
  have hRT := le_of_isMove (disparitySet_pos hv k) hm
  have hgap : (reading v k g-reading v k j)*R ≤ 3/4 := by
    have hh := mul_le_mul_of_nonneg_right (show reading v k g-reading v k j ≤ q-p by
      linarith only [(hbounds g hg).2,(hbounds j hj).1]) hR.le
    exact hh.trans hspan
  have hl := later_capture_label_barrier _ _ R _ (abs_nonneg _) hRT hwg hgap hwj
  exact opening_capture_ratio _ _ _ _ (hR.trans_le hRT) hN
    (handoff_identity hv k g R (Finset.mem_erase.mp (hI hg)).1) hwj hl

theorem frame_two_zero {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (R : ℝ) (I : Finset (Fin 8)) (p q : ℝ) (g : Fin 8) (h : Frame v k R I p q g)
    (j : Fin 8) (hj : j∈I) (hwj : InWay (reading v k j) (handoffOpening v k R g))
    (hm2 : IsMove (disparitySet v k) (handoffOpening v k R g)
      (handoffOpening v k (handoffOpening v k R g) j))
    (i : Fin 8) (hi : i≠k) (hwi : InWay (reading v k i) R) :
    advance (reading v k i) R (handoffOpening v k R g)=0 ∧
      advance (reading v k i) (handoffOpening v k R g) (handoffOpening v k (handoffOpening v k R g) j)=0 := by
  have hm := frame_move hv k R I p q g h
  have hp := frame_packet hv k R I p q g h
  have hgj := frame_next_member_ratio hv k R I p q g h j hj hwj
  obtain ⟨hR,hI,hg,hwg,hN,hbounds,hspan,hinside,hmin⟩ := h
  have him := hinside i hi hwi
  have he := band_captured_labels_equal p _ _ q R hR.le (hbounds i him).1 (hbounds i him).2
    (hbounds g hg).1 (hbounds g hg).2 hspan hwi hwg
  have hig := Fresh.NativeWitnessPacketReentry.common_positive_label_sharp _ _ R hR hwi hwg he hN
  have hgk : g≠k := (Finset.mem_erase.mp (hI hg)).1
  have hjk : j≠k := (Finset.mem_erase.mp (hI hj)).1
  have hgp : 0 < reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hgk,rfl⟩)
  have hjp : 0 < reading v k j := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨j,hjk,rfl⟩)
  have hcomb : 49*reading v k i < 81*reading v k j := by linarith only [hig,hgj]
  have ha := mul_lt_mul_of_pos_right hig hjp
  have hb := mul_lt_mul_of_pos_right hcomb hgp
  have hprod := mul_pos hgp hjp
  have hface : reading v k i*(reading v k g+reading v k j) ≤ 3*reading v k g*reading v k j := by
    nlinarith only [ha,hb,hprod]
  exact Fresh.NativeTwoSetterPacket.two_setter_zero_split hv k R g j i hgk hjk hi hwg hm hwj hm2 hwi hface

theorem frame_two_capture_fresh {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (R : ℝ) (I : Finset (Fin 8)) (p q : ℝ) (g : Fin 8) (h : Frame v k R I p q g)
    (j : Fin 8) (hj : j∈I) (hwj : InWay (reading v k j) (handoffOpening v k R g))
    (hm2 : IsMove (disparitySet v k) (handoffOpening v k R g)
      (handoffOpening v k (handoffOpening v k R g) j))
    (i : Fin 8) (hi : i≠k)
    (hafter : InWay (reading v k i) (handoffOpening v k (handoffOpening v k R g) j)) :
    ¬InWay (reading v k i) R := by
  intro hw
  have hz := (frame_two_zero hv k R I p q g h j hj hwj hm2 i hi hw).2
  exact not_lt_of_ge (nonreturning_clear hv k _ _ hm2 i hi hz) hafter

-- STANDING: DEFINITION
noncomputable def RetainedBandClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (R : ℝ) (I : Finset (Fin 8)) (p q : ℝ) (g : Fin 8),
    Frame v k R I p q g ∧ ∀ i : Fin 8, i≠k → ¬InWay (reading v k i) R →
      handoffOpening v k R g ≤ closing (reading v k i) R

theorem retained_into_current {v : Fin 8 → ℝ} {k : Fin 8}
    (h : RetainedBandClass v k) : Fresh.NativeCurrentLabelPacket.RetainedClass v k := by
  obtain ⟨hv,R,I,p,q,g,hf,hclose⟩ := h
  exact ⟨hv,R,g,hf.1,frame_packet hv k R I p q g hf,frame_move hv k R I p q g hf,hclose⟩

-- STANDING: DEFINITION
noncomputable def RecoveredBandClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (R : ℝ) (I : Finset (Fin 8)) (p q : ℝ) (g : Fin 8),
    Frame v k R I p q g ∧ ∀ i : Fin 8, i≠k → ¬InWay (reading v k i) R →
      0 < advance (reading v k i) R (handoffOpening v k R g) →
      reading v k g*((label (reading v k i*handoffOpening v k R g) : ℝ)+1/8) ≤
        reading v k i*((label (reading v k g*R) : ℝ)+1/8)

theorem recovered_into_current {v : Fin 8 → ℝ} {k : Fin 8}
    (h : RecoveredBandClass v k) : Fresh.NativeCurrentLabelPacket.RecoveredClass v k := by
  obtain ⟨hv,R,I,p,q,g,hf,hpassed⟩ := h
  exact ⟨hv,R,g,hf.1,frame_packet hv k R I p q g hf,frame_move hv k R I p q g hf,hpassed⟩

theorem retained_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : RetainedBandClass v k) : Isolation v k :=
  Fresh.NativeCurrentLabelPacket.retained_isolation (retained_into_current h)

theorem recovered_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : RecoveredBandClass v k) : Isolation v k :=
  Fresh.NativeCurrentLabelPacket.recovered_isolation (recovered_into_current h)

#print axioms retained_into_current
#print axioms recovered_into_current
#print axioms retained_isolation
#print axioms recovered_isolation

#print axioms later_capture_label_barrier
#print axioms opening_capture_ratio
#print axioms frame_next_member_ratio
#print axioms frame_two_zero
#print axioms frame_two_capture_fresh

#print axioms separation_in_band
#print axioms band_captured_labels_equal
#print axioms captured_between_same_label
#print axioms captured_block_convex
#print axioms hidden_middle_requires_span
#print axioms capture_pair_dichotomy
#print axioms frame_packet
#print axioms frame_move
#print axioms exists_frame
#print axioms frame_next_capture_fresh
end Fresh.NativeNarrowCaptureBlock
