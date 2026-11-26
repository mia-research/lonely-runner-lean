import Fresh.NativeOrderedReturnLevels

/-! Current captured labels force compact speed ratios without a prior move.
The strict integer cone K < 3N includes mixed-label packets and unequal
openings. It is a local reset condition, never a global label bound or descent.
Outsider retention/recovery duties remain explicit. -/
namespace Fresh.NativeCurrentLabelPacket
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels
  Fresh.NativeReturnClosingOrder Fresh.NativeReturnHandoff Fresh.NativeReturnSurvivors Fresh.NativeReturnLevelClearance
  Fresh.NativeCapturedPartnerJoin Fresh.NativeCanonicalReturn

theorem captured_label_compact (s d R : ℝ) (hR : 0 < R)
    (hs : InWay s R) (hd : InWay d R)
    (hl : label (s*R) < 3*label (d*R)) : s < 3*d := by
  have hu := (capture_at_label s R hs).2
  have hlo := (capture_at_label d R hd).1
  have hi : label (s*R)+1 ≤ 3*label (d*R) := by omega
  have hr : (label (s*R) : ℝ)+1 ≤ 3*(label (d*R) : ℝ) := by exact_mod_cast hi
  by_contra hn
  have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hR.le
  nlinarith only [hu,hlo,hr,hm]

-- STANDING: DEFINITION
noncomputable def Packet (v : Fin 8 → ℝ) (k : Fin 8) (R : ℝ) (g : Fin 8) : Prop :=
  g≠k ∧ InWay (reading v k g) R ∧
    ∀ i : Fin 8, i≠k → InWay (reading v k i) R →
      label (reading v k i*R) < 3*label (reading v k g*R)

theorem packet_positive_label {v : Fin 8 → ℝ} {k g : Fin 8} {R : ℝ}
    (h : Packet v k R g) : 0 < label (reading v k g*R) := by
  have hh := h.2.2 g h.1 h.2.1
  omega

theorem same_label_packet {v : Fin 8 → ℝ} {k g : Fin 8} {R : ℝ}
    (hg : g≠k) (hw : InWay (reading v k g) R)
    (hn : 0 < label (reading v k g*R))
    (hs : ∀ i : Fin 8, i≠k → InWay (reading v k i) R →
      label (reading v k i*R)=label (reading v k g*R)) : Packet v k R g := by
  refine ⟨hg,hw,?_⟩
  intro i hi hwi
  rw [hs i hi hwi]
  omega

theorem packet_member_zero {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k g : Fin 8) (R : ℝ) (hR : 0 < R) (h : Packet v k R g)
    (hm : IsMove (disparitySet v k) R (handoffOpening v k R g))
    (i : Fin 8) (hi : i≠k) (hw : InWay (reading v k i) R) :
    advance (reading v k i) R (handoffOpening v k R g)=0 := by
  exact captured_ratio_zero hv k R i g hi h.1 hw h.2.1
    (captured_label_compact _ _ R hR hw h.2.1 (h.2.2 i hi hw)).le hm

theorem packet_capture_outside {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k g : Fin 8) (R : ℝ) (hR : 0 < R) (h : Packet v k R g)
    (hm : IsMove (disparitySet v k) R (handoffOpening v k R g))
    (i : Fin 8) (hi : i≠k) (hw : InWay (reading v k i) (handoffOpening v k R g)) :
    ¬InWay (reading v k i) R := by
  intro hold
  exact not_lt_of_ge (nonreturning_clear hv k R _ hm i hi
    (packet_member_zero hv k g R hR h hm i hi hold)) hw

theorem recaptured_label_floor {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k g : Fin 8) (R : ℝ) (hR : 0 < R) (hg : g≠k)
    (hwg : InWay (reading v k g) R)
    (hm : IsMove (disparitySet v k) R (handoffOpening v k R g))
    (i : Fin 8) (hi : i≠k) (hwi : InWay (reading v k i) R)
    (ha : InWay (reading v k i) (handoffOpening v k R g)) :
    3*label (reading v k g*R) ≤ label (reading v k i*R) := by
  apply le_of_not_gt
  intro hl
  have hz := captured_ratio_zero hv k R i g hi hg hwi hwg
    (captured_label_compact _ _ R hR hwi hwg hl).le hm
  exact not_lt_of_ge (nonreturning_clear hv k R _ hm i hi hz) ha

-- STANDING: DEFINITION
noncomputable def RetainedClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (R : ℝ) (g : Fin 8), 0 < R ∧ Packet v k R g ∧
    IsMove (disparitySet v k) R (handoffOpening v k R g) ∧
    ∀ i : Fin 8, i≠k → ¬InWay (reading v k i) R →
      handoffOpening v k R g ≤ closing (reading v k i) R

theorem retained_into_partner {v : Fin 8 → ℝ} {k : Fin 8}
    (h : RetainedClass v k) : PartnerClass v k := by
  obtain ⟨hv,R,g,hR,hp,hm,hclose⟩ := h
  refine ⟨hv,R,g,hR,hp.1,hp.2.1,hm,?_⟩
  intro i hi
  exact ⟨fun hw=>Or.inl (captured_label_compact _ _ R hR hw hp.2.1 (hp.2.2 i hi hw)).le,
    hclose i hi⟩

-- STANDING: DEFINITION
noncomputable def RecoveredClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (R : ℝ) (g : Fin 8), 0 < R ∧ Packet v k R g ∧
    IsMove (disparitySet v k) R (handoffOpening v k R g) ∧
    ∀ i : Fin 8, i≠k → ¬InWay (reading v k i) R →
      0 < advance (reading v k i) R (handoffOpening v k R g) →
      reading v k g*((label (reading v k i*handoffOpening v k R g) : ℝ)+1/8) ≤
        reading v k i*((label (reading v k g*R) : ℝ)+1/8)

theorem recovered_into_canonical {v : Fin 8 → ℝ} {k : Fin 8}
    (h : RecoveredClass v k) : CanonicalReturnClass v k := by
  obtain ⟨hv,R,g,hR,hp,hm,hpassed⟩ := h
  have hc := capture_at_label (reading v k g) R hp.2.1
  refine ⟨hv,g,R,label (reading v k g*R),hp.1,hR,hc.1,hc.2,hm,?_⟩
  intro i hi ha
  apply hpassed i hi ?_ ha
  intro hw
  have hz := packet_member_zero hv k g R hR hp hm i hi hw
  change 0 < advance (reading v k i) R (handoffOpening v k R g) at ha
  omega

theorem retained_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : RetainedClass v k) : Isolation v k := partner_isolation (retained_into_partner h)

theorem recovered_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : RecoveredClass v k) : Isolation v k := canonical_isolation (recovered_into_canonical h)

#print axioms captured_label_compact
#print axioms packet_positive_label
#print axioms same_label_packet
#print axioms packet_member_zero
#print axioms packet_capture_outside
#print axioms recaptured_label_floor
#print axioms retained_into_partner
#print axioms recovered_into_canonical
#print axioms retained_isolation
#print axioms recovered_isolation
end Fresh.NativeCurrentLabelPacket
