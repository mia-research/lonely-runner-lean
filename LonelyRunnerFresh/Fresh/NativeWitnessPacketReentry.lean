import Fresh.NativeRecapturedLabelReset
import Fresh.NativeTwoSetterPacket

/-! A positive common-label capture witnesses persistent internal speed
ratios. Later clear intervals, changed labels and re-entry do not erase that
witness. One- and two-selected-opening laws reuse native capture recovery;
these local laws impose no budget on a cascade or its returns. -/
namespace Fresh.NativeWitnessPacketReentry
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnLevelClearance Fresh.NativeCurrentLabelPacket
  Fresh.NativeCapturedPartnerJoin Fresh.NativeCanonicalReturn Fresh.NativeReturnClosingOrder
  Fresh.NativeTwoSetterPacket Fresh.FastestCaptureRetention

theorem common_positive_label_sharp (s d P : ℝ) (hP : 0 < P)
    (hs : InWay s P) (hd : InWay d P) (hl : label (s*P)=label (d*P))
    (hN : 0 < label (d*P)) : 7*s < 9*d := by
  have hu := (capture_at_label s P hs).2
  have hlo := (capture_at_label d P hd).1
  rw [hl] at hu
  have hn : (1 : ℝ) ≤ (label (d*P) : ℝ) := by exact_mod_cast hN
  have hscaled : 7*(s*P) < 9*(d*P) := by linarith only [hu,hlo,hn]
  nlinarith only [hscaled,hP]

-- STANDING: DEFINITION
noncomputable def PacketWitness (v : Fin 8 → ℝ) (k : Fin 8) (P : ℝ) (I : Finset (Fin 8)) : Prop :=
  0 < P ∧ I ⊆ Finset.univ.erase k ∧ ∃ N : ℤ, 0 < N ∧
    ∀ i∈I, InWay (reading v k i) P ∧ label (reading v k i*P)=N

theorem witness_pair_sharp {v : Fin 8 → ℝ} {k : Fin 8} {P : ℝ} {I : Finset (Fin 8)}
    (h : PacketWitness v k P I) {i g : Fin 8} (hi : i∈I) (hg : g∈I) :
    7*reading v k i < 9*reading v k g := by
  obtain ⟨hP,hI,N,hN,hlabels⟩ := h
  have hsi := hlabels i hi
  have hsg := hlabels g hg
  exact common_positive_label_sharp _ _ P hP hsi.1 hsg.1 (hsi.2.trans hsg.2.symm)
    (by rw [hsg.2]; exact hN)

theorem witness_member_zero {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (P R : ℝ) (I : Finset (Fin 8)) (h : PacketWitness v k P I)
    (g : Fin 8) (hg : g∈I) (hwg : InWay (reading v k g) R)
    (hm : IsMove (disparitySet v k) R (handoffOpening v k R g))
    (i : Fin 8) (hi : i∈I) (hwi : InWay (reading v k i) R) :
    advance (reading v k i) R (handoffOpening v k R g)=0 := by
  have hik : i≠k := (Finset.mem_erase.mp (h.2.1 hi)).1
  have hgk : g≠k := (Finset.mem_erase.mp (h.2.1 hg)).1
  have hp : 0 < reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hgk,rfl⟩)
  have hratio := witness_pair_sharp h hi hg
  exact captured_ratio_zero hv k R i g hik hgk hwi hwg (by nlinarith only [hratio,hp]) hm

theorem witness_member_clear {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (P R : ℝ) (I : Finset (Fin 8)) (h : PacketWitness v k P I)
    (g : Fin 8) (hg : g∈I) (hwg : InWay (reading v k g) R)
    (hm : IsMove (disparitySet v k) R (handoffOpening v k R g))
    (i : Fin 8) (hi : i∈I) (hwi : InWay (reading v k i) R) :
    ¬InWay (reading v k i) (handoffOpening v k R g) := by
  have hik : i≠k := (Finset.mem_erase.mp (h.2.1 hi)).1
  exact not_lt.mpr (nonreturning_clear hv k R _ hm i hik
    (witness_member_zero hv k P R I h g hg hwg hm i hi hwi))

theorem witness_two_face {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (P : ℝ) (I : Finset (Fin 8)) (h : PacketWitness v k P I)
    (i g j : Fin 8) (hi : i∈I) (hg : g∈I) (hj : j∈I) :
    reading v k i*(reading v k g+reading v k j) ≤ 3*reading v k g*reading v k j := by
  have hgk : g≠k := (Finset.mem_erase.mp (h.2.1 hg)).1
  have hjk : j≠k := (Finset.mem_erase.mp (h.2.1 hj)).1
  have hd : 0 < reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hgk,rfl⟩)
  have he : 0 < reading v k j := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨j,hjk,rfl⟩)
  have hf := mul_lt_mul_of_pos_right (witness_pair_sharp h hi hg) he
  have hf' := mul_lt_mul_of_pos_right (witness_pair_sharp h hi hj) hd
  have hp := mul_pos hd he
  nlinarith only [hf,hf',hp]

theorem witness_two_zero {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (P R : ℝ) (I : Finset (Fin 8)) (h : PacketWitness v k P I)
    (g j i : Fin 8) (hg : g∈I) (hj : j∈I) (hi : i∈I)
    (hwg : InWay (reading v k g) R)
    (hm1 : IsMove (disparitySet v k) R (handoffOpening v k R g))
    (hwj : InWay (reading v k j) (handoffOpening v k R g))
    (hm2 : IsMove (disparitySet v k) (handoffOpening v k R g) (handoffOpening v k (handoffOpening v k R g) j))
    (hwi : InWay (reading v k i) R) :
    advance (reading v k i) R (handoffOpening v k R g)=0 ∧
      advance (reading v k i) (handoffOpening v k R g) (handoffOpening v k (handoffOpening v k R g) j)=0 := by
  exact two_setter_zero_split hv k R g j i
    (Finset.mem_erase.mp (h.2.1 hg)).1 (Finset.mem_erase.mp (h.2.1 hj)).1
    (Finset.mem_erase.mp (h.2.1 hi)).1 hwg hm1 hwj hm2 hwi (witness_two_face hv k P I h i g j hi hg hj)

theorem witness_two_capture_fresh {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (P R : ℝ) (I : Finset (Fin 8)) (h : PacketWitness v k P I)
    (g j i : Fin 8) (hg : g∈I) (hj : j∈I) (hi : i∈I)
    (hwg : InWay (reading v k g) R)
    (hm1 : IsMove (disparitySet v k) R (handoffOpening v k R g))
    (hwj : InWay (reading v k j) (handoffOpening v k R g))
    (hm2 : IsMove (disparitySet v k) (handoffOpening v k R g) (handoffOpening v k (handoffOpening v k R g) j))
    (hafter : InWay (reading v k i) (handoffOpening v k (handoffOpening v k R g) j)) :
    ¬InWay (reading v k i) R ∧ ¬InWay (reading v k i) (handoffOpening v k R g) := by
  have hik : i≠k := (Finset.mem_erase.mp (h.2.1 hi)).1
  constructor
  · intro hw
    have hz := (witness_two_zero hv k P R I h g j i hg hj hi hwg hm1 hwj hm2 hw).2
    exact not_lt_of_ge (nonreturning_clear hv k _ _ hm2 i hik hz) hafter
  · intro hw
    exact witness_member_clear hv k P _ I h j hj hwj hm2 i hi hw hafter

-- STANDING: DEFINITION
noncomputable def RetainedClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (P R : ℝ) (I : Finset (Fin 8)) (g : Fin 8),
    PacketWitness v k P I ∧ 0 < R ∧ g∈I ∧ InWay (reading v k g) R ∧
    IsMove (disparitySet v k) R (handoffOpening v k R g) ∧
    (∀ i : Fin 8, i≠k → InWay (reading v k i) R →
      i∈I ∨ reading v k i ≤ 3*reading v k g ∨ handoffOpening v k R i=handoffOpening v k R g) ∧
    (∀ i : Fin 8, i≠k → ¬InWay (reading v k i) R → handoffOpening v k R g ≤ closing (reading v k i) R)

theorem retained_into_partner {v : Fin 8 → ℝ} {k : Fin 8} (h : RetainedClass v k) : PartnerClass v k := by
  obtain ⟨hv,P,R,I,g,hwit,hR,hg,hwg,hm,hmask,hclose⟩ := h
  have hgk : g≠k := (Finset.mem_erase.mp (hwit.2.1 hg)).1
  have hp : 0 < reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hgk,rfl⟩)
  refine ⟨hv,R,g,hR,hgk,hwg,hm,?_⟩
  intro i hi
  refine ⟨?_,hclose i hi⟩
  intro hw
  rcases hmask i hi hw with hold|hratio|htie
  · have hh := witness_pair_sharp hwit hold hg
    exact Or.inl (by nlinarith only [hh,hp])
  · exact Or.inl hratio
  · exact Or.inr htie

-- STANDING: DEFINITION
noncomputable def RecoveredClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (P R : ℝ) (I : Finset (Fin 8)) (g : Fin 8),
    PacketWitness v k P I ∧ 0 < R ∧ g∈I ∧ InWay (reading v k g) R ∧
    IsMove (disparitySet v k) R (handoffOpening v k R g) ∧
    (∀ i : Fin 8, i≠k → InWay (reading v k i) R →
      i∈I ∨ reading v k i ≤ 3*reading v k g ∨ handoffOpening v k R i=handoffOpening v k R g) ∧
    (∀ i : Fin 8, i≠k → ¬InWay (reading v k i) R →
      0 < advance (reading v k i) R (handoffOpening v k R g) →
      reading v k g*((label (reading v k i*handoffOpening v k R g) : ℝ)+1/8) ≤
        reading v k i*((label (reading v k g*R) : ℝ)+1/8))

theorem recovered_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : RecoveredClass v k) : CanonicalReturnClass v k := by
  obtain ⟨hv,P,R,I,g,hwit,hR,hg,hwg,hm,hmask,hpassed⟩ := h
  have hgk : g≠k := (Finset.mem_erase.mp (hwit.2.1 hg)).1
  have hc := capture_at_label (reading v k g) R hwg
  refine ⟨hv,g,R,label (reading v k g*R),hgk,hR,hc.1,hc.2,hm,?_⟩
  intro i hi ha
  apply hpassed i hi ?_ ha
  intro hw
  have hz : advance (reading v k i) R (handoffOpening v k R g)=0 := by
    rcases hmask i hi hw with hold|hratio|htie
    · exact witness_member_zero hv k P R I hwit g hg hwg hm i hold hw
    · exact captured_ratio_zero hv k R i g hi hgk hw hwg hratio hm
    · have hid := handoff_identity hv k i R hi
      rw [htie] at hid
      have he := capture_at_label (reading v k i) R hw
      exact selected_advance_zero _ R _ _ he.1 he.2 hid
  change 0 < advance (reading v k i) R (handoffOpening v k R g) at ha
  omega

theorem retained_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : RetainedClass v k) : Isolation v k :=
  partner_isolation (retained_into_partner h)

theorem recovered_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : RecoveredClass v k) : Isolation v k :=
  canonical_isolation (recovered_into_canonical h)

theorem outside_clear_forces_member {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (P R : ℝ) (I : Finset (Fin 8)) (h : PacketWitness v k P I)
    (hcap : ∃ i∈I, InWay (reading v k i) R)
    (hout : ∀ i : Fin 8, i≠k → i∉I → ¬InWay (reading v k i) R) :
    ∃ g : Fin 8, g∈I ∧ InWay (reading v k g) R ∧
      step (disparitySet v k) R=handoffOpening v k R g ∧
      IsMove (disparitySet v k) R (handoffOpening v k R g) ∧
      ∀ i∈I, InWay (reading v k i) R → advance (reading v k i) R (handoffOpening v k R g)=0 := by
  have hm := isMove_step (disparitySet v k) R
  rcases hm with hfix|⟨d,hd,hw,he,hmax⟩
  · obtain ⟨i,hi,hwi⟩ := hcap
    have hik : i≠k := (Finset.mem_erase.mp (h.2.1 hi)).1
    exact (hfix.1 _ (mem_disparitySet.mpr ⟨i,hik,rfl⟩) hwi).elim
  · obtain ⟨g,hgk,rfl⟩ := mem_disparitySet.mp hd
    change InWay (reading v k g) R at hw
    have hg : g∈I := by by_contra hn; exact hout g hgk hn hw
    have heq : step (disparitySet v k) R=handoffOpening v k R g := by
      change _=opening (reading v k g) (label (reading v k g*R))
      exact he.trans (next_at_label _ R hw)
    have hm' : IsMove (disparitySet v k) R (handoffOpening v k R g) := by
      rw [←heq]
      exact isMove_step _ _
    exact ⟨g,hg,hw,heq,hm',fun i hi hwi=>witness_member_zero hv k P R I h g hg hw hm' i hi hwi⟩

theorem outside_relay_forces_member {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (P R : ℝ) (I : Finset (Fin 8)) (h : PacketWitness v k P I)
    (a : Fin 8) (ha : a≠k) (hwa : InWay (reading v k a) R)
    (hm : IsMove (disparitySet v k) R (handoffOpening v k R a))
    (hfaces : ∀ i : Fin 8, i≠k → i∉I →
      (InWay (reading v k i) R → reading v k i ≤ 3*reading v k a ∨ handoffOpening v k R i=handoffOpening v k R a) ∧
      (¬InWay (reading v k i) R → handoffOpening v k R a ≤ closing (reading v k i) R))
    (hcap : ∃ i∈I, InWay (reading v k i) (handoffOpening v k R a)) :
    ∃ g : Fin 8, g∈I ∧ InWay (reading v k g) (handoffOpening v k R a) ∧
      step (disparitySet v k) (handoffOpening v k R a)=handoffOpening v k (handoffOpening v k R a) g ∧
      IsMove (disparitySet v k) (handoffOpening v k R a) (handoffOpening v k (handoffOpening v k R a) g) ∧
      ∀ i∈I, InWay (reading v k i) (handoffOpening v k R a) →
        advance (reading v k i) (handoffOpening v k R a) (handoffOpening v k (handoffOpening v k R a) g)=0 := by
  have hout : ∀ i : Fin 8, i≠k → i∉I → ¬InWay (reading v k i) (handoffOpening v k R a) := by
    intro i hi hn
    have hz : advance (reading v k i) R (handoffOpening v k R a)=0 := by
      by_cases hwi : InWay (reading v k i) R
      · rcases (hfaces i hi hn).1 hwi with hratio|htie
        · exact captured_ratio_zero hv k R i a hi ha hwi hwa hratio hm
        · have hid := handoff_identity hv k i R hi
          rw [htie] at hid
          have hc := capture_at_label (reading v k i) R hwi
          exact selected_advance_zero _ R _ _ hc.1 hc.2 hid
      · have hip : 0 < reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
        apply (zero_iff_original_upper _ R _ hip.le (le_of_isMove (disparitySet_pos hv k) hm)).2
        have hh := (le_div_iff₀ hip).1 ((hfaces i hi hn).2 hwi)
        simpa only [closing,mul_comm] using hh
    exact not_lt.mpr (nonreturning_clear hv k R _ hm i hi hz)
  exact outside_clear_forces_member hv k P _ I h hcap hout

theorem outside_recovered_relay_forces_member {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (P R : ℝ) (I : Finset (Fin 8)) (h : PacketWitness v k P I)
    (a : Fin 8) (ha : a≠k) (hwa : InWay (reading v k a) R)
    (hm : IsMove (disparitySet v k) R (handoffOpening v k R a))
    (hpassed : ∀ i : Fin 8, i≠k → i∉I →
      0 < advance (reading v k i) R (handoffOpening v k R a) →
      reading v k a*((label (reading v k i*handoffOpening v k R a) : ℝ)+1/8) ≤
        reading v k i*((label (reading v k a*R) : ℝ)+1/8))
    (hcap : ∃ i∈I, InWay (reading v k i) (handoffOpening v k R a)) :
    ∃ g : Fin 8, g∈I ∧ InWay (reading v k g) (handoffOpening v k R a) ∧
      step (disparitySet v k) (handoffOpening v k R a)=handoffOpening v k (handoffOpening v k R a) g ∧
      IsMove (disparitySet v k) (handoffOpening v k R a) (handoffOpening v k (handoffOpening v k R a) g) ∧
      ∀ i∈I, InWay (reading v k i) (handoffOpening v k R a) →
        advance (reading v k i) (handoffOpening v k R a) (handoffOpening v k (handoffOpening v k R a) g)=0 := by
  have hout : ∀ i : Fin 8, i≠k → i∉I → ¬InWay (reading v k i) (handoffOpening v k R a) := by
    intro i hi hn hw
    have hc := (crossproduct_capture hv k a ha R _ _ hm (handoff_identity hv k a R ha) i hi).1 hw
    exact not_lt_of_ge (hpassed i hi hn hc.1) hc.2
  exact outside_clear_forces_member hv k P _ I h hcap hout

theorem forced_retained_witness {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (P R : ℝ) (I : Finset (Fin 8)) (h : PacketWitness v k P I) (hR : 0 < R)
    (hcap : ∃ i∈I, InWay (reading v k i) R)
    (hout : ∀ i : Fin 8, i≠k → i∉I → ¬InWay (reading v k i) R)
    (hclose : ∀ i : Fin 8, i≠k → ¬InWay (reading v k i) R →
      step (disparitySet v k) R ≤ closing (reading v k i) R) : RetainedClass v k := by
  obtain ⟨g,hg,hwg,heq,hm,hzero⟩ := outside_clear_forces_member hv k P R I h hcap hout
  refine ⟨hv,P,R,I,g,h,hR,hg,hwg,hm,?_,?_⟩
  · intro i hi hw
    apply Or.inl
    by_contra hn
    exact hout i hi hn hw
  · intro i hi hw
    rw [←heq]
    exact hclose i hi hw

theorem reset_frame_witness {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (P : ℝ) (a g : Fin 8) (h : Fresh.NativeRecapturedLabelReset.Frame v k P a g) :
    ∃ I : Finset (Fin 8), PacketWitness v k P I ∧ g∈I ∧
      ∀ i : Fin 8, i≠k → InWay (reading v k i) (handoffOpening v k P a) →
        i∈I ∨ reading v k i ≤ 3*reading v k g := by
  classical
  obtain ⟨ha,hg,hP,hwa,hN,hm,hwg,hgS,hm2,hmask⟩ := h
  have hf := recaptured_label_floor hv k a P hP ha hwa hm g hg hwg hgS
  have hpositive : 0 < label (reading v k g*P) := by omega
  let I := Finset.univ.filter (fun i : Fin 8=>i≠k ∧ InWay (reading v k i) P ∧
    label (reading v k i*P)=label (reading v k g*P))
  have hI : I ⊆ Finset.univ.erase k := by
    intro i hi
    have hh := (Finset.mem_filter.mp hi).2
    exact Finset.mem_erase.mpr ⟨hh.1,Finset.mem_univ i⟩
  have hgp : g∈I := by simp [I,hg,hwg]
  refine ⟨I,⟨hP,hI,label (reading v k g*P),hpositive,?_⟩,hgp,?_⟩
  · intro i hi
    have hh := (Finset.mem_filter.mp hi).2
    exact hh.2
  · intro i hi hwi
    rcases hmask i hi hwi with hold|hcone
    · exact Or.inl (by simp only [I,Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨hi,hold⟩)
    · have hS := hP.trans_le (le_of_isMove (disparitySet_pos hv k) hm)
      exact Or.inr (captured_label_compact _ _ _ hS hwi hgS hcone).le

theorem old_retainedReset_into_witness {v : Fin 8 → ℝ} {k : Fin 8}
    (h : Fresh.NativeRecapturedLabelReset.RetainedResetClass v k) : RetainedClass v k := by
  obtain ⟨hv,P,a,g,hframe,hclose⟩ := h
  obtain ⟨I,hwit,hg,hmask⟩ := reset_frame_witness hv k P a g hframe
  obtain ⟨ha,hgk,hP,hwa,hN,hm,hwg,hgS,hm2,holdmask⟩ := hframe
  refine ⟨hv,P,handoffOpening v k P a,I,g,hwit,hP.trans_le (le_of_isMove (disparitySet_pos hv k) hm),hg,hgS,hm2,?_,hclose⟩
  intro i hi hw
  rcases hmask i hi hw with hiI|hratio
  · exact Or.inl hiI
  · exact Or.inr (Or.inl hratio)

theorem old_recoveredReset_into_witness {v : Fin 8 → ℝ} {k : Fin 8}
    (h : Fresh.NativeRecapturedLabelReset.RecoveredResetClass v k) : RecoveredClass v k := by
  obtain ⟨hv,P,a,g,hframe,hpassed⟩ := h
  obtain ⟨I,hwit,hg,hmask⟩ := reset_frame_witness hv k P a g hframe
  obtain ⟨ha,hgk,hP,hwa,hN,hm,hwg,hgS,hm2,holdmask⟩ := hframe
  refine ⟨hv,P,handoffOpening v k P a,I,g,hwit,hP.trans_le (le_of_isMove (disparitySet_pos hv k) hm),hg,hgS,hm2,?_,hpassed⟩
  intro i hi hw
  rcases hmask i hi hw with hiI|hratio
  · exact Or.inl hiI
  · exact Or.inr (Or.inl hratio)

#print axioms outside_recovered_relay_forces_member
#print axioms outside_relay_forces_member
#print axioms outside_clear_forces_member
#print axioms forced_retained_witness
#print axioms reset_frame_witness
#print axioms old_retainedReset_into_witness
#print axioms old_recoveredReset_into_witness

#print axioms common_positive_label_sharp
#print axioms witness_pair_sharp
#print axioms witness_member_zero
#print axioms witness_member_clear
#print axioms witness_two_face
#print axioms witness_two_zero
#print axioms witness_two_capture_fresh
#print axioms retained_into_partner
#print axioms recovered_into_canonical
#print axioms retained_isolation
#print axioms recovered_isolation
end Fresh.NativeWitnessPacketReentry
