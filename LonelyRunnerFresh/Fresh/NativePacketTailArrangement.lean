import Fresh.NativePacketTailRetention

/-! Retained old packets and newly captured packets share one pair endpoint.
Original physical reader indices are kept; only remaining readers retain
endpoint recovery duties. Earlier watcher resets derive this input. -/
open Classical
namespace Fresh.NativePacketTailArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeOpeningReversal Fresh.NativeOpeningReversalArrangement Fresh.NativeThirdReaderRetention
  Fresh.NativeFixedPrefixArrangement Fresh.NativeFixedPrefixTransport Fresh.NativePacketTailRetention
  Fresh.NativeWatcherPacketReturn

-- STANDING: DEFINITION
noncomputable def Entry (v : Fin 8 → ℝ) (k a c : Fin 8) (E : ℝ) (N : ℤ) : Prop :=
  IsArrangement v ∧ a≠k ∧ c≠k ∧ a≠c ∧ 0<E ∧ reading v k a*E=(N : ℝ)+1/8 ∧ InWay (reading v k c) E

noncomputable def RetainedPacket (v : Fin 8 → ℝ) (k a c : Fin 8) (E : ℝ) (I : Finset (Fin 8)) : Prop :=
  I ⊆ Finset.univ.erase k ∧ ∀ i∈I,¬InWay (reading v k i) E ∧ retentionFace (reading v k a) (reading v k c) (reading v k i) E

-- STANDING: DEFINITION
noncomputable def RecoveryClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (a c : Fin 8) (E : ℝ) (N : ℤ) (I : Finset (Fin 8)), Entry v k a c E N ∧ RetainedPacket v k a c E I ∧
    ∀ i : Fin 8,i≠k → i≠a → i≠c → i∉I → ¬InWay (reading v k i) (partnerEnd (reading v k a) (reading v k c) E)

theorem recovery_into_pair {v : Fin 8 → ℝ} {k : Fin 8} (h : RecoveryClass v k) : PairRecoveryClass v k := by
  obtain ⟨a,c,E,N,I,he,hp,hother⟩ := h
  obtain ⟨hv,ha,hc,hac,hE,ho,hw⟩ := he
  have hap : 0<reading v k a := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hcp : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc,rfl⟩)
  refine ⟨hv,a,c,E,N,ha,hc,hac,hE,ho,hw,?_⟩
  intro s hs
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hs
  have hik : i≠k := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hi).1).1
  have hia : i≠a := by intro hh; subst i; exact (Finset.mem_sdiff.mp hi).2 (by simp)
  have hic : i≠c := by intro hh; subst i; exact (Finset.mem_sdiff.mp hi).2 (by simp)
  by_cases hI : i∈I
  · have hip : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hik,rfl⟩)
    have hEP := pair_end_after _ _ E hap hcp N ho hw
    exact (retained_by_face _ _ _ E _ N hap hcp hip ho hw (hp.2 i hI).1 (hp.2 i hI).2 hEP.le le_rfl).1
  · exact hother i hik hia hic hI

theorem recovery_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : RecoveryClass v k) : Isolation v k :=
  pairRecovery_isolation (recovery_into_pair h)

-- STANDING: DEFINITION
noncomputable def TwoPacketGuardClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (a c : Fin 8) (E : ℝ) (N : ℤ) (I : Finset (Fin 8)), Entry v k a c E N ∧ RetainedPacket v k a c E I ∧
    ∀ i : Fin 8,i≠k → i≠a → i≠c → i∉I →
      (¬InWay (reading v k i) E ∧ partnerEnd (reading v k a) (reading v k c) E ≤ closing (reading v k i) E) ∨
      (InWay (reading v k i) E ∧ labelledOpening (reading v k i) E ≤ labelledOpening (reading v k c) E ∧
        reading v k i*(reading v k a+reading v k c) ≤ 3*reading v k a*reading v k c)

theorem twoPacketGuard_into_recovery {v : Fin 8 → ℝ} {k : Fin 8} (h : TwoPacketGuardClass v k) : RecoveryClass v k := by
  obtain ⟨a,c,E,N,I,he,hp,hother⟩ := h
  have heSaved := he
  obtain ⟨hv,ha,hc,hac,hE,ho,hw⟩ := he
  have hap : 0<reading v k a := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hcp : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc,rfl⟩)
  have hEP := pair_end_after _ _ E hap hcp N ho hw
  refine ⟨a,c,E,N,I,heSaved,hp,?_⟩
  intro i hi hia hic hI
  have hip : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  rcases hother i hi hia hic hI with hclear|hcap
  · have hlo := le_of_not_gt (fun hh=>hclear.1 ((inWay_iff_lower_not_passed _ _).2 hh))
    have hu := (le_div_iff₀ hip).1 hclear.2
    have hu' : reading v k i*partnerEnd (reading v k a) (reading v k c) E ≤
        (label (reading v k i*E) : ℝ)+7/8 := by simpa only [closing,mul_comm] using hu
    exact (band_at_point _ E _ _ _ hip.le hEP.le le_rfl hlo hu').1
  · have hh := captured_pair_packet _ _ _ E hap hcp hip hw hcap.1 hcap.2.1 hcap.2.2
    exact not_lt.mpr (clear_of_window _ hh.1 hh.2.le)

-- STANDING: DEFINITION
noncomputable def PostResetClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (d g c : Fin 8) (R : ℝ), Fresh.NativeWatcherReturnArrangement.Entry v k d g R ∧
    Fresh.NativeWatcherReturnArrangement.BoundaryPacket v k d g R ∧ c≠k ∧
    InWay (reading v k c) (returnOpening (reading v k d) (reading v k g) R) ∧
    (∀ i : Fin 8,i≠k → InWay (reading v k i) R →
      retentionFace (reading v k d) (reading v k c) (reading v k i) (returnOpening (reading v k d) (reading v k g) R)) ∧
    (∀ i : Fin 8,i≠k → i≠d → i≠c → ¬InWay (reading v k i) R →
      ¬InWay (reading v k i) (partnerEnd (reading v k d) (reading v k c) (returnOpening (reading v k d) (reading v k g) R)))

theorem postReset_into_recovery {v : Fin 8 → ℝ} {k : Fin 8} (h : PostResetClass v k) : RecoveryClass v k := by
  obtain ⟨d,g,c,R,he,hb,hc,hwc,hfaces,hother⟩ := h
  have heSaved := he
  have horigin := Fresh.NativeWatcherReturnArrangement.boundary_new_capture_outside_packet he hb c hc hwc
  obtain ⟨hv,hd,hg,hdg,hR,hclear,hw,hret,horder⟩ := he
  have hdp : 0<reading v k d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨d,hd,rfl⟩)
  have hgp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have ht := two_opening_displacement _ _ R hdp hgp hw hret
  have hT : 0<returnOpening (reading v k d) (reading v k g) R := by linarith only [hR,ht.1,ht.2.1]
  let I := Finset.univ.filter (fun i : Fin 8=>i≠k ∧ InWay (reading v k i) R)
  refine ⟨d,c,returnOpening (reading v k d) (reading v k g) R,label (reading v k d*labelledOpening (reading v k g) R),I,
    ⟨hv,hd,hc,Ne.symm horigin.1,hT,labelled_opening_identity _ _ hdp,hwc⟩,⟨?_,?_⟩,?_⟩
  · intro i hi
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hi).2.1,Finset.mem_univ _⟩
  · intro i hi
    have hm := (Finset.mem_filter.mp hi).2
    exact ⟨(Fresh.NativeWatcherReturnArrangement.boundary_packet_retained heSaved hb i hm.1 hm.2 _ ht.2.1.le le_rfl).1,
      hfaces i hm.1 hm.2⟩
  · intro i hi hid hic hI
    have hn : ¬InWay (reading v k i) R := by
      intro hh
      exact hI (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,hh⟩)
    exact hother i hi hid hic hn

#print axioms recovery_into_pair
#print axioms recovery_isolation
#print axioms twoPacketGuard_into_recovery
#print axioms postReset_into_recovery
end Fresh.NativePacketTailArrangement
