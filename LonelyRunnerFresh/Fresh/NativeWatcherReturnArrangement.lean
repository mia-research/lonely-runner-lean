import Fresh.NativeWatcherPacketReturn

/-! Whole watcher packets rejoin the residual compact family at a returned
reader's opening. Initial captures are discharged by a mixed disparity face;
only the remaining initially clear readers retain recovery/closing duties. -/
open Classical
namespace Fresh.NativeWatcherReturnArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeOpeningReversal Fresh.NativeThirdReaderRetention Fresh.NativeResidualReturn Fresh.NativeResidualReturnArrangement
  Fresh.NativeFixedPrefixArrangement Fresh.NativeFixedPrefixTransport Fresh.NativeWatcherPacketReturn

-- STANDING: DEFINITION
noncomputable def Entry (v : Fin 8 → ℝ) (k d g : Fin 8) (R : ℝ) : Prop :=
  IsArrangement v ∧ d≠k ∧ g≠k ∧ d≠g ∧ 0<R ∧ ¬InWay (reading v k d) R ∧
    InWay (reading v k g) R ∧ InWay (reading v k d) (labelledOpening (reading v k g) R) ∧
    ∀ i : Fin 8,i≠k → InWay (reading v k i) R →
      labelledOpening (reading v k i) R ≤ labelledOpening (reading v k g) R

noncomputable def MixedPacket (v : Fin 8 → ℝ) (k d g : Fin 8) (R : ℝ) : Prop :=
  ∀ i : Fin 8,i≠k → InWay (reading v k i) R →
    reading v k i*(reading v k d+reading v k g) ≤ 3*reading v k d*reading v k g

theorem entry_move {v : Fin 8 → ℝ} {k d g : Fin 8} {R : ℝ} (he : Entry v k d g R) :
    IsMove (disparitySet v k) R (labelledOpening (reading v k g) R) := by
  obtain ⟨hv,hd,hg,hdg,hR,hclear,hw,hret,horder⟩ := he
  refine Or.inr ⟨reading v k g,mem_disparitySet.mpr ⟨g,hg,rfl⟩,hw,?_,?_⟩
  · exact (captured_opening _ R hw).symm
  · intro s hs hws
    obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hs
    rw [captured_opening _ R hws]
    exact horder i hi hws

theorem packet_retained {v : Fin 8 → ℝ} {k d g : Fin 8} {R : ℝ}
    (he : Entry v k d g R) (hp : MixedPacket v k d g R) (i : Fin 8) (hi : i≠k)
    (hw : InWay (reading v k i) R) (U : ℝ)
    (hSU : labelledOpening (reading v k g) R ≤ U)
    (hUT : U ≤ returnOpening (reading v k d) (reading v k g) R) :
    ¬InWay (reading v k i) U ∧ label (reading v k i*U)=label (reading v k i*R) := by
  obtain ⟨hv,hd,hg,hdg,hR,hclear,hwg,hret,horder⟩ := he
  have hdp : 0<reading v k d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨d,hd,rfl⟩)
  have hgp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have hip : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  exact packet_segment _ _ _ R U hdp hgp hip hwg hret hw (horder i hi hw) (hp i hi hw) hSU hUT

theorem packet_to_entry {v : Fin 8 → ℝ} {k a b c d g : Fin 8} {C : ℝ} {M : ℤ}
    (he : Fresh.NativeOutsideGroupArrangement.Entry v k a b c C M)
    (hp : Fresh.NativeOutsideGroupArrangement.Packet v k a b c C)
    (hd : d≠k) (hg : g≠k)
    (hclear : ¬InWay (reading v k d) (Fresh.NativeThirdReaderRebound.forcedEnd (reading v k a) (reading v k b) (reading v k c) C))
    (hw : InWay (reading v k g) (Fresh.NativeThirdReaderRebound.forcedEnd (reading v k a) (reading v k b) (reading v k c) C))
    (hret : InWay (reading v k d) (labelledOpening (reading v k g)
      (Fresh.NativeThirdReaderRebound.forcedEnd (reading v k a) (reading v k b) (reading v k c) C)))
    (horder : ∀ i : Fin 8,i≠k → InWay (reading v k i)
      (Fresh.NativeThirdReaderRebound.forcedEnd (reading v k a) (reading v k b) (reading v k c) C) →
      labelledOpening (reading v k i) (Fresh.NativeThirdReaderRebound.forcedEnd (reading v k a) (reading v k b) (reading v k c) C) ≤
      labelledOpening (reading v k g) (Fresh.NativeThirdReaderRebound.forcedEnd (reading v k a) (reading v k b) (reading v k c) C)) :
    Entry v k d g (Fresh.NativeThirdReaderRebound.forcedEnd (reading v k a) (reading v k b) (reading v k c) C) ∧
      g≠a ∧ g≠b ∧ ¬InWay (reading v k g) (labelledOpening (reading v k a) C) := by
  have horigin := Fresh.NativeOutsideGroupArrangement.new_capture_is_watcher he hp g hg hw
  obtain ⟨hv,ha,hb,hc,hab,hac,hbc,hC,hgap,ho,hwa,hwc⟩ := he
  have hap : 0<reading v k a := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hbp : 0<reading v k b := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨b,hb,rfl⟩)
  have hcp : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc,rfl⟩)
  have h1 := captured_labelled_advance (reading v k a) C hap hwa
  have h2 := captured_labelled_advance (reading v k c) (labelledOpening (reading v k a) C) hcp hwc
  have h3 := Fresh.NativeOutsideGroupDisplacement.forced_tail_displacement (reading v k a) (reading v k b) (reading v k c) C M hap hbp hcp hgap ho hwa hwc
  have hR : 0<Fresh.NativeThirdReaderRebound.forcedEnd (reading v k a) (reading v k b) (reading v k c) C := by
    linarith only [hC,h1.1,h2.1,h3.1]
  have hdg : d≠g := by intro hh; subst d; exact hclear hw
  exact ⟨⟨hv,hd,hg,hdg,hR,hclear,hw,hret,horder⟩,horigin⟩

-- STANDING: DEFINITION
noncomputable def RecoveryClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (d g : Fin 8) (R : ℝ), Entry v k d g R ∧ MixedPacket v k d g R ∧
    ∀ i : Fin 8,i≠k → i≠d → ¬InWay (reading v k i) R →
      ¬InWay (reading v k i) (returnOpening (reading v k d) (reading v k g) R)

theorem recovery_into_residualCompact {v : Fin 8 → ℝ} {k : Fin 8}
    (h : RecoveryClass v k) : ResidualCompactClass v k := by
  obtain ⟨d,g,R,he,hp,hother⟩ := h
  have heSaved := he
  obtain ⟨hv,hd,hg,hdg,hR,hclear,hw,hret,horder⟩ := he
  have hdp : 0<reading v k d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨d,hd,rfl⟩)
  have hgp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have hsmall := selected_mixed_compact _ _ hgp (hp g hg hw)
  have hST := (two_opening_displacement _ _ R hdp hgp hw hret).2.1
  refine ⟨hv,d,g,R,hd,hg,hdg,hR,hclear,hw,hret,by nlinarith only [hsmall,hdp],?_⟩
  intro s hs
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hs
  have hik : i≠k := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hi).1).1
  have hid : i≠d := by
    intro hh; subst i
    exact (Finset.mem_sdiff.mp hi).2 (by simp)
  change ¬InWay (reading v k i) (returnOpening (reading v k d) (reading v k g) R)
  by_cases hwi : InWay (reading v k i) R
  · exact (packet_retained heSaved hp i hik hwi _ hST.le le_rfl).1
  · exact hother i hik hid hwi

theorem recovery_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : RecoveryClass v k) : Isolation v k :=
  residualRecovery_isolation (residualCompact_into_recovery (recovery_into_residualCompact h))

-- STANDING: DEFINITION
noncomputable def GuardClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (d g : Fin 8) (R : ℝ), Entry v k d g R ∧ MixedPacket v k d g R ∧
    ∀ i : Fin 8,i≠k → i≠d → ¬InWay (reading v k i) R →
      returnOpening (reading v k d) (reading v k g) R ≤ closing (reading v k i) R

theorem guard_into_recovery {v : Fin 8 → ℝ} {k : Fin 8} (h : GuardClass v k) : RecoveryClass v k := by
  obtain ⟨d,g,R,he,hp,hguard⟩ := h
  have hv := he.1
  have hdp : 0<reading v k d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨d,he.2.1,rfl⟩)
  have hgp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,he.2.2.1,rfl⟩)
  have ht := two_opening_displacement (reading v k d) (reading v k g) R hdp hgp he.2.2.2.2.2.2.1 he.2.2.2.2.2.2.2.1
  have hRT := ht.1.le.trans ht.2.1.le
  refine ⟨d,g,R,he,hp,?_⟩
  intro i hi hid hclear
  have hip : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  have hlo := le_of_not_gt (fun hh=>hclear ((inWay_iff_lower_not_passed _ _).2 hh))
  have hu := (le_div_iff₀ hip).1 (hguard i hi hid hclear)
  have hu' : reading v k i*returnOpening (reading v k d) (reading v k g) R ≤
      (label (reading v k i*R) : ℝ)+7/8 := by simpa only [closing,mul_comm] using hu
  exact (band_at_point _ R _ _ _ hip.le hRT le_rfl hlo hu').1

-- STANDING: DEFINITION
noncomputable def MultiReturnClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (d g : Fin 8) (R : ℝ), Entry v k d g R ∧
    2 ≤ advance (reading v k d) R (labelledOpening (reading v k g) R) ∧
    (∀ i : Fin 8,i≠k → InWay (reading v k i) R → 5*reading v k i ≤ 12*reading v k g) ∧
    ∀ i : Fin 8,i≠k → i≠d → ¬InWay (reading v k i) R →
      ¬InWay (reading v k i) (returnOpening (reading v k d) (reading v k g) R)

theorem multiReturn_into_recovery {v : Fin 8 → ℝ} {k : Fin 8} (h : MultiReturnClass v k) : RecoveryClass v k := by
  obtain ⟨d,g,R,he,hm,hstrip,hother⟩ := h
  have heSaved := he
  obtain ⟨hv,hd,hg,hdg,hR,hclear,hw,hret,horder⟩ := he
  have hdp : 0<reading v k d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨d,hd,rfl⟩)
  have hgp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  refine ⟨d,g,R,heSaved,?_,hother⟩
  intro i hi hwi
  exact multi_return_mixed _ _ _ R hdp hgp (abs_nonneg _) hclear hw hret hm (hstrip i hi hwi)

-- STANDING: DEFINITION
noncomputable def EarlyPhaseClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (d g : Fin 8) (R : ℝ), Entry v k d g R ∧ phase (reading v k d) R ≤ 3/4 ∧
    (∀ i : Fin 8,i≠k → InWay (reading v k i) R → reading v k i ≤ reading v k g) ∧
    ∀ i : Fin 8,i≠k → i≠d → ¬InWay (reading v k i) R →
      ¬InWay (reading v k i) (returnOpening (reading v k d) (reading v k g) R)

theorem earlyPhase_into_recovery {v : Fin 8 → ℝ} {k : Fin 8} (h : EarlyPhaseClass v k) : RecoveryClass v k := by
  obtain ⟨d,g,R,he,hearly,hstrip,hother⟩ := h
  have heSaved := he
  obtain ⟨hv,hd,hg,hdg,hR,hclear,hw,hret,horder⟩ := he
  have hdp : 0<reading v k d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨d,hd,rfl⟩)
  have hgp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  refine ⟨d,g,R,heSaved,?_,hother⟩
  intro i hi hwi
  exact early_phase_mixed _ _ _ R hdp hgp hclear hw hret hearly (hstrip i hi hwi)

noncomputable def BoundaryPacket (v : Fin 8 → ℝ) (k d g : Fin 8) (R : ℝ) : Prop :=
  ∀ i : Fin 8,i≠k → InWay (reading v k i) R →
    boundaryFace (reading v k d) (reading v k g) (reading v k i) R

theorem boundary_packet_retained {v : Fin 8 → ℝ} {k d g : Fin 8} {R : ℝ}
    (he : Entry v k d g R) (hp : BoundaryPacket v k d g R) (i : Fin 8) (hi : i≠k)
    (hw : InWay (reading v k i) R) (U : ℝ)
    (hSU : labelledOpening (reading v k g) R ≤ U)
    (hUT : U ≤ returnOpening (reading v k d) (reading v k g) R) :
    ¬InWay (reading v k i) U ∧ label (reading v k i*U)=label (reading v k i*R) := by
  obtain ⟨hv,hd,hg,hdg,hR,hclear,hwg,hret,horder⟩ := he
  have hdp : 0<reading v k d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨d,hd,rfl⟩)
  have hgp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have hip : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  exact boundary_packet_segment _ _ _ R U hdp hgp hip hwg hret (horder i hi hw) (hp i hi hw) hSU hUT

-- STANDING: DEFINITION
noncomputable def BoundaryRecoveryClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (d g : Fin 8) (R : ℝ), Entry v k d g R ∧ BoundaryPacket v k d g R ∧
    ∀ i : Fin 8,i≠k → i≠d → ¬InWay (reading v k i) R →
      ¬InWay (reading v k i) (returnOpening (reading v k d) (reading v k g) R)

theorem boundaryRecovery_into_residualCompact {v : Fin 8 → ℝ} {k : Fin 8}
    (h : BoundaryRecoveryClass v k) : ResidualCompactClass v k := by
  obtain ⟨d,g,R,he,hp,hother⟩ := h
  have heSaved := he
  obtain ⟨hv,hd,hg,hdg,hR,hclear,hw,hret,horder⟩ := he
  have hdp : 0<reading v k d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨d,hd,rfl⟩)
  have hgp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have hsmall := boundary_selected_compact _ _ R hgp (hp g hg hw)
  have hST := (two_opening_displacement _ _ R hdp hgp hw hret).2.1
  refine ⟨hv,d,g,R,hd,hg,hdg,hR,hclear,hw,hret,hsmall,?_⟩
  intro s hs
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hs
  have hik : i≠k := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hi).1).1
  have hid : i≠d := by
    intro hh; subst i
    exact (Finset.mem_sdiff.mp hi).2 (by simp)
  change ¬InWay (reading v k i) (returnOpening (reading v k d) (reading v k g) R)
  by_cases hwi : InWay (reading v k i) R
  · exact (boundary_packet_retained heSaved hp i hik hwi _ hST.le le_rfl).1
  · exact hother i hik hid hwi

theorem mixedRecovery_into_boundaryRecovery {v : Fin 8 → ℝ} {k : Fin 8}
    (h : RecoveryClass v k) : BoundaryRecoveryClass v k := by
  obtain ⟨d,g,R,he,hp,hother⟩ := h
  have heSaved := he
  obtain ⟨hv,hd,hg,hdg,hR,hclear,hw,hret,horder⟩ := he
  have hdp : 0<reading v k d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨d,hd,rfl⟩)
  have hgp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  refine ⟨d,g,R,heSaved,?_,hother⟩
  intro i hi hwi
  have hip : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  exact mixed_into_boundary _ _ _ R hdp hgp hip hw hwi (hp i hi hwi)

-- STANDING: DEFINITION
noncomputable def BoundaryGuardClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (d g : Fin 8) (R : ℝ), Entry v k d g R ∧ BoundaryPacket v k d g R ∧
    ∀ i : Fin 8,i≠k → i≠d → ¬InWay (reading v k i) R →
      returnOpening (reading v k d) (reading v k g) R ≤ closing (reading v k i) R

theorem boundaryGuard_into_boundaryRecovery {v : Fin 8 → ℝ} {k : Fin 8}
    (h : BoundaryGuardClass v k) : BoundaryRecoveryClass v k := by
  obtain ⟨d,g,R,he,hp,hguard⟩ := h
  have hv := he.1
  have hdp : 0<reading v k d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨d,he.2.1,rfl⟩)
  have hgp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,he.2.2.1,rfl⟩)
  have ht := two_opening_displacement (reading v k d) (reading v k g) R hdp hgp he.2.2.2.2.2.2.1 he.2.2.2.2.2.2.2.1
  have hRT := ht.1.le.trans ht.2.1.le
  refine ⟨d,g,R,he,hp,?_⟩
  intro i hi hid hclear
  have hip : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  have hlo := le_of_not_gt (fun hh=>hclear ((inWay_iff_lower_not_passed _ _).2 hh))
  have hu := (le_div_iff₀ hip).1 (hguard i hi hid hclear)
  have hu' : reading v k i*returnOpening (reading v k d) (reading v k g) R ≤
      (label (reading v k i*R) : ℝ)+7/8 := by simpa only [closing,mul_comm] using hu
  exact (band_at_point _ R _ _ _ hip.le hRT le_rfl hlo hu').1

theorem boundaryRecovery_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : BoundaryRecoveryClass v k) : Isolation v k :=
  residualRecovery_isolation (residualCompact_into_recovery (boundaryRecovery_into_residualCompact h))

-- STANDING: DEFINITION
noncomputable def FirstBoundaryGuardClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (d g f : Fin 8) (R : ℝ), Entry v k d g R ∧ BoundaryPacket v k d g R ∧
    f≠k ∧ f≠d ∧ ¬InWay (reading v k f) R ∧
    (∀ i : Fin 8,i≠k → i≠d → ¬InWay (reading v k i) R →
      closing (reading v k f) R ≤ closing (reading v k i) R) ∧
    returnOpening (reading v k d) (reading v k g) R ≤ closing (reading v k f) R

theorem firstBoundaryGuard_into_guard {v : Fin 8 → ℝ} {k : Fin 8}
    (h : FirstBoundaryGuardClass v k) : BoundaryGuardClass v k := by
  obtain ⟨d,g,f,R,he,hp,hf,hfd,hclear,hfirst,hfit⟩ := h
  exact ⟨d,g,R,he,hp,fun i hi hid hclear=>hfit.trans (hfirst i hi hid hclear)⟩

theorem boundary_new_capture_outside_packet {v : Fin 8 → ℝ} {k d g : Fin 8} {R : ℝ}
    (he : Entry v k d g R) (hp : BoundaryPacket v k d g R) (i : Fin 8) (hi : i≠k)
    (hw : InWay (reading v k i) (returnOpening (reading v k d) (reading v k g) R)) :
    i≠d ∧ ¬InWay (reading v k i) R := by
  have hv := he.1
  have hdp : 0<reading v k d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨d,he.2.1,rfl⟩)
  have hgp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,he.2.2.1,rfl⟩)
  have hST := (two_opening_displacement (reading v k d) (reading v k g) R hdp hgp he.2.2.2.2.2.2.1 he.2.2.2.2.2.2.2.1).2.1
  refine ⟨?_,?_⟩
  · intro hh
    subst i
    have ho := labelled_opening_identity (reading v k d) (labelledOpening (reading v k g) R) hdp
    exact not_lt_of_ge (clear_of_window _ ho.ge (by linarith only [ho])) hw
  · intro hcap
    exact (boundary_packet_retained he hp i hi hcap _ hST.le le_rfl).1 hw

#print axioms firstBoundaryGuard_into_guard
#print axioms boundary_new_capture_outside_packet

#print axioms boundary_packet_retained
#print axioms boundaryRecovery_into_residualCompact
#print axioms mixedRecovery_into_boundaryRecovery
#print axioms boundaryGuard_into_boundaryRecovery
#print axioms boundaryRecovery_isolation

#print axioms entry_move
#print axioms packet_retained
#print axioms packet_to_entry
#print axioms recovery_into_residualCompact
#print axioms recovery_isolation
#print axioms guard_into_recovery
#print axioms multiReturn_into_recovery
#print axioms earlyPhase_into_recovery
end Fresh.NativeWatcherReturnArrangement
