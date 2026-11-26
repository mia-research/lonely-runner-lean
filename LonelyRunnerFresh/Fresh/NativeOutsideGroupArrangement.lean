import Fresh.NativeOutsideGroupDisplacement

/-! Larger captured outsider packets, arbitrary independent entry labels.
The entire packet is discharged by its ordered7/4 strip; only initially
clear non-core watchers retain closing/recovery duties. If all five outside
readers are captured, no endpoint-clearance premise remains. -/
open Classical
namespace Fresh.NativeOutsideGroupArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeCoalescedCaptureRelay Fresh.NativeFixedPrefixTransport Fresh.NativeFixedPrefixArrangement
  Fresh.NativeGroupEndpointRecovery Fresh.NativeCanonicalReturn Fresh.NativeOpeningReversal
  Fresh.NativeThirdReaderRetention Fresh.NativeThirdReaderRebound Fresh.NativeOutsideGroupDisplacement

-- STANDING: DEFINITION
noncomputable def Entry (v : Fin 8 → ℝ) (k a b c : Fin 8) (C : ℝ) (M : ℤ) : Prop :=
  IsArrangement v ∧ a≠k ∧ b≠k ∧ c≠k ∧ a≠b ∧ a≠c ∧ b≠c ∧ 0<C ∧
    3*reading v k b<reading v k a ∧ reading v k b*C=(M : ℝ)+1/8 ∧
    InWay (reading v k a) C ∧ InWay (reading v k c) (labelledOpening (reading v k a) C)

noncomputable def Packet (v : Fin 8 → ℝ) (k a b c : Fin 8) (C : ℝ) : Prop :=
  ∀ i : Fin 8,i≠k → i≠a → i≠b → InWay (reading v k i) (labelledOpening (reading v k a) C) →
    4*reading v k i ≤ 7*reading v k c ∧
    labelledOpening (reading v k i) (labelledOpening (reading v k a) C) ≤
      labelledOpening (reading v k c) (labelledOpening (reading v k a) C)

theorem entry_core_clear {v : Fin 8 → ℝ} {k a b c : Fin 8} {C : ℝ} {M : ℤ}
    (h : Entry v k a b c C M) :
    ¬InWay (reading v k a) (labelledOpening (reading v k a) C) ∧
      ¬InWay (reading v k b) (labelledOpening (reading v k a) C) := by
  obtain ⟨hv,ha,hb,hc,hab,hac,hbc,hC,hgap,ho,hw,hthird⟩ := h
  have hpa : 0<reading v k a := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hpb : 0<reading v k b := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨b,hb,rfl⟩)
  have hown := labelled_opening_identity (reading v k a) C hpa
  have hret := own_opening_retained (reading v k a) (reading v k b) C _ _ M hpa hpb.le
    (by nlinarith only [hgap,hpb]) ho hw hown rfl
  exact ⟨not_lt.mpr (clear_of_window _ hown.ge (by linarith only [hown])),
    not_lt.mpr (clear_of_window M hret.1 hret.2.le)⟩

theorem packet_core_clear {v : Fin 8 → ℝ} {k a b c : Fin 8} {C : ℝ} {M : ℤ}
    (he : Entry v k a b c C M) (hp : Packet v k a b c C) :
    ∀ i : Fin 8,i≠k → (i=a ∨ i=b ∨ InWay (reading v k i) (labelledOpening (reading v k a) C)) →
      ¬InWay (reading v k i) (forcedEnd (reading v k a) (reading v k b) (reading v k c) C) := by
  have heSaved := he
  obtain ⟨hv,ha,hb,hc,hab,hac,hbc,hC,hgap,ho,hw,hthird⟩ := he
  have hpa : 0<reading v k a := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hpb : 0<reading v k b := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨b,hb,rfl⟩)
  have hpc : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc,rfl⟩)
  obtain ⟨H,U,hH,hCU,hUW,hm,hclear⟩ := forced_triple_resolution (reading v k a) (reading v k b) (reading v k c) C M
    hpa hpb hpc hgap ho hw hthird
  intro i hi hsource
  by_cases hia : i=a
  · subst i; exact not_lt.mpr (hclear _ (by simp))
  by_cases hib : i=b
  · subst i; exact not_lt.mpr (hclear _ (by simp))
  have hcap := hsource.resolve_left hia
  have hcap' := hcap.resolve_left hib
  have hpi : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  obtain ⟨hstrip,horder⟩ := hp i hi hia hib hcap'
  have hh := captured_group_window (reading v k a) (reading v k b) (reading v k c) (reading v k i) C M
    hpa hpb hpc hpi hgap ho hw hthird hcap' hstrip horder
  exact not_lt.mpr (clear_of_window _ hh.1 hh.2.le)

-- STANDING: DEFINITION
noncomputable def OutsideRecoveryClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (a b c : Fin 8) (C : ℝ) (M : ℤ), Entry v k a b c C M ∧ Packet v k a b c C ∧
    (∀ i : Fin 8,i≠k → i≠a → i≠b → ¬InWay (reading v k i) (labelledOpening (reading v k a) C) →
      ¬InWay (reading v k i) (forcedEnd (reading v k a) (reading v k b) (reading v k c) C))

theorem outsideRecovery_into_canonical {v : Fin 8 → ℝ} {k : Fin 8}
    (h : OutsideRecoveryClass v k) : CanonicalReturnClass v k := by
  obtain ⟨a,b,c,C,M,he,hp,hwatch⟩ := h
  have hcore := packet_core_clear he hp
  have heSaved := he
  obtain ⟨hv,ha,hb,hc,hab,hac,hbc,hC,hgap,ho,hw,hthird⟩ := he
  have hpa : 0<reading v k a := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hpb : 0<reading v k b := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨b,hb,rfl⟩)
  have hpc : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc,rfl⟩)
  obtain ⟨H,U,hH,hCU,hUW,hm,hclear⟩ := forced_triple_resolution (reading v k a) (reading v k b) (reading v k c) C M
    hpa hpb hpc hgap ho hw hthird
  have hfullclear : LonelyAt (disparitySet v k) (forcedEnd (reading v k a) (reading v k b) (reading v k c) C) := by
    intro d hd
    obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hd
    by_cases hsource : i=a ∨ i=b ∨ InWay (reading v k i) (labelledOpening (reading v k a) C)
    · exact not_lt.mp (hcore i hi hsource)
    · push Not at hsource
      exact not_lt.mp (hwatch i hi hsource.1 hsource.2.1 hsource.2.2)
  have hsub : H ⊆ disparitySet v k := by
    intro d hd
    have hx := hH hd
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with he|he|he
    · subst d; exact mem_disparitySet.mpr ⟨a,ha,rfl⟩
    · subst d; exact mem_disparitySet.mpr ⟨b,hb,rfl⟩
    · subst d; exact mem_disparitySet.mpr ⟨c,hc,rfl⟩
  have hrest : ∀ d∈disparitySet v k\H,¬InWay d (forcedEnd (reading v k a) (reading v k b) (reading v k c) C) :=
    fun d hd=>not_lt.mpr (hfullclear d (Finset.mem_sdiff.mp hd).1)
  have hfull := endpoint_clear_preserves_move (fun d hd=>disparitySet_pos hv k d (hsub hd))
    (fun d hd=>disparitySet_pos hv k d (Finset.mem_sdiff.mp hd).1) _ _ hm hrest
  rw [Finset.union_sdiff_of_subset hsub] at hfull
  exact canonical_of_isolating_move hv k _ _ (hC.trans_le hCU) hUW hfull ((isolatedAt_iff_lonelyAt v k _).2 hfullclear)

theorem outsideRecovery_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : OutsideRecoveryClass v k) : Isolation v k := canonical_isolation (outsideRecovery_into_canonical h)

-- STANDING: DEFINITION
noncomputable def OutsideGuardClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (a b c : Fin 8) (C : ℝ) (M : ℤ), Entry v k a b c C M ∧ Packet v k a b c C ∧
    (∀ i : Fin 8,i≠k → i≠a → i≠b → ¬InWay (reading v k i) (labelledOpening (reading v k a) C) →
      forcedEnd (reading v k a) (reading v k b) (reading v k c) C ≤ closing (reading v k i) (labelledOpening (reading v k a) C))

theorem outsideGuard_into_recovery {v : Fin 8 → ℝ} {k : Fin 8}
    (h : OutsideGuardClass v k) : OutsideRecoveryClass v k := by
  obtain ⟨a,b,c,C,M,he,hp,hwatch⟩ := h
  have heSaved := he
  obtain ⟨hv,ha,hb,hc,hab,hac,hbc,hC,hgap,ho,hw,hthird⟩ := he
  have hpa : 0<reading v k a := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hpb : 0<reading v k b := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨b,hb,rfl⟩)
  have hpc : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc,rfl⟩)
  have ht := forced_tail_displacement (reading v k a) (reading v k b) (reading v k c) C M hpa hpb hpc hgap ho hw hthird
  have hfirst := captured_labelled_advance (reading v k c) (labelledOpening (reading v k a) C) hpc hthird
  have hEW : labelledOpening (reading v k a) C ≤ forcedEnd (reading v k a) (reading v k b) (reading v k c) C := by
    linarith only [ht.1,hfirst.1]
  refine ⟨a,b,c,C,M,heSaved,hp,?_⟩
  intro i hi hia hib hclear
  have hpi : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  have hlo := le_of_not_gt (fun hh=>hclear ((inWay_iff_lower_not_passed _ _).2 hh))
  have hu := (le_div_iff₀ hpi).1 (hwatch i hi hia hib hclear)
  have hu' : reading v k i*forcedEnd (reading v k a) (reading v k b) (reading v k c) C ≤
      (label (reading v k i*labelledOpening (reading v k a) C) : ℝ)+7/8 := by simpa only [closing,mul_comm] using hu
  exact (band_at_point _ _ _ _ _ hpi.le hEW le_rfl hlo hu').1

-- STANDING: DEFINITION
noncomputable def AllOutsideCapturedClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (a b c : Fin 8) (C : ℝ) (M : ℤ), Entry v k a b c C M ∧ Packet v k a b c C ∧
    (∀ i : Fin 8,i≠k → i≠a → i≠b → InWay (reading v k i) (labelledOpening (reading v k a) C))

theorem allOutsideCaptured_into_guard {v : Fin 8 → ℝ} {k : Fin 8}
    (h : AllOutsideCapturedClass v k) : OutsideGuardClass v k := by
  obtain ⟨a,b,c,C,M,he,hp,hcap⟩ := h
  exact ⟨a,b,c,C,M,he,hp,fun i hi hia hib hn=>(hn (hcap i hi hia hib)).elim⟩

theorem allOutsideCaptured_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : AllOutsideCapturedClass v k) : Isolation v k :=
  outsideRecovery_isolation (outsideGuard_into_recovery (allOutsideCaptured_into_guard h))

-- STANDING: DEFINITION
noncomputable def IndependentOutsideBandClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (a b c : Fin 8) (C : ℝ) (M : ℤ), Entry v k a b c C M ∧
    (∀ i : Fin 8,i≠k → i≠a → i≠b → ∃ (lo hi : ℝ) (K : ℤ),
      0<lo ∧ lo ≤ reading v k i ∧ reading v k i ≤ hi ∧
      label (lo*labelledOpening (reading v k a) C)=K ∧ label (hi*labelledOpening (reading v k a) C)=K ∧
      InWay hi (labelledOpening (reading v k a) C) ∧ 0 ≤ (K : ℝ)+1/8 ∧ 4*hi ≤ 7*reading v k c ∧
      Fresh.FastestCaptureRetention.opening lo K ≤ labelledOpening (reading v k c) (labelledOpening (reading v k a) C))

theorem independentBand_into_allCaptured {v : Fin 8 → ℝ} {k : Fin 8}
    (h : IndependentOutsideBandClass v k) : AllOutsideCapturedClass v k := by
  obtain ⟨a,b,c,C,M,he,hbands⟩ := h
  have hv := he.1
  have heSaved := he
  obtain ⟨hv',ha,hb,hc,hab,hac,hbc,hC,hgap,ho,hw,hthird⟩ := he
  have hpa : 0<reading v k a := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hstep := captured_labelled_advance (reading v k a) C hpa hw
  have hE : 0<labelledOpening (reading v k a) C := by linarith only [hC,hstep.1]
  have hpoint : ∀ i : Fin 8,i≠k → i≠a → i≠b →
      InWay (reading v k i) (labelledOpening (reading v k a) C) ∧
      (4*reading v k i ≤ 7*reading v k c ∧ labelledOpening (reading v k i) (labelledOpening (reading v k a) C) ≤
        labelledOpening (reading v k c) (labelledOpening (reading v k a) C)) := by
    intro i hi hia hib
    obtain ⟨lo,hi',K,hlo,hloi,hihi,hloK,hhiK,hcapHi,hK,hstrip,horder⟩ := hbands i hi hia hib
    have hlabel := speed_interval_label lo (reading v k i) hi' (labelledOpening (reading v k a) C) hloi hihi hE.le (hloK.trans hhiK.symm)
    rw [hloK] at hlabel
    have hcap := speed_interval_capture lo (reading v k i) hi' (labelledOpening (reading v k a) C) hloi hihi hE.le (hloK.trans hhiK.symm) hcapHi
    have hlow := (interval_opening_bounds lo (reading v k i) hi' K hlo hloi hihi hK).2.trans horder
    refine ⟨hcap,by linarith only [hihi,hstrip],?_⟩
    change Fresh.FastestCaptureRetention.opening (reading v k i) (label (reading v k i*labelledOpening (reading v k a) C)) ≤ _
    rw [hlabel]
    exact hlow
  exact ⟨a,b,c,C,M,heSaved,fun i hi hia hib _=>(hpoint i hi hia hib).2,fun i hi hia hib=>(hpoint i hi hia hib).1⟩

-- STANDING: DEFINITION
noncomputable def FirstWatcherGuardClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (a b c f : Fin 8) (C : ℝ) (M : ℤ), Entry v k a b c C M ∧ Packet v k a b c C ∧
    f≠k ∧ f≠a ∧ f≠b ∧ ¬InWay (reading v k f) (labelledOpening (reading v k a) C) ∧
    (∀ i : Fin 8,i≠k → i≠a → i≠b → ¬InWay (reading v k i) (labelledOpening (reading v k a) C) →
      closing (reading v k f) (labelledOpening (reading v k a) C) ≤ closing (reading v k i) (labelledOpening (reading v k a) C)) ∧
    forcedEnd (reading v k a) (reading v k b) (reading v k c) C ≤ closing (reading v k f) (labelledOpening (reading v k a) C)

theorem firstWatcher_into_guard {v : Fin 8 → ℝ} {k : Fin 8}
    (h : FirstWatcherGuardClass v k) : OutsideGuardClass v k := by
  obtain ⟨a,b,c,f,C,M,he,hp,hf,hfa,hfb,hclear,hfirst,hfit⟩ := h
  exact ⟨a,b,c,C,M,he,hp,fun i hi hia hib hn=>hfit.trans (hfirst i hi hia hib hn)⟩

theorem new_capture_is_watcher {v : Fin 8 → ℝ} {k a b c : Fin 8} {C : ℝ} {M : ℤ}
    (he : Entry v k a b c C M) (hp : Packet v k a b c C) (i : Fin 8) (hi : i≠k)
    (hcap : InWay (reading v k i) (forcedEnd (reading v k a) (reading v k b) (reading v k c) C)) :
    i≠a ∧ i≠b ∧ ¬InWay (reading v k i) (labelledOpening (reading v k a) C) := by
  have hcore := packet_core_clear he hp
  have hn : ¬(i=a ∨ i=b ∨ InWay (reading v k i) (labelledOpening (reading v k a) C)) :=
    fun hh=>hcore i hi hh hcap
  simpa only [not_or] using hn

#print axioms entry_core_clear
#print axioms packet_core_clear
#print axioms outsideRecovery_into_canonical
#print axioms outsideRecovery_isolation
#print axioms outsideGuard_into_recovery
#print axioms allOutsideCaptured_into_guard
#print axioms allOutsideCaptured_isolation
#print axioms independentBand_into_allCaptured
#print axioms firstWatcher_into_guard
#print axioms new_capture_is_watcher
end Fresh.NativeOutsideGroupArrangement
