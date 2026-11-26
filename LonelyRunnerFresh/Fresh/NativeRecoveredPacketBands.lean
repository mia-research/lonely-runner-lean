import Fresh.NativePacketTailArrangement

/-! Independent captured packet coordinates may clear in different terminal
integer windows. Whole setter and packet bands share one returned-reader
opening, even when their return labels or intermediate captures differ. -/
open Classical
namespace Fresh.NativeRecoveredPacketBands
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeOneReaderDeformation Fresh.NativeOpeningReversal
  Fresh.NativeThirdReaderRetention Fresh.NativeResidualReturn Fresh.NativeResidualReturnBands
  Fresh.NativeResidualReturnArrangement Fresh.NativeFixedPrefixArrangement Fresh.NativeFixedPrefixTransport
  Fresh.NativeCoalescedCaptureRelay Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def BoxClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (d g : Fin 8) (R lo hi : ℝ) (M L Qg : ℤ) (I : Finset (Fin 8)),
    d≠k ∧ g≠k ∧ d≠g ∧ 0<R ∧ 0<lo ∧ lo ≤ reading v k g ∧ reading v k g ≤ hi ∧
    ¬InWay (reading v k d) R ∧ label (lo*R)=M ∧ label (hi*R)=M ∧ InWay hi R ∧
    0 ≤ (M : ℝ)+1/8 ∧ (L : ℝ)-1/8<reading v k d*opening hi M ∧
    reading v k d*opening lo M<(L : ℝ)+1/8 ∧
    (Qg : ℝ)+1/8 ≤ lo*opening (reading v k d) L ∧ hi*opening (reading v k d) L ≤ (Qg : ℝ)+7/8 ∧
    I ⊆ (Finset.univ.erase k)\{d,g} ∧
    (∀ i∈I,∃ (al ah : ℝ) (K Q : ℤ), 0<al ∧ al ≤ reading v k i ∧ reading v k i ≤ ah ∧
      label (al*R)=K ∧ label (ah*R)=K ∧ InWay ah R ∧ 0 ≤ (K : ℝ)+1/8 ∧
      opening al K ≤ opening hi M ∧
      (Q : ℝ)+1/8 ≤ al*opening (reading v k d) L ∧ ah*opening (reading v k d) L ≤ (Q : ℝ)+7/8) ∧
    (∀ i : Fin 8,i≠k → i≠d → i≠g → i∉I →
      ¬InWay (reading v k i) R ∧ ¬InWay (reading v k i) (opening (reading v k d) L))

theorem box_into_residualBand {v : Fin 8 → ℝ} {k : Fin 8} (h : BoxClass v k) : ResidualBandClass v k := by
  obtain ⟨hv,d,g,R,lo,hi,M,L,Qg,I,hd,hg,hdg,hR,hlo,hlg,hgh,hclear,hloM,hhiM,hwHi,hM,hleft,hright,hgLo,hgHi,hI,hbands,hother⟩ := h
  have hdp : 0<reading v k d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨d,hd,rfl⟩)
  have hgp : 0<reading v k g := hlo.trans_le hlg
  have hs := interval_return_state (reading v k d) lo (reading v k g) hi R M L hdp hlo hlg hgh hR hloM hhiM hwHi hM hleft hright
  have h1 := captured_labelled_advance (reading v k g) R hgp hs.1
  have h2 := captured_labelled_advance (reading v k d) (labelledOpening (reading v k g) R) hdp hs.2.1
  have hT : 0<opening (reading v k d) L := by rw [←hs.2.2]; linarith only [hR,h1.1,h2.1]
  refine ⟨hv,d,g,R,lo,hi,M,L,Qg,hd,hg,hdg,hR,hlo,hlg,hgh,hclear,hloM,hhiM,hwHi,hM,hleft,hright,hgLo,hgHi,?_⟩
  intro s hsout
  obtain ⟨i,hiout,rfl⟩ := Finset.mem_image.mp hsout
  have hik : i≠k := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hiout).1).1
  have hid : i≠d := by intro hh; subst i; exact (Finset.mem_sdiff.mp hiout).2 (by simp)
  have hig : i≠g := by intro hh; subst i; exact (Finset.mem_sdiff.mp hiout).2 (by simp)
  by_cases hiI : i∈I
  · obtain ⟨al,ah,K,Q,hal,hl,hhi,hlK,hhK,hwah,hK,horder,htermLo,htermHi⟩ := hbands i hiI
    exact (interval_band_at_point al (reading v k i) ah _ _ _ Q hal hl hhi hT.le le_rfl le_rfl htermLo htermHi).1
  · exact (hother i hik hid hig hiI).2

theorem box_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : BoxClass v k) : Isolation v k :=
  residualRecovery_isolation (residualBand_into_recovery (box_into_residualBand h))

-- The first selected opening is derived across the independent coordinates.
theorem box_has_first_move {v : Fin 8 → ℝ} {k : Fin 8} (h : BoxClass v k) :
    ∃ (d g : Fin 8) (R : ℝ), 0<R ∧ ¬InWay (reading v k d) R ∧ InWay (reading v k g) R ∧
      IsMove (disparitySet v k) R (labelledOpening (reading v k g) R) ∧
      InWay (reading v k d) (labelledOpening (reading v k g) R) := by
  obtain ⟨hv,d,g,R,lo,hi,M,L,Qg,I,hd,hg,hdg,hR,hlo,hlg,hgh,hclear,hloM,hhiM,hwHi,hM,hleft,hright,hgLo,hgHi,hI,hbands,hother⟩ := h
  have hdp : 0<reading v k d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨d,hd,rfl⟩)
  have hgp : 0<reading v k g := hlo.trans_le hlg
  have hs := interval_return_state (reading v k d) lo (reading v k g) hi R M L hdp hlo hlg hgh hR hloM hhiM hwHi hM hleft hright
  have hlabel := speed_interval_label lo (reading v k g) hi R hlg hgh hR.le (hloM.trans hhiM.symm)
  rw [hloM] at hlabel
  have hgS : labelledOpening (reading v k g) R=opening (reading v k g) M := by simp only [labelledOpening,hlabel]
  refine ⟨d,g,R,hR,hclear,hs.1,?_,hs.2.1⟩
  refine Or.inr ⟨reading v k g,mem_disparitySet.mpr ⟨g,hg,rfl⟩,hs.1,(captured_opening _ R hs.1).symm,?_⟩
  intro s hsm hws
  obtain ⟨i,hiidx,rfl⟩ := mem_disparitySet.mp hsm
  rw [captured_opening _ R hws]
  by_cases hig : i=g
  · subst i; exact le_rfl
  have hid : i≠d := by intro hh; subst i; exact hclear hws
  have hiI : i∈I := by
    by_contra hn
    exact (hother i hiidx hid hig hn).1 hws
  obtain ⟨al,ah,K,Q,hal,hl,hhi,hlK,hhK,hwah,hK,horder,htermLo,htermHi⟩ := hbands i hiI
  have hilabel := speed_interval_label al (reading v k i) ah R hl hhi hR.le (hlK.trans hhK.symm)
  rw [hlK] at hilabel
  have hbound := (interval_opening_bounds al (reading v k i) ah K hal hl hhi hK).2
  have hgBound := (interval_opening_bounds lo (reading v k g) hi M hlo hlg hgh hM).1
  change opening (reading v k i) (label (reading v k i*R)) ≤ _
  rw [hilabel,hgS]
  exact hbound.trans (horder.trans hgBound)

#print axioms box_into_residualBand
#print axioms box_isolation
#print axioms box_has_first_move
end Fresh.NativeRecoveredPacketBands
