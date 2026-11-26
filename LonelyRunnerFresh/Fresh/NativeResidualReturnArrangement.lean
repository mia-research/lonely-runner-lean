import Fresh.NativeResidualReturnBands

/-! Residual-phase recaptures join the existing pair and sole-sharp families.
The physical returner is initially clear, without assuming an own opening.
Every outsider duty remains in recovery, closing guards or terminal bands. -/
open Classical
namespace Fresh.NativeResidualReturnArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement Fresh.NativeReturnClosingOrder
  Fresh.NativeHandoffEntryFaces Fresh.NativeFixedPrefixArrangement Fresh.NativeFixedPrefixTransport
  Fresh.NativeOneReaderDeformation Fresh.NativeOpeningReversal Fresh.NativeOpeningReversalArrangement
  Fresh.NativeThirdReaderRetention Fresh.NativeResidualReturn Fresh.NativeResidualReturnBands

-- STANDING: DEFINITION
noncomputable def ResidualRecoveryClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (d g : Fin 8) (R : ℝ), d≠k ∧ g≠k ∧ d≠g ∧ 0<R ∧
    ¬InWay (reading v k d) R ∧ InWay (reading v k g) R ∧
    InWay (reading v k d) (labelledOpening (reading v k g) R) ∧
    (∀ x∈outside v k {d,g},¬InWay x (residualEnd (reading v k d) (reading v k g) R))

theorem residualRecovery_into_pair {v : Fin 8 → ℝ} {k : Fin 8}
    (h : ResidualRecoveryClass v k) : PairRecoveryClass v k := by
  obtain ⟨hv,d,g,R,hd,hg,hdg,hR,hclear,hw,hret,hout⟩ := h
  have hgp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have ht := captured_labelled_advance _ R hgp hw
  have hS : 0<labelledOpening (reading v k g) R := by linarith only [hR,ht.1]
  refine ⟨hv,g,d,labelledOpening (reading v k g) R,label (reading v k g*R),hg,hd,Ne.symm hdg,hS,
    labelled_opening_identity _ R hgp,hret,?_⟩
  intro x hx
  have hx' : x∈outside v k {d,g} := by simpa only [Finset.pair_comm] using hx
  have hh := hout x hx'
  simpa only [residualEnd,if_pos hret] using hh

theorem residualRecovery_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : ResidualRecoveryClass v k) : Isolation v k := pairRecovery_isolation (residualRecovery_into_pair h)

-- STANDING: DEFINITION
noncomputable def ResidualGuardClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (d g : Fin 8) (R f : ℝ), d≠k ∧ g≠k ∧ d≠g ∧ 0<R ∧
    ¬InWay (reading v k d) R ∧ InWay (reading v k g) R ∧
    InWay (reading v k d) (labelledOpening (reading v k g) R) ∧ f∈outside v k {d,g} ∧
    (∀ x∈outside v k {d,g},¬InWay x (labelledOpening (reading v k g) R)) ∧
    (∀ x∈outside v k {d,g},closing f (labelledOpening (reading v k g) R) ≤ closing x (labelledOpening (reading v k g) R)) ∧
    residualEnd (reading v k d) (reading v k g) R ≤ closing f (labelledOpening (reading v k g) R)

theorem residualGuard_into_recovery {v : Fin 8 → ℝ} {k : Fin 8}
    (h : ResidualGuardClass v k) : ResidualRecoveryClass v k := by
  obtain ⟨hv,d,g,R,f,hd,hg,hdg,hR,hclear,hw,hret,hf,hinitial,hfirst,hend⟩ := h
  have hdp : 0<reading v k d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨d,hd,rfl⟩)
  have hgp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have hT := pair_end_after (reading v k g) (reading v k d) (labelledOpening (reading v k g) R)
    hgp hdp _ (labelled_opening_identity _ R hgp) hret
  have hSE : labelledOpening (reading v k g) R ≤ residualEnd (reading v k d) (reading v k g) R := by
    simpa only [residualEnd,if_pos hret] using hT.le
  refine ⟨hv,d,g,R,hd,hg,hdg,hR,hclear,hw,hret,?_⟩
  intro x hx
  have hp := outside_pos hv k {d,g} x hx
  have hlo := le_of_not_gt (fun hh=>(hinitial x hx) ((inWay_iff_lower_not_passed _ _).2 hh))
  have hu := (le_div_iff₀ hp).1 (hend.trans (hfirst x hx))
  have hu' : x*residualEnd (reading v k d) (reading v k g) R ≤
      (label (x*labelledOpening (reading v k g) R) : ℝ)+7/8 := by simpa only [closing,mul_comm] using hu
  exact (band_at_point x _ _ _ _ hp.le hSE le_rfl hlo hu').1

-- STANDING: DEFINITION
noncomputable def ResidualCompactClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (d g : Fin 8) (R : ℝ), d≠k ∧ g≠k ∧ d≠g ∧ 0<R ∧
    ¬InWay (reading v k d) R ∧ InWay (reading v k g) R ∧
    InWay (reading v k d) (labelledOpening (reading v k g) R) ∧ reading v k g ≤ 3*reading v k d ∧
    (∀ x∈outside v k {d,g},¬InWay x (labelledOpening (reading v k d) (labelledOpening (reading v k g) R)))

theorem residualCompact_into_recovery {v : Fin 8 → ℝ} {k : Fin 8}
    (h : ResidualCompactClass v k) : ResidualRecoveryClass v k := by
  obtain ⟨hv,d,g,R,hd,hg,hdg,hR,hclear,hw,hret,hcompact,hout⟩ := h
  have hdp : 0<reading v k d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨d,hd,rfl⟩)
  have hgp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have he := compact_residual_landing (reading v k d) (reading v k g) R hdp hgp hret hcompact
  refine ⟨hv,d,g,R,hd,hg,hdg,hR,hclear,hw,hret,?_⟩
  rw [he]
  exact hout

-- STANDING: DEFINITION
noncomputable def ResidualEarlyClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (d g : Fin 8) (R : ℝ), d≠k ∧ g≠k ∧ d≠g ∧ 0<R ∧
    ¬InWay (reading v k d) R ∧ InWay (reading v k g) R ∧
    InWay (reading v k d) (labelledOpening (reading v k g) R) ∧
    (2 ≤ advance (reading v k d) R (labelledOpening (reading v k g) R) ∨ phase (reading v k d) R ≤ 19/24) ∧
    (∀ x∈outside v k {d,g},¬InWay x (labelledOpening (reading v k d) (labelledOpening (reading v k g) R)))

theorem residualEarly_into_recovery {v : Fin 8 → ℝ} {k : Fin 8}
    (h : ResidualEarlyClass v k) : ResidualRecoveryClass v k := by
  obtain ⟨hv,d,g,R,hd,hg,hdg,hR,hclear,hw,hret,hearly,hout⟩ := h
  have hdp : 0<reading v k d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨d,hd,rfl⟩)
  have hgp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have hcompact : reading v k g ≤ 3*reading v k d := by
    rcases hearly with hm|hphase
    · have hh := multi_return_speed_gap _ _ R hdp hgp hclear hw hret hm
      nlinarith only [hh,hdp,hgp]
    · exact (early_phase_compact _ _ R hdp hgp hclear hw hret hphase).le
  have he := compact_residual_landing (reading v k d) (reading v k g) R hdp hgp hret hcompact
  refine ⟨hv,d,g,R,hd,hg,hdg,hR,hclear,hw,hret,?_⟩
  rw [he]
  exact hout

-- STANDING: DEFINITION
noncomputable def ResidualBandClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (d g : Fin 8) (R lo hi : ℝ) (M L Q : ℤ),
    d≠k ∧ g≠k ∧ d≠g ∧ 0<R ∧ 0<lo ∧ lo ≤ reading v k g ∧ reading v k g ≤ hi ∧
    ¬InWay (reading v k d) R ∧ label (lo*R)=M ∧ label (hi*R)=M ∧ InWay hi R ∧
    0 ≤ (M : ℝ)+1/8 ∧ (L : ℝ)-1/8<reading v k d*Fresh.FastestCaptureRetention.opening hi M ∧
    reading v k d*Fresh.FastestCaptureRetention.opening lo M<(L : ℝ)+1/8 ∧
    (Q : ℝ)+1/8 ≤ lo*Fresh.FastestCaptureRetention.opening (reading v k d) L ∧
    hi*Fresh.FastestCaptureRetention.opening (reading v k d) L ≤ (Q : ℝ)+7/8 ∧
    (∀ x∈outside v k {d,g},¬InWay x (Fresh.FastestCaptureRetention.opening (reading v k d) L))

theorem residualBand_into_recovery {v : Fin 8 → ℝ} {k : Fin 8}
    (h : ResidualBandClass v k) : ResidualRecoveryClass v k := by
  obtain ⟨hv,d,g,R,lo,hi,M,L,Q,hd,hg,hdg,hR,hlo,hlg,hgh,hclear,hloM,hhiM,hhiCap,hM,hleft,hright,hlower,hupper,hout⟩ := h
  have hdp : 0<reading v k d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨d,hd,rfl⟩)
  have hs := interval_return_state (reading v k d) lo (reading v k g) hi R M L hdp hlo hlg hgh hR hloM hhiM hhiCap hM hleft hright
  have he := (terminal_window_interval_landing (reading v k d) lo (reading v k g) hi R M L Q hdp hlo hlg hgh hR
    hclear hloM hhiM hhiCap hM hleft hright hlower hupper).1
  refine ⟨hv,d,g,R,hd,hg,hdg,hR,hclear,hs.1,hs.2.1,?_⟩
  rw [he]
  exact hout

-- STANDING: DEFINITION
noncomputable def ResidualSoleClosingClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (d g f : Fin 8) (R : ℝ),
    d≠k ∧ g≠k ∧ d≠g ∧ 0<R ∧ ¬InWay (reading v k d) R ∧ InWay (reading v k g) R ∧
    IsMove (disparitySet v k) R (labelledOpening (reading v k g) R) ∧
    InWay (reading v k d) (labelledOpening (reading v k g) R) ∧
    (∀ i : Fin 8,i≠k → InWay (reading v k i) (labelledOpening (reading v k g) R) → i=d) ∧
    FirstClosing v k (labelledOpening (reading v k g) R) f ∧
    labelledOpening (reading v k d) (labelledOpening (reading v k g) R) ≤
      closing (reading v k f) (labelledOpening (reading v k g) R)

theorem residualSoleClosing_into_soleSharp {v : Fin 8 → ℝ} {k : Fin 8}
    (h : ResidualSoleClosingClass v k) : SoleSharpClass v k := by
  obtain ⟨hv,d,g,f,R,hd,hg,hdg,hR,hclear,hw,hm,hret,hsole,hfirst,hfit⟩ := h
  have hdp : 0<reading v k d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨d,hd,rfl⟩)
  have hfp : 0<reading v k f := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨f,hfirst.1,rfl⟩)
  have hsur := (survivor_iff hv k R _ hm d).2 ⟨hd,hret⟩
  have hsharp : SharpEntrySecond v k (labelledOpening (reading v k g) R) d f := by
    refine ⟨hfirst,?_⟩
    have hu := (le_div_iff₀ hfp).1 hfit
    have hu' : reading v k f*labelledOpening (reading v k d) (labelledOpening (reading v k g) R) ≤
        (label (reading v k f*labelledOpening (reading v k g) R) : ℝ)+7/8 := by
      simpa only [closing,mul_comm] using hu
    exact (Fresh.NativeFirstClosing.deficit_iff_upper _ _ _ _ _ _ hdp
      (labelled_opening_identity _ _ hdp)).2 hu'
  refine ⟨hv,R,labelledOpening (reading v k g) R,d,f,hR,hm,hsur,?_,hsharp⟩
  intro i hi
  exact hsole i hi.1 ((survivor_iff hv k R _ hm i).1 hi).2

-- STANDING: DEFINITION
noncomputable def ResidualInverseTripleClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (d g c : Fin 8) (R : ℝ),
    d≠k ∧ g≠k ∧ c≠k ∧ d≠g ∧ g≠c ∧ d≠c ∧ 0<R ∧
    ¬InWay (reading v k d) R ∧ InWay (reading v k g) R ∧
    InWay (reading v k d) (labelledOpening (reading v k g) R) ∧
    InWay (reading v k g) (labelledOpening (reading v k d) (labelledOpening (reading v k g) R)) ∧
    InWay (reading v k c) (labelledOpening (reading v k g) (labelledOpening (reading v k d) (labelledOpening (reading v k g) R))) ∧
    (∀ x∈outside v k {g,d,c},¬InWay x
      (Fresh.NativeThirdReaderRebound.forcedEnd (reading v k g) (reading v k d) (reading v k c)
        (labelledOpening (reading v k d) (labelledOpening (reading v k g) R))))

theorem residualInverse_into_forcedTriple {v : Fin 8 → ℝ} {k : Fin 8}
    (h : ResidualInverseTripleClass v k) : Fresh.NativeThirdReaderForcedArrangement.ForcedTripleClass v k := by
  obtain ⟨hv,d,g,c,R,hd,hg,hc,hdg,hgc,hdc,hR,hclear,hw,hret,hinverse,hthird,hout⟩ := h
  have hdp : 0<reading v k d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨d,hd,rfl⟩)
  have hgp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have hgate := inverse_rebound_late_one (reading v k d) (reading v k g) R hdp hgp hclear hw hret hinverse
  have hRS := (captured_labelled_advance (reading v k g) R hgp hw).1
  have hST := (captured_labelled_advance (reading v k d) (labelledOpening (reading v k g) R) hdp hret).1
  refine ⟨hv,g,d,c,labelledOpening (reading v k d) (labelledOpening (reading v k g) R),
    label (reading v k d*labelledOpening (reading v k g) R),hg,hd,hc,Ne.symm hdg,hgc,hdc,?_,
    labelled_opening_identity _ _ hdp,hinverse,hthird,hgate.2.2,hout⟩
  linarith only [hR,hRS,hST]

#print axioms residualInverse_into_forcedTriple

#print axioms residualCompact_into_recovery
#print axioms residualRecovery_into_pair
#print axioms residualRecovery_isolation
#print axioms residualGuard_into_recovery
#print axioms residualEarly_into_recovery
#print axioms residualBand_into_recovery
#print axioms residualSoleClosing_into_soleSharp
end Fresh.NativeResidualReturnArrangement
