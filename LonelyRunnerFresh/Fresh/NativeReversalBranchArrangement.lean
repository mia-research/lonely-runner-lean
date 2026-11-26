import Fresh.NativeReversalBranchFaces

/-! Branch-refined native faces, modulo core-reading equivalence. The
actual branch law derives terminal clearance. Composed entry fit provides
a direct geometric family without an assumed terminal guard. -/
namespace Fresh.NativeReversalBranchArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeOpeningReversal Fresh.NativeOneReaderDeformation
  Fresh.NativeFixedPrefixArrangement Fresh.NativeGroupEndpointRecovery Fresh.NativeCanonicalReturn
  Fresh.NativeCapturedReversalFamily Fresh.NativeSuppliedRetainedWindow Fresh.FastestCaptureRetention
  Fresh.NativeSuppliedReversalArrangement
  Fresh.NativeReversalBranchFaces

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (a b c : Fin 8) (C E : ℝ) (M L : ℤ), Entry v k a b c C E M L ∧
    ∀ i : Fin 8, i≠k → reading v k i∉({reading v k a,reading v k b,reading v k c} : Finset ℝ) →
      (InWay (reading v k i) E ∧
        reading v k i*phase (reading v k a) (reading v k b) (reading v k c) E ≤ 3*reading v k c/4 ∧
        labelledOpening (reading v k i) E ≤ labelledOpening (reading v k c) E) ∨
      ∃ J : ℤ, Fresh.NativeReversalBranchFaces.Face (reading v k i) (reading v k c) E J
        (phase (reading v k a) (reading v k b) (reading v k c) E)

theorem class_into_canonical {v : Fin 8 → ℝ} {k : Fin 8}
    (h : Class v k) : CanonicalReturnClass v k := by
  classical
  obtain ⟨a,b,c,C,E,M,L,he,houtside⟩ := h
  obtain ⟨hv,ha,hb,hc,hab,hac,hbc,hC,hfast,ho,hCE,hquarter,hoa,hthird⟩ := he
  have hpa : 0 < reading v k a := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hpb : 0 < reading v k b := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨b,hb,rfl⟩)
  have hpc : 0 < reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc,rfl⟩)
  obtain ⟨H,U,hH,hCU,hUR,hm,hclear⟩ := Fresh.NativeSuppliedOpeningTriple.forced_triple_resolution
    _ _ _ C E M L hpa hpb hpc hfast ho hCE hquarter hoa hthird
  have htail := Fresh.NativeSuppliedOpeningGroup.forced_tail_displacement
    _ _ _ C E M L hpa hpb hpc hfast ho hCE hquarter hoa hthird
  have hbranch := entry_phase _ _ _ C E M L hpa hpb hpc hfast ho hCE hquarter hoa hthird
  have hEF : E ≤ Fresh.NativeSuppliedOpeningTriple.exitEnd (reading v k a) (reading v k b) (reading v k c) E := by
    have hh := Fresh.NativeThirdReaderRetention.captured_labelled_advance (reading v k c) E hpc hthird
    linarith only [hh.1,htail.1]
  have hfullclear : LonelyAt (disparitySet v k)
      (Fresh.NativeSuppliedOpeningTriple.exitEnd (reading v k a) (reading v k b) (reading v k c) E) := by
    intro d hd
    obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hd
    change 1/8 ≤ distInt (reading v k i*_)
    by_cases hcore : reading v k i∈({reading v k a,reading v k b,reading v k c} : Finset ℝ)
    · exact hclear _ hcore
    have hpi : 0 < reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
    rcases houtside i hi hcore with hg|⟨J,hface⟩
    · have hw := Fresh.NativeReversalBranchFaces.captured_window
        (reading v k i) (reading v k c) E _ _ hpi hpc hg.1 hbranch.2 htail.1 hg.2.2 hg.2.1
      exact clear_of_window _ hw.1 hw.2.le
    · have hw := Fresh.NativeReversalBranchFaces.retained_window _ _ E _ _ J hpi hpc hEF hbranch.2 hface
      exact clear_of_window J hw.1 hw.2.le
  have hsub : H ⊆ disparitySet v k := by
    intro d hd
    have hx := hH hd
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl
    · exact mem_disparitySet.mpr ⟨a,ha,rfl⟩
    · exact mem_disparitySet.mpr ⟨b,hb,rfl⟩
    · exact mem_disparitySet.mpr ⟨c,hc,rfl⟩
  have hfull := endpoint_clear_preserves_move (ds:=H) (added:=disparitySet v k\H)
    (fun d hd=>disparitySet_pos hv k d (hsub hd))
    (fun d hd=>disparitySet_pos hv k d (Finset.mem_sdiff.mp hd).1) _ _ hm
    (fun d hd=>not_lt.mpr (hfullclear d (Finset.mem_sdiff.mp hd).1))
  rw [Finset.union_sdiff_of_subset hsub] at hfull
  exact canonical_of_isolating_move hv k _ _ (hC.trans_le hCU) hUR hfull
    ((isolatedAt_iff_lonelyAt v k _).2 hfullclear)

theorem class_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : Isolation v k :=
  canonical_isolation (class_into_canonical h)

-- STANDING: DEFINITION
noncomputable def ScaledClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ c : ℝ, 0 < c ∧ Class (fun i=>c*v i) k

theorem scaled_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) : Isolation v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact Fresh.ProvedTypesScale.Isolation_smul_of hc (class_isolation hbase)

theorem old_into_class {v : Fin 8 → ℝ} {k : Fin 8}
    (h : Fresh.NativeReversalReadingCoalescence.Class v k) : Class v k := by
  obtain ⟨a,b,c,C,E,M,L,he,houtside⟩ := h
  have hs := he
  obtain ⟨hv,ha,hb,hc,hab,hac,hbc,hC,hfast,ho,hCE,hquarter,hoa,hthird⟩ := hs
  have hpa := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hpb := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨b,hb,rfl⟩)
  have hpc := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc,rfl⟩)
  have hr := (entry_phase _ _ _ C E M L hpa hpb hpc hfast ho hCE hquarter hoa hthird).1.le
  refine ⟨a,b,c,C,E,M,L,he,?_⟩
  intro i hi hcore
  have hpi := (disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)).le
  rcases houtside i hi hcore with hg|⟨J,hf⟩
  · exact Or.inl ⟨hg.1,coarse_strip _ _ _ hpi hr hg.2.1,hg.2.2⟩
  · exact Or.inr ⟨J,coarse_face _ _ _ _ J hpi hr hf⟩

theorem old_scaled_into_class {v : Fin 8 → ℝ} {k : Fin 8}
    (h : Fresh.NativeReversalReadingCoalescence.ScaledClass v k) : ScaledClass v k := by
  obtain ⟨hv,c,hc,hbase⟩ := h
  exact ⟨hv,c,hc,old_into_class hbase⟩

-- Composed entry fit forces phase=1/3 without assuming a terminal guard.
theorem fitted_into_class {v : Fin 8 → ℝ} {k a b c : Fin 8} {C E : ℝ} {M L : ℤ}
    (he : Entry v k a b c C E M L)
    (hfit : reading v k a*reading v k b+2*reading v k b*reading v k c ≤
      3*reading v k a*reading v k c)
    (houtside : ∀ i : Fin 8, i≠k →
      reading v k i∉({reading v k a,reading v k b,reading v k c} : Finset ℝ) →
      (InWay (reading v k i) E ∧ reading v k i*(1/3) ≤ 3*reading v k c/4 ∧
        labelledOpening (reading v k i) E ≤ labelledOpening (reading v k c) E) ∨
      ∃ J : ℤ, Fresh.NativeReversalBranchFaces.Face (reading v k i) (reading v k c) E J (1/3)) :
    Class v k := by
  have hs := he
  obtain ⟨hv,ha,hb,hc,hab,hac,hbc,hC,hfast,ho,hCE,hquarter,hoa,hthird⟩ := hs
  have hpa := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hpb := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨b,hb,rfl⟩)
  have hpc := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc,rfl⟩)
  have hr := (fit_exit _ _ _ C E M L hpa hpb hpc ho hCE hquarter hoa hthird hfit).2
  change phase (reading v k a) (reading v k b) (reading v k c) E=1/3 at hr
  refine ⟨a,b,c,C,E,M,L,he,?_⟩
  intro i hi hcore
  rw [hr]
  exact houtside i hi hcore

#print axioms class_into_canonical
#print axioms class_isolation
#print axioms scaled_isolation
#print axioms old_into_class
#print axioms old_scaled_into_class
#print axioms fitted_into_class
end Fresh.NativeReversalBranchArrangement
