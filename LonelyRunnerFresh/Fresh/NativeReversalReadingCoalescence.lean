import Fresh.NativeSuppliedReversalArrangement

/-! Quotient physical outsider duties by membership of their absolute
reading in the already clear core. Distinct moving physical speeds can have
equal absolute readings on opposite sides of the subject. -/
namespace Fresh.NativeReversalReadingCoalescence
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeOpeningReversal Fresh.NativeOneReaderDeformation
  Fresh.NativeFixedPrefixArrangement Fresh.NativeGroupEndpointRecovery Fresh.NativeCanonicalReturn
  Fresh.NativeCapturedReversalFamily Fresh.NativeSuppliedRetainedWindow Fresh.FastestCaptureRetention
  Fresh.NativeSuppliedReversalArrangement

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (a b c : Fin 8) (C E : ℝ) (M L : ℤ), Entry v k a b c C E M L ∧
    ∀ i : Fin 8, i≠k → reading v k i∉({reading v k a,reading v k b,reading v k c} : Finset ℝ) →
      GroupMember (reading v k i) (reading v k c) E ∨
      ∃ J : ℤ, Face (reading v k i) (reading v k c) E J

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
    · have hw := Fresh.NativeSuppliedOpeningGroup.captured_group_window
        _ _ _ _ C E M L hpa hpb hpc hpi hfast ho hCE hquarter hoa hthird hg.1 hg.2.1 hg.2.2
      exact clear_of_window _ hw.1 hw.2.le
    · have hw := retained_window _ _ E _ J hpi hpc hEF htail.2 hface
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
    (h : Fresh.NativeSuppliedReversalArrangement.Class v k) : Class v k := by
  obtain ⟨a,b,c,C,E,M,L,he,houtside⟩ := h
  refine ⟨a,b,c,C,E,M,L,he,?_⟩
  intro i hi hcore
  have hia : i≠a := by intro hh; subst i; exact hcore (by simp)
  have hib : i≠b := by intro hh; subst i; exact hcore (by simp)
  have hic : i≠c := by intro hh; subst i; exact hcore (by simp)
  exact houtside i hi hia hib hic

theorem old_scaled_into_class {v : Fin 8 → ℝ} {k : Fin 8}
    (h : Fresh.NativeSuppliedReversalArrangement.ScaledClass v k) : ScaledClass v k := by
  obtain ⟨hv,c,hc,hbase⟩ := h
  exact ⟨hv,c,hc,old_into_class hbase⟩

#print axioms class_into_canonical
#print axioms class_isolation
#print axioms scaled_isolation
#print axioms old_into_class
#print axioms old_scaled_into_class
end Fresh.NativeReversalReadingCoalescence
