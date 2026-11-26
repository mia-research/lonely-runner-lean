import Fresh.NativeSuppliedRetainedWindow
import Fresh.NativeCapturedReversalFamily

/-! Generic native supplied-opening reversal arrangements. Every non-core
reader is admitted by a captured-group face or a retained entry-window face.
The native phase law derives terminal guards; parameterized quiet families
embed, while arbitrary entry and recurrence forcing remain separate duties. -/
namespace Fresh.NativeSuppliedReversalArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeOpeningReversal Fresh.NativeOneReaderDeformation
  Fresh.NativeFixedPrefixArrangement Fresh.NativeGroupEndpointRecovery Fresh.NativeCanonicalReturn
  Fresh.NativeCapturedReversalFamily Fresh.NativeSuppliedRetainedWindow Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def Entry (v : Fin 8 → ℝ) (k a b c : Fin 8) (C E : ℝ) (M L : ℤ) : Prop :=
  IsArrangement v ∧ a≠k ∧ b≠k ∧ c≠k ∧ a≠b ∧ a≠c ∧ b≠c ∧ 0 < C ∧
    3*reading v k b < reading v k a ∧ reading v k b*C=(M : ℝ)+1/8 ∧
    C ≤ E ∧ reading v k a*(E-C) ≤ 1/4 ∧ reading v k a*E=(L : ℝ)+1/8 ∧
    InWay (reading v k c) E

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (a b c : Fin 8) (C E : ℝ) (M L : ℤ), Entry v k a b c C E M L ∧
    ∀ i : Fin 8, i≠k → i≠a → i≠b → i≠c →
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
    by_cases hia : i=a
    · subst i; exact hclear _ (by simp)
    by_cases hib : i=b
    · subst i; exact hclear _ (by simp)
    by_cases hic : i=c
    · subst i; exact hclear _ (by simp)
    have hpi : 0 < reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
    rcases houtside i hi hia hib hic with hg|⟨J,hface⟩
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
    (h : Fresh.NativeCapturedReversalFamily.Class v k) : Class v k := by
  obtain ⟨hv,a,b,c,M,A,N,x,ha,hb,hc,hab,hac,hbc,hM,hA,hN,hxlo,hxhi,hda,hsb,hclo,hthird,houtside⟩ := h
  have hf := Fresh.NativeArbitraryThirdReversal.incoming_faces M A N x hM hA hN hxlo hxhi
  have he := Fresh.NativeQuietReversalFamily.ending_bounds M A N hM hA hN
  have hsep := Fresh.NativeArbitraryThirdReversal.parameter_separation M A N x hM hA hN hxlo hxhi
  refine ⟨a,b,c,Fresh.NativeArbitraryThirdReversal.firstTime A N x,
    Fresh.NativeQuietReversalFamily.ending A N,M,N+A,?_,?_⟩
  · refine ⟨hv,ha,hb,hc,hab,hac,hbc,by linarith only [hf.1],?_,?_,hf.2.1,?_,?_,hthird⟩
    · rw [hda,hsb]; exact hsep.2.2
    · rw [hsb]; exact hf.2.2.1
    · rw [hda]; exact hf.2.2.2.2
    · rw [hda]; exact hf.2.2.2.1
  · intro i hi hia hib hic
    rcases houtside i hi hia hib hic with hquiet|hgroup
    · exact Or.inr ⟨0,quiet_face _ _ _ hquiet.1 hquiet.2
        (Fresh.NativeArbitraryThirdReversal.third_lower _ _ hclo he.1.le he.2 hthird) he.1.le he.2⟩
    · exact Or.inl hgroup

theorem old_scaled_into_class {v : Fin 8 → ℝ} {k : Fin 8}
    (h : Fresh.NativeCapturedReversalFamily.ScaledClass v k) : ScaledClass v k := by
  obtain ⟨hv,c,hc,hbase⟩ := h
  exact ⟨hv,c,hc,old_into_class hbase⟩

#print axioms class_into_canonical
#print axioms class_isolation
#print axioms scaled_isolation
#print axioms old_into_class
#print axioms old_scaled_into_class
end Fresh.NativeSuppliedReversalArrangement
