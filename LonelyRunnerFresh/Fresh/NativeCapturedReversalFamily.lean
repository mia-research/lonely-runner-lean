import Fresh.NativeSuppliedOpeningGroup
import Fresh.NativeArbitraryThirdReversal
import Fresh.NativeWitnessPacketReentry
import Fresh.NativeNarrowCaptureBlock

/-! The supplied-opening reversal accepts an entire captured group, with
independent entry labels, alongside quiet readers. Native phase displacement
forces their clear windows; neither closing nor terminal-clear guards are
assumed. Common-label and narrow-band intersections derive group geometry. -/
namespace Fresh.NativeCapturedReversalFamily
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeOpeningReversal Fresh.NativeOneReaderDeformation
  Fresh.NativeQuietReversalFamily Fresh.NativeFixedPrefixArrangement Fresh.NativeGroupEndpointRecovery
  Fresh.NativeCanonicalReturn Fresh.NativeRecapturedLabelReset Fresh.FastestCaptureRetention
  Fresh.NativeArbitraryThirdReversal

-- STANDING: DEFINITION
noncomputable def GroupMember (s c E : ℝ) : Prop :=
  InWay s E ∧ 4*s ≤ 7*c ∧ labelledOpening s E ≤ labelledOpening c E

theorem same_label_group_member (s c E : ℝ) (hc : 0  <  c) (hcs : c  ≤  s) (hEp : 0  <  E)
    (hs : InWay s E) (hcap : InWay c E) (hl : label (s*E)=label (c*E))
    (hN : 0  <  label (c*E)) : GroupMember s c E := by
  have hr := Fresh.NativeWitnessPacketReentry.common_positive_label_sharp s c E hEp hs hcap hl hN
  have hn : (1 : ℝ) ≤ (label (c*E) : ℝ) := by exact_mod_cast hN
  refine ⟨hs,by nlinarith only [hr,hc],?_⟩
  dsimp [labelledOpening,opening]
  rw [hl]
  apply (div_le_div_iff₀ (hc.trans_le hcs) hc).2
  have hprod := mul_le_mul_of_nonneg_left hcs
    (show 0 ≤ (label (c*E) : ℝ)+1/8 by linarith only [hn])
  nlinarith only [hprod]

theorem narrow_group_member (p s c q E : ℝ) (hc : 0  <  c) (hcs : c  ≤  s) (hEp : 0  <  E)
    (hpc : p ≤ c) (hcq : c ≤ q) (hps : p ≤ s) (hsq : s ≤ q) (hspan : (q-p)*E ≤ 3/4)
    (hs : InWay s E) (hcap : InWay c E) (hN : 0  <  label (c*E)) : GroupMember s c E := by
  exact same_label_group_member s c E hc hcs hEp hs hcap
    (Fresh.NativeNarrowCaptureBlock.band_captured_labels_equal p s c q E hEp.le
      hps hsq hpc hcq hspan hs hcap) hN

theorem witness_group_member {v : Fin 8 → ℝ} {k i g : Fin 8} {P : ℝ} {I : Finset (Fin 8)}
    (h : Fresh.NativeWitnessPacketReentry.PacketWitness v k P I) (hi : i∈I) (hg : g∈I)
    (hgp : 0 < reading v k g) (E : ℝ) (hcap : InWay (reading v k i) E)
    (horder : labelledOpening (reading v k i) E ≤ labelledOpening (reading v k g) E) :
    GroupMember (reading v k i) (reading v k g) E := by
  have hr := Fresh.NativeWitnessPacketReentry.witness_pair_sharp h hi hg
  exact ⟨hcap,by nlinarith only [hr,hgp],horder⟩

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (a b c : Fin 8) (M A N : ℤ) (x : ℝ),
    a≠k ∧ b≠k ∧ c≠k ∧ a≠b ∧ a≠c ∧ b≠c ∧
    1 ≤ M ∧ 1 ≤ A ∧ 4*A*M ≤ N ∧ -(1/8 : ℝ) ≤ x ∧ x ≤ 1/8 ∧
    reading v k a=anchor N ∧ reading v k b=partner M A N x ∧
    1/8 ≤ reading v k c ∧ InWay (reading v k c) (ending A N) ∧
    ∀ i : Fin 8, i≠k → i≠a → i≠b → i≠c →
      (1/8 ≤ reading v k i ∧ reading v k i ≤ 3/8) ∨
      GroupMember (reading v k i) (reading v k c) (ending A N)

theorem class_into_canonical {v : Fin 8 → ℝ} {k : Fin 8}
    (h : Class v k) : CanonicalReturnClass v k := by
  classical
  obtain ⟨hv,a,b,c,M,A,N,x,ha,hb,hc,hab,hac,hbc,hM,hA,hN,hxlo,hxhi,hda,hsb,hclo,hthird,houtside⟩ := h
  have hsep := parameter_separation M A N x hM hA hN hxlo hxhi
  have hf := incoming_faces M A N x hM hA hN hxlo hxhi
  have he := ending_bounds M A N hM hA hN
  have hpa : 0 < reading v k a := by rw [hda]; linarith only [hsep.1]
  have hpb : 0 < reading v k b := by rw [hsb]; linarith only [hsep.2.1]
  have hpc : 0 < reading v k c := by linarith only [hclo]
  have hfast : 3*reading v k b < reading v k a := by rw [hda,hsb]; exact hsep.2.2
  have ho : reading v k b*firstTime A N x=(M : ℝ)+1/8 := by rw [hsb]; exact hf.2.2.1
  have hoa : reading v k a*ending A N=((N+A : ℤ) : ℝ)+1/8 := by rw [hda]; exact hf.2.2.2.1
  have hquarter : reading v k a*(ending A N-firstTime A N x) ≤ 1/4 := by
    rw [hda]; exact hf.2.2.2.2
  obtain ⟨H,U,hH,hCU,hUR,hm,hclear⟩ :=
    Fresh.NativeSuppliedOpeningTriple.forced_triple_resolution
      (reading v k a) (reading v k b) (reading v k c) (firstTime A N x) (ending A N)
      M (N+A) hpa hpb hpc hfast ho hf.2.1 hquarter hoa hthird
  have hend : Fresh.NativeSuppliedOpeningTriple.exitEnd
      (reading v k a) (reading v k b) (reading v k c) (ending A N) < 7/3 :=
    Fresh.NativeSuppliedOpeningTriple.exit_before_quiet_closing _ _ _ _
      (by rw [hda]; exact hsep.1) (by rw [hsb]; exact hsep.2.1)
      (third_lower _ _ hclo he.1.le he.2 hthird) he.2 hthird
  have hfullclear : LonelyAt (disparitySet v k)
      (Fresh.NativeSuppliedOpeningTriple.exitEnd (reading v k a) (reading v k b) (reading v k c) (ending A N)) := by
    intro d hd
    obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hd
    change 1/8 ≤ distInt (reading v k i*_)
    by_cases hia : i=a
    · subst i; exact hclear _ (by simp)
    by_cases hib : i=b
    · subst i; exact hclear _ (by simp)
    by_cases hic : i=c
    · subst i; exact hclear _ (by simp)
    rcases houtside i hi hia hib hic with hquiet|hgroup
    · exact not_lt.mp (quiet_before_closing _ _ hquiet.1 hquiet.2
        (hf.1.le.trans (hCU.trans hUR.le)) hend.le)
    · have hpi : 0 < reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
      have hw := Fresh.NativeSuppliedOpeningGroup.captured_group_window
        (reading v k a) (reading v k b) (reading v k c) (reading v k i)
        (firstTime A N x) (ending A N) M (N+A) hpa hpb hpc hpi
        hfast ho hf.2.1 hquarter hoa hthird hgroup.1 hgroup.2.1 hgroup.2.2
      exact clear_of_window _ hw.1 hw.2.le
  have hpoint := (isolatedAt_iff_lonelyAt v k _).2 hfullclear
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
  exact canonical_of_isolating_move hv k _ _
    ((by linarith only [hf.1] : 0 < firstTime A N x).trans_le hCU) hUR hfull hpoint

theorem class_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : Isolation v k :=
  canonical_isolation (class_into_canonical h)

-- STANDING: DEFINITION
noncomputable def ScaledClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ c : ℝ, 0  <  c ∧ Class (fun i=>c*v i) k

theorem scaled_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) : Isolation v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact Fresh.ProvedTypesScale.Isolation_smul_of hc (class_isolation hbase)

#print axioms witness_group_member
#print axioms same_label_group_member
#print axioms narrow_group_member
#print axioms class_into_canonical
#print axioms class_isolation
#print axioms scaled_isolation
end Fresh.NativeCapturedReversalFamily
