import Fresh.NativePhaseOriginLevels
import Fresh.NativeUpperPairArrangement

/-! A current capture group whose origin-relative levels are below three
selected levels. Origin labels remain independent; no predecessor move from
that origin and no shared own-opening cohort are supplied. Native retained
entry faces discharge readers currently outside the group. -/
namespace Fresh.NativePhaseOriginArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeCanonicalReturn
  Fresh.NativeFixedPrefixArrangement Fresh.NativePhaseOriginLevels Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (W T t : ℝ) (g : Fin 8) (N : ℤ),
    0<W ∧ W ≤ T ∧ 0<t ∧ t<1/4 ∧ g≠k ∧
    reading v k g*W=(N : ℝ)-1/8+t ∧ InWay (reading v k g) T ∧
    IsMove (disparitySet v k) T (handoffOpening v k T g) ∧
    ∀ i : Fin 8,i≠k →
      (InWay (reading v k i) T ∧ ∃ M : ℤ,
        reading v k i*W=(M : ℝ)-1/8+t ∧
        advance (reading v k i) W T<3*advance (reading v k g) W T) ∨
      ((label (reading v k i*T) : ℝ)+1/8 ≤ reading v k i*T ∧
        reading v k i*((label (reading v k g*T) : ℝ)+1/8-reading v k g*T) ≤
          reading v k g*((label (reading v k i*T) : ℝ)+7/8-reading v k i*T))

theorem class_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : CanonicalReturnClass v k := by
  obtain ⟨hv,W,T,t,g,N,hW,hWT,ht,ht',hg,hog,hwg,hm,hreaders⟩ := h
  have hgp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have hstep := captured_labelled_advance (reading v k g) T hgp hwg
  change 0<handoffOpening v k T g-T ∧ _ at hstep
  have ho := handoff_identity hv k g T hg
  have hpoint : IsolatedAt v k (handoffOpening v k T g) := by
    apply (isolatedAt_iff_lonelyAt v k _).2
    intro d hd
    obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hd
    change 1/8 ≤ distInt (reading v k i*handoffOpening v k T g)
    rcases hreaders i hi with ⟨hwi,M,hoi,hle⟩|⟨hlo,hface⟩
    · have hz := triple_level_zero hv k W T t i g M N hi hg hWT ht ht' hoi hog hwi hwg hle hm
      exact nonreturning_clear hv k T _ hm i hi hz
    · have hw := Fresh.NativeOpeningRetention.weighted_window (reading v k g) (reading v k i)
        T (handoffOpening v k T g) (label (reading v k g*T)) (label (reading v k i*T)) hgp
        (show 0 ≤ reading v k i from abs_nonneg _) (by linarith only [hstep.1]) ho hlo hface
      exact clear_of_window _ hw.1 hw.2
  exact canonical_of_isolating_move hv k T _ (hW.trans_le hWT) (by linarith only [hstep.1]) hm hpoint

theorem class_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : Isolation v k :=
  canonical_isolation (class_into_canonical h)

-- STANDING: DEFINITION
noncomputable def ScaledClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ c : ℝ,0<c ∧ Class (fun i=>c*v i) k

theorem scaled_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) : Isolation v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact Fresh.ProvedTypesScale.Isolation_smul_of hc (class_isolation hbase)

#print axioms class_into_canonical
#print axioms class_isolation
#print axioms scaled_isolation
end Fresh.NativePhaseOriginArrangement
