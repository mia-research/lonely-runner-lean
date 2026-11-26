import Fresh.NativeFastSecondFourthArrangement

/-! Coalescence of the native small-fourth families across the complete
second/third relative-speed trichotomy. First-entry captures, the integer
anchor and initial slow windows remain explicit local hypotheses. -/
namespace Fresh.NativeSmallFourthArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeThirdReaderRebound
  Fresh.NativeUpperGridPacket Fresh.NativeCanonicalReturn Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (V t : ℝ) (u a b c e : Fin 8) (K M N : ℤ),
    u≠k ∧ a≠k ∧ b≠k ∧ c≠k ∧ e≠k ∧ 1 ≤ K ∧ 0<t ∧ t<1/4 ∧
    reading v k u*V=(K : ℝ) ∧ 8*reading v k u ≤ reading v k a ∧
    reading v k a ≤ reading v k b ∧ reading v k a ≤ reading v k e ∧
    reading v k e ≤ reading v k b ∧ reading v k e ≤ reading v k c ∧
    let W := V+1/(8*reading v k u)
    let Z := labelledOpening (reading v k a) W
    let Y := labelledOpening (reading v k b) Z
    reading v k a*W=(M : ℝ)-1/8+t ∧ reading v k b*W=(N : ℝ)-1/8+t ∧
    InWay (reading v k b) Z ∧ InWay (reading v k c) Y ∧
    ∀ i : Fin 8,i≠k → reading v k i∉({reading v k u,reading v k a,reading v k b,reading v k c,reading v k e} : Finset ℝ) →
      2*reading v k i ≤ reading v k u ∧ ∃ J : ℤ,(J : ℝ)+1/8 ≤ reading v k i*V ∧ reading v k i*V ≤ (J : ℝ)+3/4

theorem class_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : CanonicalReturnClass v k := by
  obtain ⟨hv,V,t,u,a,b,c,e,K,M,N,hu,ha,hb,hc,he,hK,ht,ht',hdV,hfast,hpq,hps,hsq,hsr,hframe⟩ := h
  by_cases hqr : 3*reading v k b<reading v k c
  · exact Fresh.NativeHierarchicalFourthArrangement.class_into_canonical
      ⟨hv,V,t,u,a,b,c,e,K,M,N,hu,ha,hb,hc,he,hK,ht,ht',hdV,hfast,hpq,hps,hqr,hframe⟩
  by_cases hrq : 3*reading v k c<reading v k b
  · exact Fresh.NativeFastSecondFourthArrangement.class_into_canonical
      ⟨hv,V,t,u,a,b,c,e,K,M,N,hu,ha,hb,hc,he,hK,ht,ht',hdV,hfast,hpq,hps,hrq,hsr,hframe⟩
  · exact Fresh.NativeComparableFourthArrangement.class_into_canonical
      ⟨hv,V,t,u,a,b,c,e,K,M,N,hu,ha,hb,hc,he,hK,ht,ht',hdV,hfast,hpq,hps,
        le_of_not_gt hrq,le_of_not_gt hqr,hsq,hsr,hframe⟩

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
end Fresh.NativeSmallFourthArrangement
