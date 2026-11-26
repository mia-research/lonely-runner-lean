import Fresh.NativeFixedPrefixArrangement

/-! Group endpoint recovery and exact restart reductions. Supplied subgroup
histories need not be full-cascade visits. No termination or move bound. -/
open Classical
namespace Fresh.NativeGroupEndpointRecovery
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeOneReaderDeformation Fresh.NativeReturnSurvivors Fresh.NativeFixedPrefixTransport
  Fresh.NativeFixedPrefixArrangement Fresh.NativeCanonicalReturn

theorem endpoint_clear_preserves_move {ds added : Finset ℝ}
    (hp : ∀ d∈ds,0<d) (ha : ∀ d∈added,0<d) (U R : ℝ)
    (hm : IsMove ds U R) (hc : ∀ d∈added,¬InWay d R) :
    IsMove (ds∪added) U R := by
  apply (union_move_iff hp ha U R hm).2
  intro d hd
  have hUR := le_of_isMove hp hm
  have hl := label_monotone (mul_le_mul_of_nonneg_left hUR (ha d hd).le)
  have hlR : (label (d*U) : ℝ) ≤ (label (d*R) : ℝ) := by exact_mod_cast hl
  have hlo := le_of_not_gt (fun h=>(hc d hd) ((inWay_iff_lower_not_passed d R).2 h))
  linarith only [hlR,hlo]

theorem endpoint_union_lonely {ds added : Finset ℝ} {R : ℝ}
    (hg : LonelyAt ds R) (ha : ∀ d∈added,¬InWay d R) : LonelyAt (ds∪added) R := by
  intro d hd
  rcases Finset.mem_union.mp hd with hd|hd
  · exact hg d hd
  · exact not_lt.mp (ha d hd)

theorem subgroup_prefix_lower_bound {ds whole : Finset ℝ}
    (hp : ∀ d∈ds,0<d) (hsub : ds ⊆ whole) (C t : ℝ) (N : ℕ)
    (hCt : C≤t) (ht : LonelyAt whole t) : cascadeSeq ds C N ≤ t := by
  exact seq_le_of_lonely hp (fun d hd=>ht d (hsub hd))
    (by simpa only [cascadeSeq_zero] using hCt) (cascadeSeq_isMove ds C) N

-- Equivalence of future isolation questions; does not assert existence.
theorem restart_future_iff {ds whole : Finset ℝ}
    (hp : ∀ d∈ds,0<d) (hsub : ds ⊆ whole) (C : ℝ) (N : ℕ) :
    (∃ t,C≤t ∧ LonelyAt whole t) ↔
      ∃ t,cascadeSeq ds C N≤t ∧ LonelyAt whole t := by
  constructor
  · rintro ⟨t,hCt,ht⟩
    exact ⟨t,subgroup_prefix_lower_bound hp hsub C t N hCt ht,ht⟩
  · rintro ⟨t,hRt,ht⟩
    have hCR : C≤cascadeSeq ds C N := by
      simpa only [cascadeSeq_zero] using start_le_seq hp (cascadeSeq_isMove ds C) N
    exact ⟨t,hCR.trans hRt,ht⟩

-- Both finite endpoints are supplied; the restart need not have been visited.
theorem restart_isolated_endpoints_equal {ds whole : Finset ℝ}
    (hp : ∀ d∈ds,0<d) (hw : ∀ d∈whole,0<d) (hsub : ds ⊆ whole)
    (C : ℝ) (N M K : ℕ)
    (hF : LonelyAt whole (cascadeSeq whole C M))
    (hT : LonelyAt whole (cascadeSeq whole (cascadeSeq ds C N) K)) :
    cascadeSeq whole C M = cascadeSeq whole (cascadeSeq ds C N) K := by
  have hCF : C≤cascadeSeq whole C M := by
    simpa only [cascadeSeq_zero] using start_le_seq hw (cascadeSeq_isMove whole C) M
  have hRF := subgroup_prefix_lower_bound hp hsub C _ N hCF hF
  have hCR : C≤cascadeSeq ds C N := by
    simpa only [cascadeSeq_zero] using start_le_seq hp (cascadeSeq_isMove ds C) N
  have hRT : cascadeSeq ds C N≤cascadeSeq whole (cascadeSeq ds C N) K := by
    simpa only [cascadeSeq_zero] using start_le_seq hw (cascadeSeq_isMove whole (cascadeSeq ds C N)) K
  apply le_antisymm
  · exact seq_le_of_lonely hw hT (by simpa only [cascadeSeq_zero] using hCR.trans hRT)
      (cascadeSeq_isMove whole C) M
  · exact seq_le_of_lonely hw hF (by simpa only [cascadeSeq_zero] using hRF)
      (cascadeSeq_isMove whole (cascadeSeq ds C N)) K

-- STANDING: DEFINITION
noncomputable def GroupEndpointClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (I : Finset (Fin 8)) (C : ℝ) (N : ℕ),
    I ⊆ Finset.univ.erase k ∧ I≠Finset.univ.erase k ∧ 0<C ∧ 0<N ∧
    cascadeSeq (part v k I) C (N-1)<cascadeSeq (part v k I) C N ∧
    LonelyAt (part v k I) (cascadeSeq (part v k I) C N) ∧
    (∀ d∈outside v k I,¬InWay d (cascadeSeq (part v k I) C N))

theorem groupEndpoint_into_canonical {v : Fin 8 → ℝ} {k : Fin 8}
    (h : GroupEndpointClass v k) : CanonicalReturnClass v k := by
  obtain ⟨hv,I,C,N,hI,hproper,hC,hN,hstrict,hgroup,hout⟩ := h
  have hp := part_pos hv k I hI
  have hlast : N-1+1=N := by omega
  have hm := cascadeSeq_isMove (part v k I) C (N-1)
  rw [hlast] at hm
  have hf := endpoint_clear_preserves_move hp (outside_pos hv k I) _ _ hm hout
  have hc := endpoint_union_lonely hgroup hout
  rw [part_union_outside v k I hI] at hf hc
  have hU : 0<cascadeSeq (part v k I) C (N-1) := lt_of_lt_of_le hC (by
    simpa only [cascadeSeq_zero] using start_le_seq hp (cascadeSeq_isMove (part v k I) C) (N-1))
  exact canonical_of_isolating_move hv k _ _ hU hstrict hf ((isolatedAt_iff_lonelyAt v k _).2 hc)

theorem groupEndpoint_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : GroupEndpointClass v k) : Isolation v k :=
  canonical_isolation (groupEndpoint_into_canonical h)

theorem prefixRecovery_into_groupEndpoint {v : Fin 8 → ℝ} {k : Fin 8}
    (h : PrefixRecoveryClass v k) : GroupEndpointClass v k := by
  obtain ⟨hv,I,C,N,hI,hproper,hC,hN,hstrict,_hfaces,hgroup,hout⟩ := h
  exact ⟨hv,I,C,N,hI,hproper,hC,hN,hstrict,hgroup,hout⟩

theorem closingGuard_into_groupEndpoint {v : Fin 8 → ℝ} {k : Fin 8}
    (h : ClosingGuardClass v k) : GroupEndpointClass v k :=
  prefixRecovery_into_groupEndpoint (closingGuard_into_prefixRecovery h)

theorem tailInterval_into_groupEndpoint {v : Fin 8 → ℝ} {k : Fin 8}
    (h : TailIntervalClass v k) : GroupEndpointClass v k :=
  prefixRecovery_into_groupEndpoint (tailInterval_into_prefixRecovery h)

theorem endpoint_capture_outside {v : Fin 8 → ℝ} {k : Fin 8}
    (I : Finset (Fin 8)) (R : ℝ) (hgroup : LonelyAt (part v k I) R)
    (i : Fin 8) (hcap : InWay (reading v k i) R) : i∉I := by
  intro hi
  exact not_lt_of_ge (hgroup _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)) hcap

theorem physical_restart_future_iff {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k : Fin 8) (I : Finset (Fin 8)) (hI : I ⊆ Finset.univ.erase k) (C : ℝ) (N : ℕ) :
    (∃ t,C≤t ∧ IsolatedAt v k t) ↔
      ∃ t,cascadeSeq (part v k I) C N≤t ∧ IsolatedAt v k t := by
  have hsub : part v k I ⊆ disparitySet v k := by
    rw [←part_union_outside v k I hI]
    exact Finset.subset_union_left
  simpa only [isolatedAt_iff_lonelyAt] using restart_future_iff (part_pos hv k I hI) hsub C N

#print axioms endpoint_clear_preserves_move
#print axioms endpoint_union_lonely
#print axioms subgroup_prefix_lower_bound
#print axioms restart_future_iff
#print axioms restart_isolated_endpoints_equal
#print axioms groupEndpoint_into_canonical
#print axioms groupEndpoint_isolation
#print axioms prefixRecovery_into_groupEndpoint
#print axioms closingGuard_into_groupEndpoint
#print axioms tailInterval_into_groupEndpoint
#print axioms endpoint_capture_outside
#print axioms physical_restart_future_iff
end Fresh.NativeGroupEndpointRecovery
