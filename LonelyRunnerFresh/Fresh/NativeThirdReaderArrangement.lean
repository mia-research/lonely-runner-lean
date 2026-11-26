import Fresh.NativeThirdReaderRetention

/-! Three-reader continuation families. Clearance of the old reader is
proved from the composed face; all remaining physical duties stay explicit.
No assumption that larger recurrences stop is introduced. -/
open Classical
namespace Fresh.NativeThirdReaderArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeCoalescedCaptureRelay Fresh.NativeFixedPrefixTransport Fresh.FastestCaptureRetention
  Fresh.NativeFixedPrefixArrangement Fresh.NativeGroupEndpointRecovery Fresh.NativeCanonicalReturn
  Fresh.NativeOpeningReversal Fresh.NativeThirdReaderRetention

-- STANDING: DEFINITION
noncomputable def TripleRecoveryClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (a b c : Fin 8) (C : ℝ) (M : ℤ),
    a≠k ∧ b≠k ∧ c≠k ∧ a≠b ∧ a≠c ∧ b≠c ∧ 0<C ∧
    reading v k b*C=(M : ℝ)+1/8 ∧ InWay (reading v k a) C ∧
    InWay (reading v k c) (labelledOpening (reading v k a) C) ∧
    reading v k a*reading v k b+2*reading v k b*reading v k c ≤ 3*reading v k a*reading v k c ∧
    (∀ d∈outside v k {a,b,c},¬InWay d (thirdEnd (reading v k a) (reading v k c) C))

theorem tripleRecovery_into_canonical {v : Fin 8 → ℝ} {k : Fin 8}
    (h : TripleRecoveryClass v k) : CanonicalReturnClass v k := by
  obtain ⟨hv,a,b,c,C,M,ha,hb,hc,hab,hac,hbc,hC,ho,hw,hthird,hfit,hout⟩ := h
  have hI : ({a,b,c} : Finset (Fin 8)) ⊆ Finset.univ.erase k := by
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with he|he|he
    all_goals subst i; simp_all
  have hpa := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hpb := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨b,hb,rfl⟩)
  have hpc := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc,rfl⟩)
  let E := labelledOpening (reading v k a) C
  have hCE := (captured_labelled_advance _ C hpa hw).1
  have hp := pair_last_move_and_clear (reading v k a) (reading v k c) E (label (reading v k a*C))
    hpa hpc (labelled_opening_identity _ C hpa) hthird
  obtain ⟨U,hEU,hUT,hm⟩ := hp.1
  have hclearTriple := triple_clear _ _ _ C M hpa hpb hpc ho hw hthird hfit
  have hpart : part v k {a,b,c}={reading v k a,reading v k b,reading v k c} := by simp [part]
  have hgroup : LonelyAt (part v k {a,b,c}) (thirdEnd (reading v k a) (reading v k c) C) := by
    simpa only [hpart] using hclearTriple
  have hclear := endpoint_union_lonely hgroup hout
  rw [part_union_outside v k {a,b,c} hI] at hclear
  have hsub : ({reading v k a,reading v k c} : Finset ℝ) ⊆ disparitySet v k := by
    intro d hd
    rcases Finset.mem_insert.mp hd with he|hd
    · subst d; exact mem_disparitySet.mpr ⟨a,ha,rfl⟩
    · rw [Finset.mem_singleton.mp hd]; exact mem_disparitySet.mpr ⟨c,hc,rfl⟩
  have hrest : ∀ d∈disparitySet v k\{reading v k a,reading v k c},¬InWay d (thirdEnd (reading v k a) (reading v k c) C) :=
    fun d hd=>not_lt.mpr (hclear d (Finset.mem_sdiff.mp hd).1)
  have hfull := endpoint_clear_preserves_move (fun d hd=>disparitySet_pos hv k d (hsub hd))
    (fun d hd=>disparitySet_pos hv k d (Finset.mem_sdiff.mp hd).1) _ _ hm hrest
  rw [Finset.union_sdiff_of_subset hsub] at hfull
  have hposE : 0<E := by
    change 0<E-C at hCE
    linarith only [hC,hCE]
  exact canonical_of_isolating_move hv k _ _ (hposE.trans_le hEU) hUT hfull
    ((isolatedAt_iff_lonelyAt v k _).2 hclear)

theorem tripleRecovery_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : TripleRecoveryClass v k) : Isolation v k := canonical_isolation (tripleRecovery_into_canonical h)

-- STANDING: DEFINITION
noncomputable def SimpleTripleClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (a b c : Fin 8) (C : ℝ) (M : ℤ),
    a≠k ∧ b≠k ∧ c≠k ∧ a≠b ∧ a≠c ∧ b≠c ∧ 0<C ∧
    reading v k b*C=(M : ℝ)+1/8 ∧ InWay (reading v k a) C ∧
    InWay (reading v k c) (labelledOpening (reading v k a) C) ∧
    3*reading v k b<reading v k a ∧ 3*reading v k b ≤ 7*reading v k c ∧
    (∀ d∈outside v k {a,b,c},¬InWay d (thirdEnd (reading v k a) (reading v k c) C))

theorem simpleTriple_into_recovery {v : Fin 8 → ℝ} {k : Fin 8}
    (h : SimpleTripleClass v k) : TripleRecoveryClass v k := by
  obtain ⟨hv,a,b,c,C,M,ha,hb,hc,hab,hac,hbc,hC,ho,hw,hthird,hr,hseven,hout⟩ := h
  have hpa := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hpc := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc,rfl⟩)
  exact ⟨hv,a,b,c,C,M,ha,hb,hc,hab,hac,hbc,hC,ho,hw,hthird,
    simple_seven_three_fit _ _ _ hpa hpc hr hseven,hout⟩

-- STANDING: DEFINITION
noncomputable def TripleGuardClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (a b c : Fin 8) (C f : ℝ) (M : ℤ),
    a≠k ∧ b≠k ∧ c≠k ∧ a≠b ∧ a≠c ∧ b≠c ∧ 0<C ∧
    reading v k b*C=(M : ℝ)+1/8 ∧ InWay (reading v k a) C ∧
    InWay (reading v k c) (labelledOpening (reading v k a) C) ∧
    reading v k a*reading v k b+2*reading v k b*reading v k c ≤ 3*reading v k a*reading v k c ∧
    f∈outside v k {a,b,c} ∧
    (∀ d∈outside v k {a,b,c},¬InWay d (labelledOpening (reading v k a) C)) ∧
    (∀ d∈outside v k {a,b,c},closing f (labelledOpening (reading v k a) C) ≤ closing d (labelledOpening (reading v k a) C)) ∧
    thirdEnd (reading v k a) (reading v k c) C ≤ closing f (labelledOpening (reading v k a) C)

theorem tripleGuard_into_recovery {v : Fin 8 → ℝ} {k : Fin 8}
    (h : TripleGuardClass v k) : TripleRecoveryClass v k := by
  obtain ⟨hv,a,b,c,C,f,M,ha,hb,hc,hab,hac,hbc,hC,ho,hw,hthird,hfit,hf,hclear,hfirst,hend⟩ := h
  have hpa := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hpc := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc,rfl⟩)
  have hET := pair_end_after _ _ (labelledOpening (reading v k a) C) hpa hpc _
    (labelled_opening_identity _ C hpa) hthird
  refine ⟨hv,a,b,c,C,M,ha,hb,hc,hab,hac,hbc,hC,ho,hw,hthird,hfit,?_⟩
  intro d hd
  have hp := outside_pos hv k {a,b,c} d hd
  have hlo := le_of_not_gt (fun hh=>(hclear d hd) ((inWay_iff_lower_not_passed _ _).2 hh))
  have hu := (le_div_iff₀ hp).1 (hend.trans (hfirst d hd))
  have hu' : d*thirdEnd (reading v k a) (reading v k c) C ≤
      (label (d*labelledOpening (reading v k a) C) : ℝ)+7/8 := by
    simpa only [closing,mul_comm] using hu
  exact (band_at_point d _ _ _ _ hp.le hET.le le_rfl hlo hu').1

theorem triple_endpoint_captures_outside {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k a b c : Fin 8) (C : ℝ) (M : ℤ) (ha : a≠k) (hb : b≠k) (hc : c≠k)
    (ho : reading v k b*C=(M : ℝ)+1/8) (hw : InWay (reading v k a) C)
    (hthird : InWay (reading v k c) (labelledOpening (reading v k a) C))
    (hfit : reading v k a*reading v k b+2*reading v k b*reading v k c ≤ 3*reading v k a*reading v k c)
    (i : Fin 8) (hi : InWay (reading v k i) (thirdEnd (reading v k a) (reading v k c) C)) :
    i≠a ∧ i≠b ∧ i≠c := by
  have hpa := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hpb := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨b,hb,rfl⟩)
  have hpc := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc,rfl⟩)
  have ht := triple_clear _ _ _ C M hpa hpb hpc ho hw hthird hfit
  have hn : i∉({a,b,c} : Finset (Fin 8)) := by
    intro hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with he|he|he
    all_goals subst i; exact not_lt_of_ge (ht _ (by simp [reading])) hi
  simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hn

-- The old partner's reciprocal opening interval supplies all the state
-- hypotheses needed for a common third-reader landing.
theorem interval_opening_states (a lo hi : ℝ) (M L : ℤ)
    (ha : 0<a) (hlo : 0<lo) (hM : 0 ≤ (M : ℝ)+1/8)
    (hleft : (L : ℝ)-1/8<a*opening hi M) (hright : a*opening lo M<(L : ℝ)+1/8) :
    ∀ b : ℝ,lo ≤ b → b ≤ hi → b*opening b M=(M : ℝ)+1/8 ∧
      InWay a (opening b M) ∧ labelledOpening a (opening b M)=opening a L := by
  intro b hl hb
  have hpos := hlo.trans_le hl
  have hbounds := interval_opening_bounds lo b hi M hlo hl hb hM
  have hlow := hleft.trans_le (mul_le_mul_of_nonneg_left hbounds.1 ha.le)
  have hhigh := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hbounds.2 ha.le) hright
  have hlabel := (entry_iff_label a (opening b M) L).1 (Or.inr ⟨hlow,hhigh⟩)
  refine ⟨?_,(inWay_iff_lower_not_passed _ _).2 (by rw [hlabel]; exact hhigh),?_⟩
  · dsimp [opening]; field_simp
  · simp only [labelledOpening,hlabel]

-- All old speeds in a band with one common anchor landing share the same
-- third-reader endpoint; one upper speed discharges the composed face.
theorem interval_third_clear (a lo hi c E : ℝ) (C : ℝ → ℝ) (M : ℤ)
    (ha : 0<a) (hlo : 0<lo) (hc : 0<c)
    (hfaces : ∀ b : ℝ,lo ≤ b → b ≤ hi →
      b*C b=(M : ℝ)+1/8 ∧ InWay a (C b) ∧ labelledOpening a (C b)=E)
    (hthird : InWay c E) (hfit : a*hi+2*hi*c ≤ 3*a*c) :
    ∀ b : ℝ,lo ≤ b → b ≤ hi → LonelyAt ({a,b,c} : Finset ℝ) (partnerEnd a c E) := by
  intro b hl hb
  obtain ⟨ho,hw,hE⟩ := hfaces b hl hb
  have ht : InWay c (labelledOpening a (C b)) := by rw [hE]; exact hthird
  have hh := triple_clear a b c (C b) M ha (hlo.trans_le hl) hc ho hw ht
    (old_speed_interval_fit a b hi c ha hc hb hfit)
  simpa only [thirdEnd,hE] using hh

theorem opening_band_third_clear (a lo hi c : ℝ) (M L : ℤ)
    (ha : 0<a) (hlo : 0<lo) (hc : 0<c) (hM : 0 ≤ (M : ℝ)+1/8)
    (hleft : (L : ℝ)-1/8<a*opening hi M) (hright : a*opening lo M<(L : ℝ)+1/8)
    (hthird : InWay c (opening a L)) (hfit : a*hi+2*hi*c ≤ 3*a*c) :
    ∀ b : ℝ,lo ≤ b → b ≤ hi → LonelyAt ({a,b,c} : Finset ℝ) (partnerEnd a c (opening a L)) :=
  interval_third_clear a lo hi c (opening a L) (fun b=>opening b M) M ha hlo hc
    (interval_opening_states a lo hi M L ha hlo hM hleft hright) hthird hfit

#print axioms interval_opening_states
#print axioms opening_band_third_clear

#print axioms tripleRecovery_into_canonical
#print axioms tripleRecovery_isolation
#print axioms simpleTriple_into_recovery
#print axioms tripleGuard_into_recovery
#print axioms triple_endpoint_captures_outside
#print axioms interval_third_clear
end Fresh.NativeThirdReaderArrangement
