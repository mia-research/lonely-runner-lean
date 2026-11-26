import Fresh.NativeThirdReaderArrangement
import Fresh.NativeThirdReaderRebound

/-! The third reader's composed-fit hypothesis is removed by the forced
rebound. Full arrangement recovery or outsider closing guards remain explicit.
Any capture at the derived endpoint must involve a fourth physical reader. -/
open Classical
namespace Fresh.NativeThirdReaderForcedArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeFixedPrefixTransport Fresh.NativeFixedPrefixArrangement Fresh.NativeGroupEndpointRecovery
  Fresh.NativeOpeningReversal Fresh.NativeThirdReaderRetention Fresh.NativeThirdReaderArrangement
  Fresh.NativeThirdReaderRebound Fresh.NativeCanonicalReturn

theorem fitted_forced_end_eq (a b c C : ℝ) (M : ℤ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (ho : b*C=(M : ℝ)+1/8) (hw : InWay a C) (hthird : InWay c (labelledOpening a C))
    (hfit : a*b+2*b*c ≤ 3*a*c) : forcedEnd a b c C=thirdEnd a c C := by
  have hh := old_opening_retained a b c C M ha hb hc ho hw hthird hfit
  have hn : ¬InWay b (thirdEnd a c C) := not_lt.mpr (clear_of_window M hh.1 hh.2.le)
  exact if_neg hn

-- STANDING: DEFINITION
noncomputable def ForcedTripleClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (a b c : Fin 8) (C : ℝ) (M : ℤ),
    a≠k ∧ b≠k ∧ c≠k ∧ a≠b ∧ a≠c ∧ b≠c ∧ 0<C ∧
    reading v k b*C=(M : ℝ)+1/8 ∧ InWay (reading v k a) C ∧
    InWay (reading v k c) (labelledOpening (reading v k a) C) ∧ 3*reading v k b<reading v k a ∧
    (∀ d∈outside v k {a,b,c},¬InWay d (forcedEnd (reading v k a) (reading v k b) (reading v k c) C))

theorem forcedTriple_into_canonical {v : Fin 8 → ℝ} {k : Fin 8}
    (h : ForcedTripleClass v k) : CanonicalReturnClass v k := by
  obtain ⟨hv,a,b,c,C,M,ha,hb,hc,hab,hac,hbc,hC,ho,hw,hthird,hfast,hout⟩ := h
  have hpa := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hpb := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨b,hb,rfl⟩)
  have hpc := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc,rfl⟩)
  obtain ⟨H,U,hH,hCU,hUR,hm,hclear⟩ := forced_triple_resolution _ _ _ C M hpa hpb hpc hfast ho hw hthird
  have hI : ({a,b,c} : Finset (Fin 8)) ⊆ Finset.univ.erase k := by
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with he|he|he
    all_goals subst i; simp_all
  have hgroup : LonelyAt (part v k {a,b,c}) (forcedEnd (reading v k a) (reading v k b) (reading v k c) C) := by
    simpa [part,reading] using hclear
  have hfullclear := endpoint_union_lonely hgroup hout
  rw [part_union_outside v k {a,b,c} hI] at hfullclear
  have hsub : H ⊆ disparitySet v k := by
    intro d hd
    have hx := hH hd
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with he|he|he
    · subst d; exact mem_disparitySet.mpr ⟨a,ha,rfl⟩
    · subst d; exact mem_disparitySet.mpr ⟨b,hb,rfl⟩
    · subst d; exact mem_disparitySet.mpr ⟨c,hc,rfl⟩
  have hrest : ∀ d∈disparitySet v k\H,¬InWay d (forcedEnd (reading v k a) (reading v k b) (reading v k c) C) :=
    fun d hd=>not_lt.mpr (hfullclear d (Finset.mem_sdiff.mp hd).1)
  have hfull := endpoint_clear_preserves_move (fun d hd=>disparitySet_pos hv k d (hsub hd))
    (fun d hd=>disparitySet_pos hv k d (Finset.mem_sdiff.mp hd).1) _ _ hm hrest
  rw [Finset.union_sdiff_of_subset hsub] at hfull
  exact canonical_of_isolating_move hv k _ _ (hC.trans_le hCU) hUR hfull
    ((isolatedAt_iff_lonelyAt v k _).2 hfullclear)

theorem forcedTriple_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : ForcedTripleClass v k) : Isolation v k := canonical_isolation (forcedTriple_into_canonical h)

theorem simpleTriple_into_forced {v : Fin 8 → ℝ} {k : Fin 8}
    (h : SimpleTripleClass v k) : ForcedTripleClass v k := by
  obtain ⟨hv,a,b,c,C,M,ha,hb,hc,hab,hac,hbc,hC,ho,hw,hthird,hfast,hseven,hout⟩ := h
  have hpa := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hpb := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨b,hb,rfl⟩)
  have hpc := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc,rfl⟩)
  have he := fitted_forced_end_eq (reading v k a) (reading v k b) (reading v k c) C M hpa hpb hpc ho hw hthird
    (simple_seven_three_fit _ _ _ hpa hpc hfast hseven)
  refine ⟨hv,a,b,c,C,M,ha,hb,hc,hab,hac,hbc,hC,ho,hw,hthird,hfast,?_⟩
  rw [he]
  exact hout

-- STANDING: DEFINITION
noncomputable def ForcedTripleGuardClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (a b c : Fin 8) (C f : ℝ) (M : ℤ),
    a≠k ∧ b≠k ∧ c≠k ∧ a≠b ∧ a≠c ∧ b≠c ∧ 0<C ∧
    reading v k b*C=(M : ℝ)+1/8 ∧ InWay (reading v k a) C ∧
    InWay (reading v k c) (labelledOpening (reading v k a) C) ∧ 3*reading v k b<reading v k a ∧
    f∈outside v k {a,b,c} ∧ (∀ d∈outside v k {a,b,c},¬InWay d C) ∧
    (∀ d∈outside v k {a,b,c},closing f C ≤ closing d C) ∧
    forcedEnd (reading v k a) (reading v k b) (reading v k c) C ≤ closing f C

theorem forcedTripleGuard_into_forced {v : Fin 8 → ℝ} {k : Fin 8}
    (h : ForcedTripleGuardClass v k) : ForcedTripleClass v k := by
  obtain ⟨hv,a,b,c,C,f,M,ha,hb,hc,hab,hac,hbc,hC,ho,hw,hthird,hfast,hf,hclear,hfirst,hend⟩ := h
  have hpa := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hpb := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨b,hb,rfl⟩)
  have hpc := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc,rfl⟩)
  obtain ⟨H,U,hH,hCU,hUR,hm,htriple⟩ := forced_triple_resolution _ _ _ C M hpa hpb hpc hfast ho hw hthird
  refine ⟨hv,a,b,c,C,M,ha,hb,hc,hab,hac,hbc,hC,ho,hw,hthird,hfast,?_⟩
  intro d hd
  have hp := outside_pos hv k {a,b,c} d hd
  have hlo := le_of_not_gt (fun hh=>(hclear d hd) ((inWay_iff_lower_not_passed _ _).2 hh))
  have hu := (le_div_iff₀ hp).1 (hend.trans (hfirst d hd))
  have hu' : d*forcedEnd (reading v k a) (reading v k b) (reading v k c) C ≤ (label (d*C) : ℝ)+7/8 := by
    simpa only [closing,mul_comm] using hu
  exact (band_at_point d C _ _ _ hp.le (hCU.trans hUR.le) le_rfl hlo hu').1

theorem forced_triple_capture_outside {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k a b c : Fin 8) (C : ℝ) (M : ℤ) (ha : a≠k) (hb : b≠k) (hc : c≠k)
    (ho : reading v k b*C=(M : ℝ)+1/8) (hw : InWay (reading v k a) C)
    (hthird : InWay (reading v k c) (labelledOpening (reading v k a) C))
    (hfast : 3*reading v k b<reading v k a) (i : Fin 8)
    (hi : InWay (reading v k i) (forcedEnd (reading v k a) (reading v k b) (reading v k c) C)) :
    i≠a ∧ i≠b ∧ i≠c := by
  have hpa := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hpb := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨b,hb,rfl⟩)
  have hpc := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc,rfl⟩)
  obtain ⟨H,U,hH,hCU,hUR,hm,hclear⟩ := forced_triple_resolution _ _ _ C M hpa hpb hpc hfast ho hw hthird
  have hn : i∉({a,b,c} : Finset (Fin 8)) := by
    intro hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with he|he|he
    all_goals subst i; exact not_lt_of_ge (hclear _ (by simp [reading])) hi
  simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hn

#print axioms fitted_forced_end_eq
#print axioms forcedTriple_into_canonical
#print axioms forcedTriple_isolation
#print axioms simpleTriple_into_forced
#print axioms forcedTripleGuard_into_forced
#print axioms forced_triple_capture_outside
end Fresh.NativeThirdReaderForcedArrangement
