import Fresh.NativeUpperTripleTail

/-! Three independent upper reading values with no ratio or return-advance
bound. The tighter native slow window retains through a fresh or old third
return. Physical reading aliases remain allowed. -/
namespace Fresh.NativeUpperTripleArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeDoubleGridRecovery
  Fresh.NativeUpperGridPacket Fresh.NativeCanonicalReturn Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def Slow (s d V : ℝ) : Prop :=
  2*s ≤ d ∧ ∃ J : ℤ,(J : ℝ)+1/8 ≤ s*V ∧ s*V ≤ (J : ℝ)+55/72

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (V : ℝ) (u a b c : Fin 8) (K H A B : ℤ),
    u≠k ∧ a≠k ∧ b≠k ∧ c≠k ∧ 1 ≤ K ∧ 1 ≤ H ∧ 1 ≤ A ∧ 1 ≤ B ∧
    reading v k u*V=(K : ℝ) ∧ reading v k a*V=8*(H : ℝ)*(K : ℝ)+7/8 ∧
    reading v k b*V=8*(A : ℝ)*(K : ℝ)+7/8 ∧ reading v k c*V=8*(B : ℝ)*(K : ℝ)+7/8 ∧
    reading v k a ≤ reading v k b ∧ reading v k a ≤ reading v k c ∧
    ∀ s : Fin 8,s≠k → reading v k s∉({reading v k u,reading v k a,reading v k b,reading v k c} : Finset ℝ) →
      Slow (reading v k s) (reading v k u) V

theorem class_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : CanonicalReturnClass v k := by
  obtain ⟨hv,V,u,a,b,c,K,H,A,B,hu,ha,hb,hc,hK,hH,hA,hB,hdV,hpV,hqV,hrV,hpq,hpr,hslow⟩ := h
  have hd : 0<reading v k u := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨u,hu,rfl⟩)
  have hp : 0<reading v k a := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hq : 0<reading v k b := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨b,hb,rfl⟩)
  have hr : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc,rfl⟩)
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hHr : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hV : 0<V := by nlinarith only [hdV,hKr,hd]
  have hprod := mul_nonneg (sub_nonneg.mpr hHr) (sub_nonneg.mpr hKr)
  have hbig : 1<reading v k a*V := by nlinarith only [hpV,hprod,hHr,hKr]
  have hfast := upper_fast (reading v k u) (reading v k a) V K H hd hK hH hdV hpV
  have ht : 0<7/(64*(K : ℝ)) := by positivity
  have ht' : 7/(64*(K : ℝ))<1/4 := by
    apply (div_lt_iff₀ (by positivity : 0<64*(K : ℝ))).2
    linarith only [hKr]
  have hpW := (upper_return (reading v k u) (reading v k a) V K H hd hK hdV hpV).1
  have hqW := (upper_return (reading v k u) (reading v k b) V K A hd hK hdV hqV).1
  have hrW := (upper_return (reading v k u) (reading v k c) V K B hd hK hdV hrV).1
  obtain ⟨F,z,L,hz,hVF,hown,hcore,hretained⟩ := Fresh.NativeUpperTripleTail.three_resolution
    (reading v k u) (reading v k a) (reading v k b) (reading v k c) V (7/(64*(K : ℝ)))
    K (8*H*K+H+1) (8*A*K+A+1) (8*B*K+B+1) hd hp hq hr hfast hpq hpr ht ht' hdV hpW hqW hrW
  have hzpos : 0<z := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with he|he|he <;> subst z <;> assumption
  have hzmin : reading v k a ≤ z := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with he|he|he
    · exact he ▸ le_rfl
    · exact he ▸ hpq
    · exact he ▸ hpr
  have hL : 0<L := by
    have hm := mul_le_mul_of_nonneg_right hzmin hV.le
    have hstep := mul_pos hzpos (sub_pos.mpr hVF)
    have hl : (0 : ℝ)<(L : ℝ) := by nlinarith only [hm,hstep,hbig,hown]
    exact_mod_cast hl
  obtain ⟨w,hw,hwz⟩ : ∃ w : Fin 8,w≠k ∧ reading v k w=z := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with he|he|he
    · exact ⟨a,ha,he.symm⟩
    · exact ⟨b,hb,he.symm⟩
    · exact ⟨c,hc,he.symm⟩
  apply Fresh.NativeArbitraryThirdReversal.anchored_point_into_canonical hv k w F L hw hL
    (by rw [hwz]; exact hown)
  apply (isolatedAt_iff_lonelyAt v k F).2
  intro d hmem
  obtain ⟨s,hs,rfl⟩ := mem_disparitySet.mp hmem
  change 1/8 ≤ distInt (reading v k s*F)
  by_cases hm : reading v k s∈({reading v k u,reading v k a,reading v k b,reading v k c} : Finset ℝ)
  · exact hcore _ hm
  · obtain ⟨hspeed,J,hlo,hhi⟩ := hslow s hs hm
    have hw := hretained _ J (show 0 ≤ reading v k s from abs_nonneg _) hspeed hlo hhi
    exact clear_of_window J hw.1 hw.2.le

theorem class_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : Isolation v k :=
  canonical_isolation (class_into_canonical h)

-- STANDING: DEFINITION
noncomputable def ScaledClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ c : ℝ,0<c ∧ Class (fun i=>c*v i) k

theorem scaled_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) : Isolation v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact Fresh.ProvedTypesScale.Isolation_smul_of hc (class_isolation hbase)

-- STANDING: DEFINITION
noncomputable def ReturnedClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (R : ℝ) (g j i u a b c : Fin 8) (K H A B : ℤ),
    0<R ∧ g≠k ∧ j≠k ∧ i≠k ∧ u≠k ∧ a≠k ∧ b≠k ∧ c≠k ∧
    3*reading v k g ≤ 5*reading v k j ∧
    3*reading v k j ≤ 5*reading v k g ∧
    InWay (reading v k g) R ∧ InWay (reading v k j) (handoffOpening v k R g) ∧
    InWay (reading v k i) R ∧ handoffOpening v k R i ≤ handoffOpening v k R g ∧
    InWay (reading v k i) (handoffOpening v k (handoffOpening v k R g) j) ∧
    1 ≤ K ∧ 1 ≤ H ∧ 1 ≤ A ∧ 1 ≤ B ∧ 2*label (reading v k i*handoffOpening v k (handoffOpening v k R g) j)+1 ≤ K ∧
    reading v k u*handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i=(K : ℝ) ∧
    reading v k a*handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i=8*(H : ℝ)*(K : ℝ)+7/8 ∧
    reading v k b*handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i=8*(A : ℝ)*(K : ℝ)+7/8 ∧
    reading v k c*handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i=8*(B : ℝ)*(K : ℝ)+7/8 ∧
    reading v k a ≤ reading v k b ∧ reading v k a ≤ reading v k c ∧
    ∀ q : Fin 8,q≠k → reading v k q∉({reading v k g,reading v k j,reading v k i,reading v k u} : Finset ℝ) →
      (1/8 ≤ reading v k q*handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i ∧
        reading v k q*handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i ≤ 1/2) ∨
      reading v k q=reading v k a ∨ reading v k q=reading v k b ∨ reading v k q=reading v k c

theorem returned_into_class {v : Fin 8 → ℝ} {k : Fin 8} (h : ReturnedClass v k) : Class v k := by
  obtain ⟨hv,R,g,j,i,u,a,b,c,K,H,A,B,_hR,hg,hj,hi,hu,ha,hb,hc,hgj,hjg,hwg,hwj,hwi,horder,hret,hK,hH,hA,hB,hlarge,hdV,hpV,hqV,hrV,hpq,hpr,houtside⟩ := h
  let V := handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i
  have hgp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have hjp : 0<reading v k j := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨j,hj,rfl⟩)
  have hip : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  have hdp : 0<reading v k u := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨u,hu,rfl⟩)
  have hmargin := Fresh.NativeTightReboundCore.core_window (reading v k g) (reading v k j) (reading v k i) R hgp hjp hip
    hgj hjg hwg hwj hwi horder hret
  change ∀ q∈({reading v k g,reading v k j,reading v k i} : Finset ℝ),q ≤ reading v k i ∧
    ∃ J : ℤ,(J : ℝ)+1/8 ≤ q*V ∧ q*V ≤ (J : ℝ)+55/72 at hmargin
  change reading v k u*V=(K : ℝ) at hdV
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hV : 0<V := by nlinarith only [hdV,hKr,hdp]
  have hsV := handoff_identity hv k i (handoffOpening v k (handoffOpening v k R g) j) hi
  change reading v k i*V=(label (reading v k i*handoffOpening v k (handoffOpening v k R g) j) : ℝ)+1/8 at hsV
  have hlargeR : 2*(label (reading v k i*handoffOpening v k (handoffOpening v k R g) j) : ℝ)+1 ≤ (K : ℝ) := by exact_mod_cast hlarge
  have hspeed : 2*reading v k i ≤ reading v k u := by nlinarith only [hsV,hdV,hlargeR,hV]
  refine ⟨hv,V,u,a,b,c,K,H,A,B,hu,ha,hb,hc,hK,hH,hA,hB,hdV,hpV,hqV,hrV,hpq,hpr,?_⟩
  intro q hq hnot
  have hnd : reading v k q≠reading v k u := by
    intro he
    exact hnot (by simp only [Finset.mem_insert,Finset.mem_singleton]; exact Or.inl he)
  by_cases hcore : reading v k q∈({reading v k g,reading v k j,reading v k i} : Finset ℝ)
  · obtain ⟨hle,J,hlo,hhi⟩ := hmargin _ hcore
    exact ⟨by linarith only [hle,hspeed],J,hlo,hhi⟩
  have hnotcore : reading v k q∉({reading v k g,reading v k j,reading v k i,reading v k u} : Finset ℝ) := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hcore ⊢
    tauto
  rcases houtside q hq hnotcore with hquiet|he|he|he
  · change 1/8 ≤ reading v k q*V ∧ reading v k q*V ≤ 1/2 at hquiet
    have hr : 2*reading v k q ≤ reading v k u := by nlinarith only [hquiet.2,hdV,hKr,hV]
    exact ⟨hr,0,by simpa using hquiet.1,by norm_num; linarith only [hquiet.2]⟩
  · exact (hnot (by simp only [Finset.mem_insert,Finset.mem_singleton]; exact Or.inr (Or.inl he))).elim
  · exact (hnot (by simp only [Finset.mem_insert,Finset.mem_singleton]; exact Or.inr (Or.inr (Or.inl he)))).elim
  · exact (hnot (by simp only [Finset.mem_insert,Finset.mem_singleton]; exact Or.inr (Or.inr (Or.inr he)))).elim

theorem returned_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ReturnedClass v k) : Isolation v k :=
  class_isolation (returned_into_class h)

-- STANDING: DEFINITION
noncomputable def ReturnedScaledClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ c : ℝ,0<c ∧ ReturnedClass (fun i=>c*v i) k

theorem returned_scaled_into_scaled {v : Fin 8 → ℝ} {k : Fin 8}
    (h : ReturnedScaledClass v k) : ScaledClass v k := by
  obtain ⟨hv,c,hc,hbase⟩ := h
  exact ⟨hv,c,hc,returned_into_class hbase⟩

theorem returned_scaled_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : ReturnedScaledClass v k) : Isolation v k := scaled_isolation (returned_scaled_into_scaled h)

#print axioms returned_into_class
#print axioms returned_isolation
#print axioms returned_scaled_into_scaled
#print axioms returned_scaled_isolation

#print axioms class_into_canonical
#print axioms class_isolation
#print axioms scaled_isolation
end Fresh.NativeUpperTripleArrangement
