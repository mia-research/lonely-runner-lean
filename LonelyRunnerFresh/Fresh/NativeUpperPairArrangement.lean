import Fresh.NativeUpperPairHandoff
import Fresh.NativeUpperGridArrangement

/-! Arbitrary independent upper-grid pair, modulo reading equivalence.
The second reader may cross unbounded labels before recapture. Either the
first opening isolates or the forced faster reader's own opening does. -/
namespace Fresh.NativeUpperPairArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeDoubleGridRecovery
  Fresh.NativeUpperGridPacket Fresh.NativeUpperPairHandoff Fresh.NativeCanonicalReturn Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (V : ℝ) (u a b : Fin 8) (K H A : ℤ),
    u≠k ∧ a≠k ∧ b≠k ∧ 1 ≤ K ∧ 1 ≤ H ∧ 1 ≤ A ∧
    reading v k u*V=(K : ℝ) ∧ reading v k a*V=8*(H : ℝ)*(K : ℝ)+7/8 ∧
    reading v k b*V=8*(A : ℝ)*(K : ℝ)+7/8 ∧ reading v k a ≤ reading v k b ∧
    ∀ s : Fin 8,s≠k → reading v k s∉({reading v k u,reading v k a,reading v k b} : Finset ℝ) →
      Fresh.NativeUpperGridArrangement.Slow (reading v k s) (reading v k u) V

theorem class_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : CanonicalReturnClass v k := by
  obtain ⟨hv,V,u,a,b,K,H,A,hu,ha,hb,hK,hH,hA,hdV,hpV,hqV,hpq,hslow⟩ := h
  have hd : 0<reading v k u := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨u,hu,rfl⟩)
  have hp : 0<reading v k a := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hq : 0<reading v k b := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨b,hb,rfl⟩)
  let W := V+1/(8*reading v k u)
  let Z := labelledOpening (reading v k a) W
  have hrp := upper_return (reading v k u) (reading v k a) V K H hd hK hdV hpV
  have hrq := upper_return (reading v k u) (reading v k b) V K A hd hK hdV hqV
  change reading v k a*W=(8*H*K+H+1 : ℤ)-1/8+7/(64*(K : ℝ)) ∧ _ at hrp
  change reading v k b*W=(8*A*K+A+1 : ℤ)-1/8+7/(64*(K : ℝ)) ∧ _ at hrq
  have hfast := upper_fast (reading v k u) (reading v k a) V K H hd hK hH hdV hpV
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have ht : 0<7/(64*(K : ℝ)) := by positivity
  have ht' : 7/(64*(K : ℝ))<1/4 := by
    apply (div_lt_iff₀ (by positivity : 0<64*(K : ℝ))).2
    linarith only [hKr]
  have hdown := integer_step (reading v k u) V K hd hdV
  have hpown := labelled_opening_identity (reading v k a) W hp
  rw [hrp.2.1] at hpown
  have hM : 0<8*H*K+H+1 := by
    have hh := mul_pos (show 0<8*H by omega) (show 0<K by omega)
    omega
  by_cases hrecap : InWay (reading v k b) Z
  · have hlarge := Fresh.NativeUpperPairHandoff.recapture_fast (reading v k a) (reading v k b) W
      (7/(64*(K : ℝ))) (8*H*K+H+1) (8*A*K+A+1) hp ht ht' hrp.1 hrq.1 hpq hrecap
    have hfastq : 32*reading v k u ≤ reading v k b := by linarith only [hlarge,hfast]
    have hcore := processed_clear (reading v k u) (reading v k a) (reading v k b) V K
      hd hp hq hdV hfast hlarge hrp.2.2.1 hrecap
    have hqown := labelled_opening_identity (reading v k b) Z hq
    have hWZ : W ≤ Z := by
      have hh := (captured_labelled_advance (reading v k a) W hp hrp.2.2.1).1
      change 0<Z-W at hh
      linarith only [hh]
    have hlabel := label_monotone (mul_le_mul_of_nonneg_left hWZ hq.le)
    rw [hrq.2.1] at hlabel
    have hN : 0<label (reading v k b*Z) := by
      have hh := mul_pos (show 0<8*A by omega) (show 0<K by omega)
      omega
    apply Fresh.NativeArbitraryThirdReversal.anchored_point_into_canonical hv k b _ _ hb hN hqown
    apply (isolatedAt_iff_lonelyAt v k _).2
    intro d hmem
    obtain ⟨s,hs,rfl⟩ := mem_disparitySet.mp hmem
    change 1/8 ≤ distInt (reading v k s*labelledOpening (reading v k b) Z)
    by_cases hm : reading v k s∈({reading v k u,reading v k a,reading v k b} : Finset ℝ)
    · exact hcore _ hm
    obtain ⟨hspeed,J,hlo,hhi⟩ := hslow s hs hm
    have hw := slow_recap_window (reading v k u) (reading v k a) (reading v k b) (reading v k s)
      V J hd hp hq (show 0 ≤ reading v k s from abs_nonneg _) hfast hfastq hspeed hrp.2.2.1 hrecap hlo hhi
    exact clear_of_window J hw.1 hw.2.le
  · apply Fresh.NativeArbitraryThirdReversal.anchored_point_into_canonical hv k a Z _ ha hM hpown
    apply (isolatedAt_iff_lonelyAt v k _).2
    intro d hmem
    obtain ⟨s,hs,rfl⟩ := mem_disparitySet.mp hmem
    change 1/8 ≤ distInt (reading v k s*Z)
    by_cases hm : reading v k s∈({reading v k u,reading v k a,reading v k b} : Finset ℝ)
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      rcases hm with he|he|he
      · rw [he]
        have hw := own_opening_retained (reading v k a) (reading v k u) W Z (8*H*K+H+1) K hp hd.le
          (by linarith only [hfast,hp]) hdown hrp.2.2.1 hpown hrp.2.1.symm
        exact clear_of_window K hw.1 hw.2.le
      · rw [he]
        exact clear_of_window _ hpown.ge (by linarith only [hpown])
      · rw [he]
        exact not_lt.mp hrecap
    · obtain ⟨hspeed,J,hlo,hhi⟩ := hslow s hs hm
      have hw := slow_margin (reading v k u) (reading v k a) (reading v k s) V K J hd hp
        (show 0 ≤ reading v k s from abs_nonneg _) hdV hfast hspeed hrp.2.2.1 hlo hhi
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
  IsArrangement v ∧ ∃ (R : ℝ) (g j i u a b : Fin 8) (K H A : ℤ),
    0<R ∧ g≠k ∧ j≠k ∧ i≠k ∧ u≠k ∧ a≠k ∧ b≠k ∧
    3*reading v k i ≤ 5*reading v k g ∧ 3*reading v k g ≤ 5*reading v k j ∧
    3*reading v k j ≤ 5*reading v k g ∧
    InWay (reading v k g) R ∧ InWay (reading v k j) (handoffOpening v k R g) ∧
    InWay (reading v k i) R ∧ handoffOpening v k R i ≤ handoffOpening v k R g ∧
    InWay (reading v k i) (handoffOpening v k (handoffOpening v k R g) j) ∧
    1 ≤ K ∧ 1 ≤ H ∧ 1 ≤ A ∧ 2*label (reading v k i*handoffOpening v k (handoffOpening v k R g) j)+1 ≤ K ∧
    reading v k u*handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i=(K : ℝ) ∧
    reading v k a*handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i=8*(H : ℝ)*(K : ℝ)+7/8 ∧
    reading v k b*handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i=8*(A : ℝ)*(K : ℝ)+7/8 ∧
    reading v k a ≤ reading v k b ∧
    ∀ q : Fin 8,q≠k → reading v k q∉({reading v k g,reading v k j,reading v k i,reading v k u} : Finset ℝ) →
      (1/8 ≤ reading v k q*handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i ∧
        reading v k q*handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i ≤ 1/2) ∨
      reading v k q=reading v k a ∨ reading v k q=reading v k b

theorem returned_into_class {v : Fin 8 → ℝ} {k : Fin 8} (h : ReturnedClass v k) : Class v k := by
  obtain ⟨hv,R,g,j,i,u,a,b,K,H,A,_hR,hg,hj,hi,hu,ha,hb,hsg,hgj,hjg,hwg,hwj,hwi,horder,hret,hK,hH,hA,hlarge,hdV,hpV,hqV,hpq,houtside⟩ := h
  let V := handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i
  have hgp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have hjp : 0<reading v k j := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨j,hj,rfl⟩)
  have hip : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  have hdp : 0<reading v k u := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨u,hu,rfl⟩)
  have hmargin := core_margin (reading v k g) (reading v k j) (reading v k i) R hgp hjp hip
    hsg hgj hjg hwg hwj hwi horder hret
  change ∀ q∈({reading v k g,reading v k j,reading v k i} : Finset ℝ),q ≤ reading v k i ∧
    ∃ J : ℤ,(J : ℝ)+1/8 ≤ q*V ∧ q*V ≤ (J : ℝ)+19/24 at hmargin
  change reading v k u*V=(K : ℝ) at hdV
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hV : 0<V := by nlinarith only [hdV,hKr,hdp]
  have hsV := handoff_identity hv k i (handoffOpening v k (handoffOpening v k R g) j) hi
  change reading v k i*V=(label (reading v k i*handoffOpening v k (handoffOpening v k R g) j) : ℝ)+1/8 at hsV
  have hlargeR : 2*(label (reading v k i*handoffOpening v k (handoffOpening v k R g) j) : ℝ)+1 ≤ (K : ℝ) := by exact_mod_cast hlarge
  have hspeed : 2*reading v k i ≤ reading v k u := by nlinarith only [hsV,hdV,hlargeR,hV]
  refine ⟨hv,V,u,a,b,K,H,A,hu,ha,hb,hK,hH,hA,hdV,hpV,hqV,hpq,?_⟩
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
  rcases houtside q hq hnotcore with hquiet|he|he
  · change 1/8 ≤ reading v k q*V ∧ reading v k q*V ≤ 1/2 at hquiet
    have hr : 2*reading v k q ≤ reading v k u := by nlinarith only [hquiet.2,hdV,hKr,hV]
    exact ⟨hr,0,by simpa using hquiet.1,by norm_num; linarith only [hquiet.2]⟩
  · exact (hnot (by simp only [Finset.mem_insert,Finset.mem_singleton]; exact Or.inr (Or.inl he))).elim
  · exact (hnot (by simp only [Finset.mem_insert,Finset.mem_singleton]; exact Or.inr (Or.inr he))).elim

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
end Fresh.NativeUpperPairArrangement
