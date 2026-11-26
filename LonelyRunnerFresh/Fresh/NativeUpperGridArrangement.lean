import Fresh.NativeUpperGridPacket
import Fresh.NativeDoubleGridArrangement

/-! Upper-grid packets recapture after the integer handoff, then their
minimum reading clears the packet and the derived slow core. Earlier
supplied boundaries need not be visits of the full physical cascade. -/
namespace Fresh.NativeUpperGridArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeDoubleGridRecovery
  Fresh.NativeClearReboundCore Fresh.NativeUpperGridPacket Fresh.NativeCanonicalReturn Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def Upper (q V : ℝ) (K : ℤ) : Prop :=
  ∃ H : ℤ, 1 ≤ H ∧ q*V=8*(H : ℝ)*(K : ℝ)+7/8

-- STANDING: DEFINITION
noncomputable def Slow (q d V : ℝ) : Prop :=
  2*q ≤ d ∧ ∃ J : ℤ,(J : ℝ)+1/8 ≤ q*V ∧ q*V ≤ (J : ℝ)+19/24

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (V : ℝ) (u m : Fin 8) (K H : ℤ),
    u≠k ∧ m≠k ∧ 1 ≤ K ∧ 1 ≤ H ∧ reading v k u*V=(K : ℝ) ∧
    reading v k m*V=8*(H : ℝ)*(K : ℝ)+7/8 ∧
    ∀ q : Fin 8,q≠k → reading v k q≠reading v k u →
      Slow (reading v k q) (reading v k u) V ∨
      (Upper (reading v k q) V K ∧ reading v k m ≤ reading v k q ∧ reading v k q ≤ 4*reading v k m)

theorem class_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : CanonicalReturnClass v k := by
  obtain ⟨hv,V,u,m,K,H,hu,hm,hK,hH,hdV,hpV,houtside⟩ := h
  have hd : 0<reading v k u := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨u,hu,rfl⟩)
  have hp : 0<reading v k m := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨m,hm,rfl⟩)
  let W := V+1/(8*reading v k u)
  have hret := upper_return (reading v k u) (reading v k m) V K H hd hK hdV hpV
  have hfast := upper_fast (reading v k u) (reading v k m) V K H hd hK hH hdV hpV
  change reading v k m*W=(8*H*K+H+1 : ℤ)-1/8+7/(64*(K : ℝ)) ∧ _ at hret
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have ht : 0<7/(64*(K : ℝ)) := by positivity
  have ht' : 7/(64*(K : ℝ))<1/4 := by
    apply (div_lt_iff₀ (by positivity : 0<64*(K : ℝ))).2
    linarith only [hKr]
  have hstep := integer_step (reading v k u) V K hd hdV
  have hpown := handoff_identity hv k m W hm
  change reading v k m*labelledOpening (reading v k m) W=(label (reading v k m*W) : ℝ)+1/8 at hpown
  rw [hret.2.1] at hpown
  have hM : 0<8*H*K+H+1 := by
    have hh := mul_pos (show 0<8*H by omega) (show 0<K by omega)
    omega
  apply Fresh.NativeArbitraryThirdReversal.anchored_point_into_canonical hv k m _ _ hm hM hpown
  apply (isolatedAt_iff_lonelyAt v k _).2
  intro d hmem
  obtain ⟨q,hq,rfl⟩ := mem_disparitySet.mp hmem
  change 1/8 ≤ distInt (reading v k q*labelledOpening (reading v k m) W)
  by_cases he : reading v k q=reading v k u
  · rw [he]
    have hw := own_opening_retained (reading v k m) (reading v k u) W
      (labelledOpening (reading v k m) W) (8*H*K+H+1) K hp hd.le
      (by linarith only [hfast,hp]) hstep hret.2.2.1 hpown hret.2.1.symm
    exact clear_of_window K hw.1 hw.2.le
  rcases houtside q hq he with ⟨hslow,J,hlo,hhi⟩|⟨⟨A,hA,hqV⟩,hmin,hmax⟩
  · have hw := slow_margin (reading v k u) (reading v k m) (reading v k q) V K J hd hp
      (show 0 ≤ reading v k q from abs_nonneg _) hdV hfast hslow hret.2.2.1 hlo hhi
    exact clear_of_window J hw.1 hw.2.le
  · have hr := upper_return (reading v k u) (reading v k q) V K A hd hK hdV hqV
    have hw := packet_window (reading v k m) (reading v k q) W (7/(64*(K : ℝ)))
      (8*H*K+H+1) (8*A*K+A+1) hp ht ht' hret.1 hr.1 hmin hmax
    exact clear_of_window _ hw.1 hw.2.le

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
  IsArrangement v ∧ ∃ (R : ℝ) (g j i u m : Fin 8) (K H : ℤ),
    0<R ∧ g≠k ∧ j≠k ∧ i≠k ∧ u≠k ∧ m≠k ∧
    3*reading v k i ≤ 5*reading v k g ∧ 3*reading v k g ≤ 5*reading v k j ∧
    3*reading v k j ≤ 5*reading v k g ∧
    InWay (reading v k g) R ∧ InWay (reading v k j) (handoffOpening v k R g) ∧
    InWay (reading v k i) R ∧ handoffOpening v k R i ≤ handoffOpening v k R g ∧
    InWay (reading v k i) (handoffOpening v k (handoffOpening v k R g) j) ∧
    1 ≤ K ∧ 1 ≤ H ∧ 2*label (reading v k i*handoffOpening v k (handoffOpening v k R g) j)+1 ≤ K ∧
    reading v k u*handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i=(K : ℝ) ∧
    reading v k m*handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i=8*(H : ℝ)*(K : ℝ)+7/8 ∧
    ∀ q : Fin 8,q≠k → reading v k q∉({reading v k g,reading v k j,reading v k i,reading v k u} : Finset ℝ) →
      (1/8 ≤ reading v k q*handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i ∧
        reading v k q*handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i ≤ 1/2) ∨
      (Upper (reading v k q) (handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i) K ∧
        reading v k m ≤ reading v k q ∧ reading v k q ≤ 4*reading v k m)

theorem returned_into_class {v : Fin 8 → ℝ} {k : Fin 8} (h : ReturnedClass v k) : Class v k := by
  obtain ⟨hv,R,g,j,i,u,m,K,H,_hR,hg,hj,hi,hu,hm,hsg,hgj,hjg,hwg,hwj,hwi,horder,hret,hK,hH,hlarge,hdV,hpV,houtside⟩ := h
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
  refine ⟨hv,V,u,m,K,H,hu,hm,hK,hH,hdV,hpV,?_⟩
  intro q hq hne
  by_cases hcore : reading v k q∈({reading v k g,reading v k j,reading v k i} : Finset ℝ)
  · obtain ⟨hle,J,hlo,hhi⟩ := hmargin _ hcore
    exact Or.inl ⟨by linarith only [hle,hspeed],J,hlo,hhi⟩
  have hnot : reading v k q∉({reading v k g,reading v k j,reading v k i,reading v k u} : Finset ℝ) := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hcore ⊢
    tauto
  rcases houtside q hq hnot with hquiet|hupper
  · change 1/8 ≤ reading v k q*V ∧ reading v k q*V ≤ 1/2 at hquiet
    have hqratio : 2*reading v k q ≤ reading v k u := by nlinarith only [hquiet.2,hdV,hKr,hV]
    exact Or.inl ⟨hqratio,0,by simpa using hquiet.1,by norm_num; linarith only [hquiet.2]⟩
  · exact Or.inr hupper

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

#print axioms class_into_canonical
#print axioms class_isolation
#print axioms scaled_isolation
#print axioms returned_into_class
#print axioms returned_isolation
#print axioms returned_scaled_into_scaled
#print axioms returned_scaled_isolation
end Fresh.NativeUpperGridArrangement
