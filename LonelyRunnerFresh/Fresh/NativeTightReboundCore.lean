import Fresh.NativeUpperPairArrangement
import Fresh.NativeDoubleGridRecovery

/-! A failed native composed face forces sharper separation and tighter
returned clear windows. No full-arrangement moves or common-clear witness
are assumed. These margins belong to the supplied core fragment only. -/
namespace Fresh.NativeTightReboundCore
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeClearReboundCore
  Fresh.NativeDoubleGridRecovery Fresh.FastestCaptureRetention

theorem composed_face_failed (g j s R : ℝ) (hg : 0<g) (hj : 0<j) (hs : 0<s)
    (hwg : InWay g R) (hwj : InWay j (labelledOpening g R)) (hws : InWay s R)
    (horder : labelledOpening s R ≤ labelledOpening g R)
    (hret : InWay s (labelledOpening j (labelledOpening g R))) :
    3*g*j<s*(g+j) := by
  apply lt_of_not_ge
  intro hf
  have hw := Fresh.NativeWatcherPacketReturn.packet_window j g s R hj hg hs hwg hwj hws horder
    (by nlinarith only [hf])
  exact not_lt_of_ge (clear_of_window _ hw.1 hw.2.le) hret

theorem separation (g j s : ℝ) (hg : 0<g) (hj : 0<j)
    (hgj : 3*g ≤ 5*j) (hjg : 3*j ≤ 5*g) (hf : 3*g*j<s*(g+j)) :
    9*g<8*s ∧ 9*j<8*s := by
  constructor
  · by_contra hn
    have h1 := mul_le_mul_of_nonneg_right (le_of_not_gt hn) (add_pos hg hj).le
    have h2 := mul_le_mul_of_nonneg_left hgj hg.le
    nlinarith only [h1,h2,hf]
  · by_contra hn
    have h1 := mul_le_mul_of_nonneg_right (le_of_not_gt hn) (add_pos hg hj).le
    have h2 := mul_le_mul_of_nonneg_left hjg hj.le
    nlinarith only [h1,h2,hf]

theorem core_window (g j s R : ℝ) (hg : 0<g) (hj : 0<j) (hs : 0<s)
    (hgj : 3*g ≤ 5*j) (hjg : 3*j ≤ 5*g)
    (hwg : InWay g R) (hwj : InWay j (labelledOpening g R)) (hws : InWay s R)
    (horder : labelledOpening s R ≤ labelledOpening g R)
    (hret : InWay s (labelledOpening j (labelledOpening g R))) :
    ∀ q∈({g,j,s} : Finset ℝ),q ≤ s ∧ ∃ J : ℤ,
      (J : ℝ)+1/8 ≤ q*labelledOpening s (labelledOpening j (labelledOpening g R)) ∧
      q*labelledOpening s (labelledOpening j (labelledOpening g R)) ≤ (J : ℝ)+55/72 := by
  have hf := composed_face_failed g j s R hg hj hs hwg hwj hws horder hret
  have hsep := separation g j s hg hj hgj hjg hf
  have hy := captured_labelled_advance j (labelledOpening g R) hj hwj
  have hz := captured_labelled_advance s (labelledOpening j (labelledOpening g R)) hs hret
  have h1 := mul_le_mul_of_nonneg_right hgj hy.1.le
  have h2 := mul_le_mul_of_nonneg_right hsep.1.le hz.1.le
  have h3 := mul_le_mul_of_nonneg_right hsep.2.le hz.1.le
  have hgo := labelled_opening_identity g R hg
  have hjo := labelled_opening_identity j (labelledOpening g R) hj
  have hso := labelled_opening_identity s (labelledOpening j (labelledOpening g R)) hs
  have hlowg := mul_nonneg hg.le (show 0 ≤ labelledOpening s (labelledOpening j (labelledOpening g R))-labelledOpening g R by linarith only [hy.1,hz.1])
  have hlowj := mul_nonneg hj.le hz.1.le
  intro q hq
  simp only [Finset.mem_insert,Finset.mem_singleton] at hq
  rcases hq with hq|hq|hq
  · subst q
    exact ⟨by linarith only [hsep.1,hs],label (g*R),by nlinarith only [hgo,hlowg],by nlinarith only [hgo,h1,h2,hy.2,hz.2]⟩
  · subst q
    exact ⟨by linarith only [hsep.2,hs],label (j*labelledOpening g R),by nlinarith only [hjo,hlowj],by nlinarith only [hjo,h3,hz.2]⟩
  · subst q
    exact ⟨le_rfl,label (s*labelledOpening j (labelledOpening g R)),hso.ge,by linarith only [hso]⟩

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (R : ℝ) (g j i u a b : Fin 8) (K H A : ℤ),
    0<R ∧ g≠k ∧ j≠k ∧ i≠k ∧ u≠k ∧ a≠k ∧ b≠k ∧
    3*reading v k g ≤ 5*reading v k j ∧
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

theorem class_into_pair {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : Fresh.NativeUpperPairArrangement.Class v k := by
  obtain ⟨hv,R,g,j,i,u,a,b,K,H,A,_hR,hg,hj,hi,hu,ha,hb,hgj,hjg,hwg,hwj,hwi,horder,hret,hK,hH,hA,hlarge,hdV,hpV,hqV,hpq,houtside⟩ := h
  let V := handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i
  have hgp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have hjp : 0<reading v k j := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨j,hj,rfl⟩)
  have hip : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  have hdp : 0<reading v k u := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨u,hu,rfl⟩)
  have hmargin := core_window (reading v k g) (reading v k j) (reading v k i) R hgp hjp hip
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
  refine ⟨hv,V,u,a,b,K,H,A,hu,ha,hb,hK,hH,hA,hdV,hpV,hqV,hpq,?_⟩
  intro q hq hnot
  have hnd : reading v k q≠reading v k u := by
    intro he
    exact hnot (by simp only [Finset.mem_insert,Finset.mem_singleton]; exact Or.inl he)
  by_cases hcore : reading v k q∈({reading v k g,reading v k j,reading v k i} : Finset ℝ)
  · obtain ⟨hle,J,hlo,hhi⟩ := hmargin _ hcore
    exact ⟨by linarith only [hle,hspeed],J,hlo,by linarith only [hhi]⟩
  have hnotcore : reading v k q∉({reading v k g,reading v k j,reading v k i,reading v k u} : Finset ℝ) := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hcore ⊢
    tauto
  rcases houtside q hq hnotcore with hquiet|he|he
  · change 1/8 ≤ reading v k q*V ∧ reading v k q*V ≤ 1/2 at hquiet
    have hr : 2*reading v k q ≤ reading v k u := by nlinarith only [hquiet.2,hdV,hKr,hV]
    exact ⟨hr,0,by simpa using hquiet.1,by norm_num; linarith only [hquiet.2]⟩
  · exact (hnot (by simp only [Finset.mem_insert,Finset.mem_singleton]; exact Or.inr (Or.inl he))).elim
  · exact (hnot (by simp only [Finset.mem_insert,Finset.mem_singleton]; exact Or.inr (Or.inr he))).elim

theorem class_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : Isolation v k :=
  Fresh.NativeUpperPairArrangement.class_isolation (class_into_pair h)

-- STANDING: DEFINITION
noncomputable def ScaledClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ c : ℝ,0<c ∧ Class (fun i=>c*v i) k

theorem scaled_into_pair {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) :
    Fresh.NativeUpperPairArrangement.ScaledClass v k := by
  obtain ⟨hv,c,hc,hbase⟩ := h
  exact ⟨hv,c,hc,class_into_pair hbase⟩

theorem scaled_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) : Isolation v k :=
  Fresh.NativeUpperPairArrangement.scaled_isolation (scaled_into_pair h)

#print axioms class_into_pair
#print axioms class_isolation
#print axioms scaled_into_pair
#print axioms scaled_isolation

#print axioms composed_face_failed
#print axioms separation
#print axioms core_window
end Fresh.NativeTightReboundCore
