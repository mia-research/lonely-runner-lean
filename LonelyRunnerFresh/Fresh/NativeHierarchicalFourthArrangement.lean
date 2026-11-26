import Fresh.NativeHierarchicalFourthTail

/-! A fast third reader resolves an arbitrary fourth reader through the
native forced triple tail. The fourth reader need not share an origin phase
or satisfy the old-second simple-fit face. All outsider duties are derived
from initial slow windows and actual local boundary displacement. -/
namespace Fresh.NativeHierarchicalFourthArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeThirdReaderRebound
  Fresh.NativeUpperGridPacket Fresh.NativeCanonicalReturn Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (V t : ℝ) (u a b c e : Fin 8) (K M N : ℤ),
    u≠k ∧ a≠k ∧ b≠k ∧ c≠k ∧ e≠k ∧ 1 ≤ K ∧ 0<t ∧ t<1/4 ∧
    reading v k u*V=(K : ℝ) ∧ 8*reading v k u ≤ reading v k a ∧
    reading v k a ≤ reading v k b ∧ reading v k a ≤ reading v k e ∧ 3*reading v k b<reading v k c ∧
    let W := V+1/(8*reading v k u)
    let Z := labelledOpening (reading v k a) W
    let Y := labelledOpening (reading v k b) Z
    reading v k a*W=(M : ℝ)-1/8+t ∧ reading v k b*W=(N : ℝ)-1/8+t ∧
    InWay (reading v k b) Z ∧ InWay (reading v k c) Y ∧
    ∀ i : Fin 8,i≠k → reading v k i∉({reading v k u,reading v k a,reading v k b,reading v k c,reading v k e} : Finset ℝ) →
      2*reading v k i ≤ reading v k u ∧ ∃ J : ℤ,(J : ℝ)+1/8 ≤ reading v k i*V ∧ reading v k i*V ≤ (J : ℝ)+3/4

theorem class_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : CanonicalReturnClass v k := by
  classical
  obtain ⟨hv,V,t,u,a,b,c,e,K,M,N,hu,ha,hb,hc,he,hK,ht,ht',hdV,hfast,hpq,hps,hqr,hframe⟩ := h
  let d := reading v k u
  let p := reading v k a
  let q := reading v k b
  let r := reading v k c
  let s := reading v k e
  let W := V+1/(8*d)
  let Z := labelledOpening p W
  let Y := labelledOpening q Z
  let T := labelledOpening r Y
  obtain ⟨hpW,hqW,hqc,hrc,hslow⟩ := hframe
  have hd : 0<d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨u,hu,rfl⟩)
  have hp : 0<p := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hq : 0<q := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨b,hb,rfl⟩)
  have hr : 0<r := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc,rfl⟩)
  have hs : 0<s := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨e,he,rfl⟩)
  have hpc := (phase_capture_label p W t M ht ht' hpW).2
  have hlarge := Fresh.NativeUpperPairHandoff.recapture_fast p q W t M N hp ht ht' hpW hqW hpq hqc
  have hfastq : 32*d ≤ q := by linarith only [hlarge,hfast]
  have hfastr : 96*d ≤ r := by linarith only [hfastq,hqr]
  have hfasts : 8*d ≤ s := hfast.trans hps
  have hpr : p ≤ r := by linarith only [hpq,hqr,hq]
  have hpZ := labelled_opening_identity p W hp
  have hqY := labelled_opening_identity q Z hq
  have hrT := labelled_opening_identity r Y hr
  have hZ := captured_labelled_advance p W hp hpc
  have hY := captured_labelled_advance q Z hq hqc
  have hT := captured_labelled_advance r Y hr hrc
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hV : 0<V := by nlinarith only [hdV,hKr,hd]
  have hYpos : 0<Y := by
    have hstep : 0<1/(8*d) := by positivity
    change 0<Z-W ∧ _ at hZ
    change 0<Y-Z ∧ _ at hY
    dsimp [W] at hZ
    linarith only [hV,hZ.1,hY.1,hstep]
  have hdW := Fresh.NativeDoubleGridRecovery.integer_step d V K hd hdV
  change d*W=(K : ℝ)+1/8 at hdW
  have clear_at (F : ℝ) (hVF : 0<F-V) (hdis : d*(F-V)<15/64)
      (hcore : LonelyAt ({r,q,s} : Finset ℝ) F)
      (hmin : (label (p*W) : ℝ)+1/8 ≤ p*F ∧ p*F<(label (p*W) : ℝ)+7/8) : IsolatedAt v k F := by
    have hFZ : Z ≤ F := by
      by_contra hn
      have hb := mul_pos hp (sub_pos.mpr (lt_of_not_ge hn))
      nlinarith only [hmin.1,hpZ,hb]
    have hFW : W ≤ F := by linarith only [hFZ,hZ.1]
    have hdFbound := mul_le_mul_of_nonneg_left hFW hd.le
    have hdF : (K : ℝ)+1/8 ≤ d*F ∧ d*F<(K : ℝ)+7/8 := by
      constructor <;> nlinarith only [hdW,hdFbound,hdV,hdis]
    apply (isolatedAt_iff_lonelyAt v k F).2
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hx
    change 1/8 ≤ distInt (reading v k i*F)
    by_cases hm : reading v k i∈({d,p,q,r,s} : Finset ℝ)
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      rcases hm with hd'|hp'|hq'|hr'|hs'
      · rw [hd']; exact clear_of_window K hdF.1 hdF.2.le
      · rw [hp']; exact clear_of_window _ hmin.1 hmin.2.le
      · rw [hq']; exact hcore _ (by simp)
      · rw [hr']; exact hcore _ (by simp)
      · rw [hs']; exact hcore _ (by simp)
    · obtain ⟨hspeed,J,hlo,hhi⟩ := hslow i hi hm
      have hw := Fresh.NativeFourthReturnGeometry.slow_window d (reading v k i) V F J
        (show 0 ≤ reading v k i from abs_nonneg _) hVF.le hdis hspeed hlo hhi
      exact clear_of_window J hw.1 hw.2.le
  by_cases hsc : InWay s T
  · let F := forcedEnd r q s Y
    obtain ⟨H,B,hH,hYB,hBF,hm,hcore⟩ := forced_triple_resolution r q s Y (label (q*Z)) hr hq hs hqr hqY hrc hsc
    have hmin := Fresh.NativeHierarchicalFourthTail.minimum_window p q r s Z (label (p*W)) hp hq hr hs
      (by linarith only [hlarge]) (by linarith only [hlarge,hqr]) hps hqr hpZ hqc hrc hsc
    have hdis := Fresh.NativeHierarchicalFourthTail.forced_displacement d p q r s V hd hp hq hr hs
      hfast hfastq hfastr hfasts hqr hpc hqc hrc hsc
    change 0<F-V ∧ d*(F-V)<37/168 at hdis
    have hpoint := clear_at F hdis.1 (by linarith only [hdis.2]) hcore hmin
    have hcoreSub : ({r,q,s} : Finset ℝ) ⊆ disparitySet v k := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with hx|hx|hx
      · rw [hx]; exact mem_disparitySet.mpr ⟨c,hc,rfl⟩
      · rw [hx]; exact mem_disparitySet.mpr ⟨b,hb,rfl⟩
      · rw [hx]; exact mem_disparitySet.mpr ⟨e,he,rfl⟩
    have hHsub : H ⊆ disparitySet v k := hH.trans hcoreSub
    have hHpos : ∀ x∈H,0<x := fun x hx=>disparitySet_pos hv k x (hHsub hx)
    have hApos : ∀ x∈disparitySet v k\H,0<x := fun x hx=>disparitySet_pos hv k x (Finset.mem_sdiff.mp hx).1
    have hfull := Fresh.NativeGroupEndpointRecovery.endpoint_clear_preserves_move hHpos hApos B F hm (by
      intro x hx
      exact not_lt.mpr ((isolatedAt_iff_lonelyAt v k F).1 hpoint x (Finset.mem_sdiff.mp hx).1))
    rw [Finset.union_sdiff_of_subset hHsub] at hfull
    exact Fresh.NativeFixedPrefixArrangement.canonical_of_isolating_move hv k B F (hYpos.trans_le hYB) hBF hfull hpoint
  · have hqclear := own_opening_retained r q Y T (label (r*Y)) (label (q*Z)) hr hq.le
      (by linarith only [hqr,hr]) hqY hrc hrT rfl
    have hfit : p*(q+r) ≤ 3*q*r := by
      have h1 := mul_le_mul_of_nonneg_right hpq hr.le
      have h2 := mul_le_mul_of_nonneg_right hpr hq.le
      nlinarith only [h1,h2,mul_pos hq hr]
    have hmin := Fresh.NativeClearWindowRebound.own_two_window q r p Z (label (p*W)) hq hr hp hpZ hqc hrc hfit
    have hdis := Fresh.NativeHierarchicalFourthTail.prefix_displacement d p q r V hd hp hq hr hfast hfastq hfastr hpc hqc hrc
    change 0<T-V ∧ d*(T-V)<1/6 at hdis
    have hcore : LonelyAt ({r,q,s} : Finset ℝ) T := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with hx|hx|hx
      · subst x; exact clear_of_window _ hrT.ge (by linarith only [hrT])
      · subst x; exact clear_of_window _ hqclear.1 hqclear.2.le
      · subst x; exact not_lt.mp hsc
    have hpoint := clear_at T hdis.1 (by linarith only [hdis.2]) hcore hmin
    have hb1 := mul_le_mul_of_nonneg_right hfast hV.le
    have hb2 := mul_le_mul_of_nonneg_right hpr hV.le
    have hb3 := mul_pos hr hdis.1
    have hL : 0<label (r*Y) := by
      have hh : (0 : ℝ)<(label (r*Y) : ℝ) := by nlinarith only [hrT,hdV,hKr,hb1,hb2,hb3]
      exact_mod_cast hh
    exact Fresh.NativeArbitraryThirdReversal.anchored_point_into_canonical hv k c T _ hc hL hrT hpoint

theorem class_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : Isolation v k :=
  canonical_isolation (class_into_canonical h)

-- STANDING: DEFINITION
noncomputable def ScaledClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ c : ℝ,0<c ∧ Class (fun i=>c*v i) k

theorem scaled_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) : Isolation v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact Fresh.ProvedTypesScale.Isolation_smul_of hc (class_isolation hbase)

theorem simple_into_class {v : Fin 8 → ℝ} {k : Fin 8}
    (h : Fresh.NativeRecoveredSecondArrangement.SimpleClass v k) : Class v k := by
  obtain ⟨hv,V,t,u,a,b,c,e,K,M,N,hu,ha,hb,hc,he,hK,ht,ht',hdV,hfast,hpq,hps,hqr,_hqs,hframe⟩ := h
  obtain ⟨hpW,hqW,hqc,hrc,_hsc,_hret,hslow⟩ := hframe
  exact ⟨hv,V,t,u,a,b,c,e,K,M,N,hu,ha,hb,hc,he,hK,ht,ht',hdV,hfast,hpq,hps,hqr,hpW,hqW,hqc,hrc,hslow⟩

#print axioms class_into_canonical
#print axioms class_isolation
#print axioms scaled_isolation
#print axioms simple_into_class
end Fresh.NativeHierarchicalFourthArrangement
