import Fresh.NativeFastSecondResetTail

/-! A native second-reader reset resolves an arbitrary fourth reading above
the minimum. The reset itself forces the fast-second separation. Initial
slow windows and native boundary displacement derive every outsider duty. -/
namespace Fresh.NativeFastSecondResetArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeThirdReaderRebound
  Fresh.NativeUpperGridPacket Fresh.NativeCanonicalReturn Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (V t : ℝ) (u a b c e : Fin 8) (K M N : ℤ),
    u≠k ∧ a≠k ∧ b≠k ∧ c≠k ∧ e≠k ∧ 1 ≤ K ∧ 0<t ∧ t<1/4 ∧
    reading v k u*V=(K : ℝ) ∧ 8*reading v k u ≤ reading v k a ∧
    reading v k a ≤ reading v k b ∧ reading v k a ≤ reading v k c ∧ reading v k a ≤ reading v k e ∧
    let W := V+1/(8*reading v k u)
    let Z := labelledOpening (reading v k a) W
    let Y := labelledOpening (reading v k b) Z
    reading v k a*W=(M : ℝ)-1/8+t ∧ reading v k b*W=(N : ℝ)-1/8+t ∧
    InWay (reading v k b) Z ∧ InWay (reading v k c) Y ∧
    InWay (reading v k b) (labelledOpening (reading v k c) Y) ∧
    ∀ i : Fin 8,i≠k → reading v k i∉({reading v k u,reading v k a,reading v k b,reading v k c,reading v k e} : Finset ℝ) →
      2*reading v k i ≤ reading v k u ∧ ∃ J : ℤ,(J : ℝ)+1/8 ≤ reading v k i*V ∧ reading v k i*V ≤ (J : ℝ)+3/4

theorem class_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : CanonicalReturnClass v k := by
  classical
  obtain ⟨hv,V,t,u,a,b,c,e,K,M,N,hu,ha,hb,hc,he,hK,ht,ht',hdV,hfast,hpq,hpr,hps,hframe⟩ := h
  let d := reading v k u
  let p := reading v k a
  let q := reading v k b
  let r := reading v k c
  let s := reading v k e
  let W := V+1/(8*d)
  let Z := labelledOpening p W
  let Y := labelledOpening q Z
  let T := labelledOpening r Y
  let A := labelledOpening q T
  obtain ⟨hpW,hqW,hqc,hrc,hqret,hslow⟩ := hframe
  have hd : 0<d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨u,hu,rfl⟩)
  have hp : 0<p := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hq : 0<q := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨b,hb,rfl⟩)
  have hr : 0<r := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc,rfl⟩)
  have hs : 0<s := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨e,he,rfl⟩)
  have hpc := (phase_capture_label p W t M ht ht' hpW).2
  have hlarge := Fresh.NativeUpperPairHandoff.recapture_fast p q W t M N hp ht ht' hpW hqW hpq hqc
  have hfastq : 32*d ≤ q := by linarith only [hlarge,hfast]
  have hfastr : 8*d ≤ r := hfast.trans hpr
  have hfasts : 8*d ≤ s := hfast.trans hps
  have hpZ := labelled_opening_identity p W hp
  have hqY := labelled_opening_identity q Z hq
  have hrT := labelled_opening_identity r Y hr
  have hqr := recapture_forces_three q r Y T (label (q*Z)) (label (r*Y)) hq hr hqY hrc hrT rfl hqret
  have hqA := labelled_opening_identity q T hq
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
  have clear_at (F : ℝ) (hVF : 0<F-V) (hdis : d*(F-V)<1/4)
      (hcore : LonelyAt ({q,r,s} : Finset ℝ) F)
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
      have hw := Fresh.NativeComparableFourthTail.slow_quarter_window d (reading v k i) V F J
        (show 0 ≤ reading v k i from abs_nonneg _) hVF.le hdis hspeed hlo hhi
      exact clear_of_window J hw.1 hw.2.le
  by_cases hsc : InWay s A
  · let F := forcedEnd q r s T
    obtain ⟨H,B,hH,hTB,hBF,hm,hcore⟩ := forced_triple_resolution q r s T (label (r*Y)) hq hr hs hqr hrT hqret hsc
    have hmin := Fresh.NativeFastSecondResetTail.minimum_window p q r s Z (label (p*W)) hp hq hr hs
      (by linarith only [hlarge]) hpr hps hqr hpZ hqc hrc hqret hsc
    have hdis := Fresh.NativeFastSecondResetTail.local_displacement d p q r s V hd hp hq hr hs
      hfast hfastq hfastr hps hqr hpc hqc hrc hqret hsc
    change 0<F-V ∧ d*(F-V)<1/4 at hdis
    have hpoint := clear_at F hdis.1 hdis.2 hcore hmin
    have hcoreSub : ({q,r,s} : Finset ℝ) ⊆ disparitySet v k := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with hx|hx|hx
      · rw [hx]; exact mem_disparitySet.mpr ⟨b,hb,rfl⟩
      · rw [hx]; exact mem_disparitySet.mpr ⟨c,hc,rfl⟩
      · rw [hx]; exact mem_disparitySet.mpr ⟨e,he,rfl⟩
    have hHsub : H ⊆ disparitySet v k := hH.trans hcoreSub
    have hHpos : ∀ x∈H,0<x := fun x hx=>disparitySet_pos hv k x (hHsub hx)
    have hApos : ∀ x∈disparitySet v k\H,0<x := fun x hx=>disparitySet_pos hv k x (Finset.mem_sdiff.mp hx).1
    have hfull := Fresh.NativeGroupEndpointRecovery.endpoint_clear_preserves_move hHpos hApos B F hm (by
      intro x hx
      exact not_lt.mpr ((isolatedAt_iff_lonelyAt v k F).1 hpoint x (Finset.mem_sdiff.mp hx).1))
    rw [Finset.union_sdiff_of_subset hHsub] at hfull
    have hTpos : 0<T := by linarith only [hYpos,hT.1]
    exact Fresh.NativeFixedPrefixArrangement.canonical_of_isolating_move hv k B F (hTpos.trans_le hTB) hBF hfull hpoint
  · have hrwindow := own_opening_retained q r T A (label (q*T)) (label (r*Y)) hq hr.le
      (by linarith only [hqr,hq]) hrT hqret hqA rfl
    have hmin := Fresh.NativeFastSecondResetTail.reset_minimum_window p q r Z (label (p*W)) hp hq hr
      (by linarith only [hlarge]) hpr hpZ hqc hrc hqret
    have hdis := Fresh.NativeFastSecondResetTail.reset_prefix_displacement d p q r V hd hp hq hr
      hfast hfastq hfastr hpc hqc hrc hqret
    change 0<A-V ∧ d*(A-V)<13/64 at hdis
    have hcore : LonelyAt ({q,r,s} : Finset ℝ) A := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with hx|hx|hx
      · subst x; exact clear_of_window _ hqA.ge (by linarith only [hqA])
      · subst x; exact clear_of_window _ hrwindow.1 hrwindow.2.le
      · subst x; exact not_lt.mp hsc
    have hpoint := clear_at A hdis.1 (by linarith only [hdis.2]) hcore ⟨hmin.1,by linarith only [hmin.2]⟩
    have hb1 := mul_le_mul_of_nonneg_right hfast hV.le
    have hb2 := mul_le_mul_of_nonneg_right hpq hV.le
    have hb3 := mul_pos hq hdis.1
    have hL : 0<label (q*T) := by
      have hh : (0 : ℝ)<(label (q*T) : ℝ) := by nlinarith only [hqA,hdV,hKr,hb1,hb2,hb3]
      exact_mod_cast hh
    exact Fresh.NativeArbitraryThirdReversal.anchored_point_into_canonical hv k b A _ hb hL hqA hpoint

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
end Fresh.NativeFastSecondResetArrangement
