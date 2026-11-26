import Fresh.NativeFastSecondResetArrangement

/-! A fast-second return at the fourth opening resolves without assuming
the second was captured at the earlier third opening. Only the minimum
and second share an origin phase; all later outsider duties are derived. -/
namespace Fresh.NativeFastSecondReturnArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeUpperGridPacket
  Fresh.NativeCanonicalReturn Fresh.NativeFourthReturnGeometry Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (V t : ℝ) (u a b c e : Fin 8) (K M N : ℤ),
    u≠k ∧ a≠k ∧ b≠k ∧ c≠k ∧ e≠k ∧ 1 ≤ K ∧ 0<t ∧ t<1/4 ∧
    reading v k u*V=(K : ℝ) ∧ 8*reading v k u ≤ reading v k a ∧
    reading v k a ≤ reading v k b ∧ reading v k a ≤ reading v k c ∧ reading v k a ≤ reading v k e ∧
    3*reading v k c<reading v k b ∧ 3*reading v k e<reading v k b ∧
    let W := V+1/(8*reading v k u)
    let Z := labelledOpening (reading v k a) W
    let Y := labelledOpening (reading v k b) Z
    let T := labelledOpening (reading v k c) Y
    let G := labelledOpening (reading v k e) T
    reading v k a*W=(M : ℝ)-1/8+t ∧ reading v k b*W=(N : ℝ)-1/8+t ∧
    InWay (reading v k b) Z ∧ InWay (reading v k c) Y ∧ InWay (reading v k e) T ∧
    InWay (reading v k b) G ∧
    ∀ i : Fin 8,i≠k → reading v k i∉({reading v k u,reading v k a,reading v k b,reading v k c,reading v k e} : Finset ℝ) →
      2*reading v k i ≤ reading v k u ∧ ∃ J : ℤ,(J : ℝ)+1/8 ≤ reading v k i*V ∧ reading v k i*V ≤ (J : ℝ)+3/4

theorem class_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : CanonicalReturnClass v k := by
  obtain ⟨hv,V,t,u,a,b,c,e,K,M,N,hu,ha,hb,hc,he,hK,ht,ht',hdV,hfast,hpq,hpr,hps,hqr,hqs,hframe⟩ := h
  let d := reading v k u
  let p := reading v k a
  let q := reading v k b
  let r := reading v k c
  let s := reading v k e
  let W := V+1/(8*d)
  let Z := labelledOpening p W
  let Y := labelledOpening q Z
  let T := labelledOpening r Y
  let G := labelledOpening s T
  let U := labelledOpening q G
  obtain ⟨hpW,hqW,hqc,hrc,hsc,hret,hslow⟩ := hframe
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
  have hZ := captured_labelled_advance p W hp hpc
  have hrT := labelled_opening_identity r Y hr
  have hlabel := Fresh.NativeCohortOutsiderRelay.label_at_opening r T (label (r*Y)) hrT
  have hrOwn : r*T=(label (r*T) : ℝ)+1/8 := by rw [hlabel]; exact hrT
  have hpZ := labelled_opening_identity p W hp
  have hpU := minimum_window p q r s Z (label (p*W)) hp hq hr hs (by linarith only [hlarge]) hpr hps hpZ hqc hrc hsc hret
  change (label (p*W) : ℝ)+1/8 ≤ p*U ∧ p*U<(label (p*W) : ℝ)+7/8 at hpU
  have hlocal := local_displacement d p q r s V hd hp hq hr hs hfast hfastq hfastr hfasts hpc hqc hrc hsc hret
  change 0<U-V ∧ d*(U-V)<15/64 at hlocal
  have hdW := Fresh.NativeDoubleGridRecovery.integer_step d V K hd hdV
  change d*W=(K : ℝ)+1/8 at hdW
  have hd_at (F : ℝ) (hpF : (label (p*W) : ℝ)+1/8 ≤ p*F)
      (hlocalF : d*(F-V)<15/64) : (K : ℝ)+1/8 ≤ d*F ∧ d*F<(K : ℝ)+7/8 := by
    have hFZ : Z ≤ F := by
      have hh : p*Z ≤ p*F := by linarith only [hpF,hpZ]
      by_contra hn
      have hbad := mul_pos hp (sub_pos.mpr (lt_of_not_ge hn))
      nlinarith only [hh,hbad]
    have hFW : W ≤ F := by linarith only [hFZ,hZ.1]
    have hlo := mul_le_mul_of_nonneg_left hFW hd.le
    constructor <;> nlinarith only [hdW,hlo,hdV,hlocalF]
  have clear_at (F : ℝ) (hVF : 0<F-V) (hdis : d*(F-V)<15/64)
      (hcore : LonelyAt ({q,r,s} : Finset ℝ) F)
      (hmin : (label (p*W) : ℝ)+1/8 ≤ p*F ∧ p*F<(label (p*W) : ℝ)+7/8) : IsolatedAt v k F := by
    have hdF := hd_at F hmin.1 hdis
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
      have hw := slow_window d (reading v k i) V F J (show 0 ≤ reading v k i from abs_nonneg _) hVF.le hdis hspeed hlo hhi
      exact clear_of_window J hw.1 hw.2.le
  have hqU := labelled_opening_identity q G hq
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hV : 0<V := by nlinarith only [hdV,hKr,hd]
  by_cases hrret : InWay r U
  · let F := partnerEnd q r U
    have hgap := old_third_forced_gap q r s T hq hr hs hrOwn hsc hret hqs hrret
    have hnewr : 18*d ≤ r := by linarith only [hgap,hfasts]
    have hnewq : 54*d ≤ q := by linarith only [hqr,hnewr]
    have hpr' : 9*p ≤ 4*r := by linarith only [hgap,hps]
    have hpq' : 27*p ≤ 4*q := by linarith only [hqr,hpr']
    have hmin := Fresh.NativeFourthReboundTail.minimum_window p q r s Z (label (p*W)) hp hq hr hs hpq' hpr' hps hpZ hqc hrc hsc hret hrret
    change (label (p*W) : ℝ)+1/8 ≤ p*F ∧ p*F<(label (p*W) : ℝ)+7/8 at hmin
    have hdis := Fresh.NativeFourthReboundTail.local_displacement d p q r s V hd hp hq hr hs hfast hnewq hnewr hfasts hpc hqc hrc hsc hret hrret
    change 0<F-V ∧ d*(F-V)<11/48 at hdis
    have hcore := Fresh.NativeFourthReboundTail.rebound_core q r s G (label (s*T)) hq hr hs
      (by linarith only [hqs,hs]) (by linarith only [hgap,hs]) (labelled_opening_identity s T hs) hret hrret
    have hpoint := clear_at F hdis.1 (by linarith only [hdis.2]) hcore hmin
    have hbc : b≠c := by
      intro hbc
      have heq : q=r := by dsimp [q,r]; rw [hbc]
      nlinarith only [heq,hqr,hr]
    apply Fresh.NativeOpeningReversalArrangement.pairRecovery_into_canonical
    refine ⟨hv,b,c,U,label (q*G),hb,hc,hbc,?_,hqU,hrret,?_⟩
    · linarith only [hV,hlocal.1]
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      have hik := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hi).1).1
      exact not_lt.mpr ((isolatedAt_iff_lonelyAt v k F).1 hpoint _ (mem_disparitySet.mpr ⟨i,hik,rfl⟩))
  · have hsU := own_opening_retained q s G U (label (q*G)) (label (s*T)) hq hs.le
      (by linarith only [hqs,hq]) (labelled_opening_identity s T hs) hret hqU rfl
    have hcore : LonelyAt ({q,r,s} : Finset ℝ) U := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with hx|hx|hx
      · subst x; exact clear_of_window _ hqU.ge (by linarith only [hqU])
      · subst x; exact not_lt.mp hrret
      · subst x; exact clear_of_window _ hsU.1 hsU.2.le
    have hpoint := clear_at U hlocal.1 hlocal.2 hcore hpU
    have hb1 := mul_le_mul_of_nonneg_right hfast hV.le
    have hb2 := mul_le_mul_of_nonneg_right hpq hV.le
    have hb3 := mul_pos hq hlocal.1
    have hL : 0<label (q*G) := by
      have hh : (0 : ℝ)<(label (q*G) : ℝ) := by nlinarith only [hqU,hdV,hKr,hb1,hb2,hb3]
      exact_mod_cast hh
    exact Fresh.NativeArbitraryThirdReversal.anchored_point_into_canonical hv k b U _ hb hL hqU hpoint

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
end Fresh.NativeFastSecondReturnArrangement
