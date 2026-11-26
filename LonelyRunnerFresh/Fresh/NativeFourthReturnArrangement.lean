import Fresh.NativeFourthReturnGeometry

/-! A fourth-reader reversal family. Native common-origin return levels
force the previous setter's face; initial slow windows force all remaining
duties. No terminal outsider clearance or full prior move chain is assumed. -/
namespace Fresh.NativeFourthReturnArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeUpperGridPacket
  Fresh.NativeCanonicalReturn Fresh.NativeFourthReturnGeometry Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (V t : ℝ) (u a b c e : Fin 8) (K M N P Q : ℤ),
    u≠k ∧ a≠k ∧ b≠k ∧ c≠k ∧ e≠k ∧ 1 ≤ K ∧ 0<t ∧ t<1/4 ∧
    reading v k u*V=(K : ℝ) ∧ 8*reading v k u ≤ reading v k a ∧
    reading v k a ≤ reading v k b ∧ reading v k a ≤ reading v k c ∧ reading v k a ≤ reading v k e ∧
    let W := V+1/(8*reading v k u)
    let Z := labelledOpening (reading v k a) W
    let Y := labelledOpening (reading v k b) Z
    let T := labelledOpening (reading v k c) Y
    let G := labelledOpening (reading v k e) T
    reading v k a*W=(M : ℝ)-1/8+t ∧ reading v k b*W=(N : ℝ)-1/8+t ∧
    reading v k c*W=(P : ℝ)-1/8+t ∧ reading v k e*W=(Q : ℝ)-1/8+t ∧
    InWay (reading v k b) Z ∧ InWay (reading v k c) Y ∧ InWay (reading v k e) T ∧
    InWay (reading v k b) T ∧ labelledOpening (reading v k b) T ≤ G ∧ InWay (reading v k b) G ∧
    advance (reading v k c) W T<2*advance (reading v k e) W T ∧
    ∀ i : Fin 8,i≠k → reading v k i∉({reading v k u,reading v k a,reading v k b,reading v k c,reading v k e} : Finset ℝ) →
      2*reading v k i ≤ reading v k u ∧ ∃ J : ℤ,(J : ℝ)+1/8 ≤ reading v k i*V ∧ reading v k i*V ≤ (J : ℝ)+3/4

theorem class_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : CanonicalReturnClass v k := by
  obtain ⟨hv,V,t,u,a,b,c,e,K,M,N,P,Q,hu,ha,hb,hc,he,hK,ht,ht',hdV,hfast,hpq,hpr,hps,hframe⟩ := h
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
  obtain ⟨hpW,hqW,hrW,hsW,hqc,hrc,hsc,hqt,horder,hret,hlevel,hslow⟩ := hframe
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
  have hY := captured_labelled_advance q Z hq hqc
  have hT := captured_labelled_advance r Y hr hrc
  have hWT : W ≤ T := by linarith only [hZ.1,hY.1,hT.1]
  have hrT := labelled_opening_identity r Y hr
  have hlabel := Fresh.NativeCohortOutsiderRelay.label_at_opening r T (label (r*Y)) hrT
  have hrOwn : r*T=(label (r*T) : ℝ)+1/8 := by rw [hlabel]; exact hrT
  have hthree := returned_three_clear q r s W T t P Q hq hr hs hWT ht ht' hrW hsW hrOwn hqt hsc horder hret hlevel
  have hpZ := labelled_opening_identity p W hp
  have hpU := minimum_window p q r s Z (label (p*W)) hp hq hr hs (by linarith only [hlarge]) hpr hps hpZ hqc hrc hsc hret
  change (label (p*W) : ℝ)+1/8 ≤ p*U ∧ p*U<(label (p*W) : ℝ)+7/8 at hpU
  have hlocal := local_displacement d p q r s V hd hp hq hr hs hfast hfastq hfastr hfasts hpc hqc hrc hsc hret
  change 0<U-V ∧ d*(U-V)<15/64 at hlocal
  have hUZ : Z ≤ U := by
    have hh : p*Z ≤ p*U := by linarith only [hpU.1,hpZ]
    by_contra hn
    have hb := mul_pos hp (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith only [hh,hb]
  have hUW : W ≤ U := by linarith only [hUZ,hZ.1]
  have hdW := Fresh.NativeDoubleGridRecovery.integer_step d V K hd hdV
  change d*W=(K : ℝ)+1/8 at hdW
  have hdUlo := mul_le_mul_of_nonneg_left hUW hd.le
  have hdU : (K : ℝ)+1/8 ≤ d*U ∧ d*U<(K : ℝ)+7/8 := by
    constructor <;> nlinarith only [hdW,hdUlo,hdV,hlocal.2]
  have hqU := labelled_opening_identity q G hq
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hV : 0<V := by nlinarith only [hdV,hKr,hd]
  have hb1 := mul_le_mul_of_nonneg_right hfast hV.le
  have hb2 := mul_le_mul_of_nonneg_right hpq hV.le
  have hb3 := mul_pos hq hlocal.1
  have hL : 0<label (q*G) := by
    have hh : (0 : ℝ)<(label (q*G) : ℝ) := by nlinarith only [hqU,hdV,hKr,hb1,hb2,hb3]
    exact_mod_cast hh
  apply Fresh.NativeArbitraryThirdReversal.anchored_point_into_canonical hv k b U _ hb hL hqU
  apply (isolatedAt_iff_lonelyAt v k U).2
  intro x hx
  obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hx
  change 1/8 ≤ distInt (reading v k i*U)
  by_cases hm : reading v k i∈({d,p,q,r,s} : Finset ℝ)
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with hd'|hp'|hq'|hr'|hs'
    · rw [hd']; exact clear_of_window K hdU.1 hdU.2.le
    · rw [hp']; exact clear_of_window _ hpU.1 hpU.2.le
    · rw [hq']; exact hthree _ (by simp)
    · rw [hr']; exact hthree _ (by simp)
    · rw [hs']; exact hthree _ (by simp)
  · obtain ⟨hspeed,J,hlo,hhi⟩ := hslow i hi hm
    have hw := slow_window d (reading v k i) V U J (show 0 ≤ reading v k i from abs_nonneg _)
      hlocal.1.le hlocal.2 hspeed hlo hhi
    exact clear_of_window J hw.1 hw.2.le

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
end Fresh.NativeFourthReturnArrangement
