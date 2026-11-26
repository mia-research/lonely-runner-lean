import Fresh.NativeArbitraryFourthGrid

/-! Four common-origin upper readings. Any captured next reader is selected
for the proved native two-grid family; if none is captured, the minimum
opening isolates. No first capture or later speed ratio is assumed. -/
namespace Fresh.NativeFourUpperArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeThirdReaderRebound
  Fresh.NativeUpperGridPacket Fresh.NativeCanonicalReturn Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (V t : ℝ) (u a b c e : Fin 8) (K M N P Q : ℤ),
    u≠k ∧ a≠k ∧ b≠k ∧ c≠k ∧ e≠k ∧ 1 ≤ K ∧ 0<t ∧ t<1/4 ∧
    reading v k u*V=(K : ℝ) ∧ 8*reading v k u ≤ reading v k a ∧
    reading v k a ≤ reading v k b ∧ reading v k a ≤ reading v k c ∧ reading v k a ≤ reading v k e ∧
    let W := V+1/(8*reading v k u)
    reading v k a*W=(M : ℝ)-1/8+t ∧ reading v k b*W=(N : ℝ)-1/8+t ∧
    reading v k c*W=(P : ℝ)-1/8+t ∧ reading v k e*W=(Q : ℝ)-1/8+t ∧
    ∀ i : Fin 8,i≠k → reading v k i∉({reading v k u,reading v k a,reading v k b,reading v k c,reading v k e} : Finset ℝ) →
      2*reading v k i ≤ reading v k u ∧ ∃ J : ℤ,(J : ℝ)+1/8 ≤ reading v k i*V ∧ reading v k i*V ≤ (J : ℝ)+3/4

theorem class_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : CanonicalReturnClass v k := by
  classical
  obtain ⟨hv,V,t,u,a,b,c,e,K,M,N,P,Q,hu,ha,hb,hc,he,hK,ht,ht',hdV,hfast,hpq,hpr,hps,hframe⟩ := h
  let d := reading v k u
  let p := reading v k a
  let q := reading v k b
  let r := reading v k c
  let s := reading v k e
  let W := V+1/(8*d)
  let Z := labelledOpening p W
  obtain ⟨hpW,hqW,hrW,hsW,hslow⟩ := hframe
  by_cases hqc : InWay q Z
  · exact Fresh.NativeTwoGridFourthArrangement.class_into_canonical
      ⟨hv,V,t,u,a,b,c,e,K,M,N,hu,ha,hb,hc,he,hK,ht,ht',hdV,hfast,hpq,hpr,hps,hpW,hqW,hqc,hslow⟩
  by_cases hrc : InWay r Z
  · have hslow' : ∀ i : Fin 8,i≠k → reading v k i∉({d,p,r,q,s} : Finset ℝ) →
        2*reading v k i ≤ d ∧ ∃ J : ℤ,(J : ℝ)+1/8 ≤ reading v k i*V ∧ reading v k i*V ≤ (J : ℝ)+3/4 := by
      intro i hi hm
      apply hslow i hi
      simpa only [Finset.mem_insert,Finset.mem_singleton,or_comm,or_left_comm,or_assoc] using hm
    exact Fresh.NativeTwoGridFourthArrangement.class_into_canonical
      ⟨hv,V,t,u,a,c,b,e,K,M,P,hu,ha,hc,hb,he,hK,ht,ht',hdV,hfast,hpr,hpq,hps,hpW,hrW,hrc,hslow'⟩
  by_cases hsc : InWay s Z
  · have hslow' : ∀ i : Fin 8,i≠k → reading v k i∉({d,p,s,q,r} : Finset ℝ) →
        2*reading v k i ≤ d ∧ ∃ J : ℤ,(J : ℝ)+1/8 ≤ reading v k i*V ∧ reading v k i*V ≤ (J : ℝ)+3/4 := by
      intro i hi hm
      apply hslow i hi
      simpa only [Finset.mem_insert,Finset.mem_singleton,or_comm,or_left_comm,or_assoc] using hm
    exact Fresh.NativeTwoGridFourthArrangement.class_into_canonical
      ⟨hv,V,t,u,a,e,b,c,K,M,Q,hu,ha,he,hb,hc,hK,ht,ht',hdV,hfast,hps,hpq,hpr,hpW,hsW,hsc,hslow'⟩
  have hd : 0<d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨u,hu,rfl⟩)
  have hp : 0<p := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hpc := (phase_capture_label p W t M ht ht' hpW).2
  have hpZ := labelled_opening_identity p W hp
  have hZ := captured_labelled_advance p W hp hpc
  have hstep : 0<1/(8*d) := by positivity
  have hid : d*(1/(8*d))=1/8 := by field_simp
  have hb0 := mul_le_mul_of_nonneg_right hfast hZ.1.le
  have hdis : 0<Z-V ∧ d*(Z-V)<5/32 := by
    change 0<Z-W ∧ p*(Z-W)<1/4 at hZ
    change 8*d*(Z-W) ≤ p*(Z-W) at hb0
    dsimp [W] at hZ hb0
    constructor <;> nlinarith only [hZ.1,hstep,hid,hZ.2,hb0]
  have hdW := Fresh.NativeDoubleGridRecovery.integer_step d V K hd hdV
  change d*W=(K : ℝ)+1/8 at hdW
  have hdZbound := mul_le_mul_of_nonneg_left (show W ≤ Z by linarith only [hZ.1]) hd.le
  have hdZ : (K : ℝ)+1/8 ≤ d*Z ∧ d*Z<(K : ℝ)+7/8 := by
    constructor <;> nlinarith only [hdW,hdZbound,hdV,hdis.2]
  have hpoint : IsolatedAt v k Z := by
    apply (isolatedAt_iff_lonelyAt v k Z).2
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hx
    change 1/8 ≤ distInt (reading v k i*Z)
    by_cases hm : reading v k i∈({d,p,q,r,s} : Finset ℝ)
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      rcases hm with hd'|hp'|hq'|hr'|hs'
      · rw [hd']; exact clear_of_window K hdZ.1 hdZ.2.le
      · rw [hp']; exact clear_of_window _ hpZ.ge (by linarith only [hpZ])
      · rw [hq']; exact not_lt.mp hqc
      · rw [hr']; exact not_lt.mp hrc
      · rw [hs']; exact not_lt.mp hsc
    · obtain ⟨hspeed,J,hlo,hhi⟩ := hslow i hi hm
      have hw := Fresh.NativeComparableFourthTail.slow_quarter_window d (reading v k i) V Z J
        (show 0 ≤ reading v k i from abs_nonneg _) hdis.1.le (by linarith only [hdis.2]) hspeed hlo hhi
      exact clear_of_window J hw.1 hw.2.le
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hV : 0<V := by nlinarith only [hdV,hKr,hd]
  have h1 := mul_le_mul_of_nonneg_right hfast hV.le
  have h2 := mul_pos hp hdis.1
  have hL : 0<label (p*W) := by
    have hh : (0 : ℝ)<(label (p*W) : ℝ) := by nlinarith only [hpZ,hdV,hKr,h1,h2]
    exact_mod_cast hh
  exact Fresh.NativeArbitraryThirdReversal.anchored_point_into_canonical hv k a Z _ ha hL hpZ hpoint

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
end Fresh.NativeFourUpperArrangement
