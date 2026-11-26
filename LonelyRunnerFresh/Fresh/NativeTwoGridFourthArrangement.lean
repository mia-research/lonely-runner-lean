import Fresh.NativeArbitraryFourthArrangement

/-! Two common-phase readings and two arbitrary readings above the minimum.
Only the first second-reader capture is assumed. A current third capture
is chosen if present; otherwise the second opening already isolates. -/
namespace Fresh.NativeTwoGridFourthArrangement
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
    reading v k a*W=(M : ℝ)-1/8+t ∧ reading v k b*W=(N : ℝ)-1/8+t ∧
    InWay (reading v k b) Z ∧
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
  obtain ⟨hpW,hqW,hqc,hslow⟩ := hframe
  by_cases hrc : InWay r Y
  · exact Fresh.NativeArbitraryFourthArrangement.class_into_canonical
      ⟨hv,V,t,u,a,b,c,e,K,M,N,hu,ha,hb,hc,he,hK,ht,ht',hdV,hfast,hpq,hpr,hps,hpW,hqW,hqc,hrc,hslow⟩
  by_cases hsc : InWay s Y
  · have hslow' : ∀ i : Fin 8,i≠k → reading v k i∉({d,p,q,s,r} : Finset ℝ) →
        2*reading v k i ≤ d ∧ ∃ J : ℤ,(J : ℝ)+1/8 ≤ reading v k i*V ∧ reading v k i*V ≤ (J : ℝ)+3/4 := by
      intro i hi hm
      apply hslow i hi
      simpa only [Finset.mem_insert,Finset.mem_singleton,or_comm,or_left_comm,or_assoc] using hm
    exact Fresh.NativeArbitraryFourthArrangement.class_into_canonical
      ⟨hv,V,t,u,a,b,e,c,K,M,N,hu,ha,hb,he,hc,hK,ht,ht',hdV,hfast,hpq,hps,hpr,hpW,hqW,hqc,hsc,hslow'⟩
  have hd : 0<d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨u,hu,rfl⟩)
  have hp : 0<p := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hq : 0<q := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨b,hb,rfl⟩)
  have hpc := (phase_capture_label p W t M ht ht' hpW).2
  have hlarge := Fresh.NativeUpperPairHandoff.recapture_fast p q W t M N hp ht ht' hpW hqW hpq hqc
  have hfastq : 32*d ≤ q := by linarith only [hlarge,hfast]
  have hpZ := labelled_opening_identity p W hp
  have hqY := labelled_opening_identity q Z hq
  have hZ := captured_labelled_advance p W hp hpc
  have hY := captured_labelled_advance q Z hq hqc
  have hstep : 0<1/(8*d) := by positivity
  have hid : d*(1/(8*d))=1/8 := by field_simp
  have hb0 := mul_le_mul_of_nonneg_right hfast hZ.1.le
  have hb1 := mul_le_mul_of_nonneg_right hfastq hY.1.le
  have hdis : 0<Y-V ∧ d*(Y-V)<21/128 := by
    change 0<Z-W ∧ p*(Z-W)<1/4 at hZ
    change 8*d*(Z-W) ≤ p*(Z-W) at hb0
    dsimp [W] at hZ hb0
    constructor <;> nlinarith only [hZ.1,hY.1,hstep,hid,hZ.2,hY.2,hb0,hb1]
  have hpY := own_opening_retained q p Z Y (label (q*Z)) (label (p*W)) hq hp.le
    (by linarith only [hlarge,hp]) hpZ hqc hqY rfl
  have hdW := Fresh.NativeDoubleGridRecovery.integer_step d V K hd hdV
  change d*W=(K : ℝ)+1/8 at hdW
  have hYW : W ≤ Y := by linarith only [hZ.1,hY.1]
  have hdYbound := mul_le_mul_of_nonneg_left hYW hd.le
  have hdY : (K : ℝ)+1/8 ≤ d*Y ∧ d*Y<(K : ℝ)+7/8 := by
    constructor <;> nlinarith only [hdW,hdYbound,hdV,hdis.2]
  have hpoint : IsolatedAt v k Y := by
    apply (isolatedAt_iff_lonelyAt v k Y).2
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hx
    change 1/8 ≤ distInt (reading v k i*Y)
    by_cases hm : reading v k i∈({d,p,q,r,s} : Finset ℝ)
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      rcases hm with hd'|hp'|hq'|hr'|hs'
      · rw [hd']; exact clear_of_window K hdY.1 hdY.2.le
      · rw [hp']; exact clear_of_window _ hpY.1 hpY.2.le
      · rw [hq']; exact clear_of_window _ hqY.ge (by linarith only [hqY])
      · rw [hr']; exact not_lt.mp hrc
      · rw [hs']; exact not_lt.mp hsc
    · obtain ⟨hspeed,J,hlo,hhi⟩ := hslow i hi hm
      have hw := Fresh.NativeComparableFourthTail.slow_quarter_window d (reading v k i) V Y J
        (show 0 ≤ reading v k i from abs_nonneg _) hdis.1.le (by linarith only [hdis.2]) hspeed hlo hhi
      exact clear_of_window J hw.1 hw.2.le
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hV : 0<V := by nlinarith only [hdV,hKr,hd]
  have h1 := mul_le_mul_of_nonneg_right hfast hV.le
  have h2 := mul_le_mul_of_nonneg_right hpq hV.le
  have h3 := mul_pos hq hdis.1
  have hL : 0<label (q*Z) := by
    have hh : (0 : ℝ)<(label (q*Z) : ℝ) := by nlinarith only [hqY,hdV,hKr,h1,h2,h3]
    exact_mod_cast hh
  exact Fresh.NativeArbitraryThirdReversal.anchored_point_into_canonical hv k b Y _ hb hL hqY hpoint

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
end Fresh.NativeTwoGridFourthArrangement
