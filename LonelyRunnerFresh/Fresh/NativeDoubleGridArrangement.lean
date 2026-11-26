import Fresh.NativeDoubleGridRecovery
import Fresh.NativeClearWitnessArrangement

/-! Native integer-grid recovery with independent observer return labels.
A returned-core subclass forces the core and quiet-reader duties using an
integer speed parameter. Earlier supplied openings need not be visits. -/
namespace Fresh.NativeDoubleGridArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeDoubleGridRecovery
  Fresh.NativeClearReboundCore Fresh.NativeCanonicalReturn Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def Grid (q V : ℝ) (K : ℤ) : Prop :=
  ∃ (H : ℤ) (a : ℝ), 0 ≤ H ∧ 1 ≤ a ∧ a ≤ 56/9 ∧ q*V=8*(H : ℝ)*(K : ℝ)+a/8

-- STANDING: DEFINITION
noncomputable def Retained (q d V : ℝ) : Prop :=
  (label (q*V) : ℝ)+1/8 ≤ q*V ∧ q/8 ≤ d*((label (q*V) : ℝ)+7/8-q*V)

theorem margin_into_retained (q d V : ℝ) (J : ℤ) (hd : 0<d)
    (hr : 2*q ≤ d) (hlo : (J : ℝ)+1/8 ≤ q*V) (hhi : q*V ≤ (J : ℝ)+19/24) :
    Retained q d V := by
  have hl := (entry_iff_label q V J).1 (Or.inl ⟨hlo,by linarith only [hhi]⟩)
  unfold Retained
  rw [hl]
  refine ⟨hlo,?_⟩
  have hm := mul_le_mul_of_nonneg_left hhi hd.le
  nlinarith only [hm,hr,hd]

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (V : ℝ) (u : Fin 8) (K : ℤ), u≠k ∧ 1 ≤ K ∧ reading v k u*V=(K : ℝ) ∧
    ∀ q : Fin 8, q≠k → reading v k q≠reading v k u →
      Retained (reading v k q) (reading v k u) V ∨ Grid (reading v k q) V K

theorem class_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : CanonicalReturnClass v k := by
  obtain ⟨hv,V,u,K,hu,hK,ho,houtside⟩ := h
  have hd : 0<reading v k u := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨u,hu,rfl⟩)
  have hstep := integer_step (reading v k u) V K hd ho
  have hKpos : 0<K := by omega
  apply Fresh.NativeArbitraryThirdReversal.anchored_point_into_canonical hv k u _ K hu hKpos hstep
  apply (isolatedAt_iff_lonelyAt v k _).2
  intro d hmem
  obtain ⟨q,hq,rfl⟩ := mem_disparitySet.mp hmem
  change 1/8 ≤ distInt (reading v k q*(V+1/(8*reading v k u)))
  by_cases he : reading v k q=reading v k u
  · rw [he]
    exact clear_of_window K hstep.ge (by linarith only [hstep])
  rcases houtside q hq he with hr|⟨H,a,_hH,ha,ha',hqV⟩
  · have hqp : 0 ≤ reading v k q := abs_nonneg _
    have hf : reading v k q*((K : ℝ)+1/8-reading v k u*V) ≤
        reading v k u*((label (reading v k q*V) : ℝ)+7/8-reading v k q*V) := by
      rw [ho]
      simpa using hr.2
    have hw := Fresh.NativeOpeningRetention.weighted_window (reading v k u) (reading v k q)
      V (V+1/(8*reading v k u)) K (label (reading v k q*V)) hd hqp
      (le_add_of_nonneg_right (by positivity)) hstep hr.1 hf
    exact clear_of_window _ hw.1 hw.2
  · have hw := recovery_window (reading v k u) (reading v k q) V K H a hd hK ho ha ha' hqV
    exact clear_of_window _ hw.1 hw.2

theorem class_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : Isolation v k :=
  canonical_isolation (class_into_canonical h)

-- STANDING: DEFINITION
noncomputable def ScaledClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ c : ℝ, 0<c ∧ Class (fun i=>c*v i) k

theorem scaled_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) : Isolation v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact Fresh.ProvedTypesScale.Isolation_smul_of hc (class_isolation hbase)

-- STANDING: DEFINITION
noncomputable def ReturnedClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (R : ℝ) (g j i u : Fin 8) (K : ℤ),
    0<R ∧ g≠k ∧ j≠k ∧ i≠k ∧ u≠k ∧
    3*reading v k i ≤ 5*reading v k g ∧ 3*reading v k g ≤ 5*reading v k j ∧
    3*reading v k j ≤ 5*reading v k g ∧
    InWay (reading v k g) R ∧ InWay (reading v k j) (handoffOpening v k R g) ∧
    InWay (reading v k i) R ∧ handoffOpening v k R i ≤ handoffOpening v k R g ∧
    InWay (reading v k i) (handoffOpening v k (handoffOpening v k R g) j) ∧
    1 ≤ K ∧ 2*label (reading v k i*handoffOpening v k (handoffOpening v k R g) j)+1 ≤ K ∧
    reading v k u*handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i=(K : ℝ) ∧
    ∀ q : Fin 8, q≠k → reading v k q∉({reading v k g,reading v k j,reading v k i,reading v k u} : Finset ℝ) →
      (1/8 ≤ reading v k q*handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i ∧
        reading v k q*handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i ≤ 1/2) ∨
      Grid (reading v k q) (handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i) K

theorem returned_into_class {v : Fin 8 → ℝ} {k : Fin 8} (h : ReturnedClass v k) : Class v k := by
  obtain ⟨hv,R,g,j,i,u,K,hR,hg,hj,hi,hu,hsg,hgj,hjg,hwg,hwj,hwi,horder,hret,hK,hlarge,hdV,houtside⟩ := h
  let V := handoffOpening v k (handoffOpening v k (handoffOpening v k R g) j) i
  have hgp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have hjp : 0<reading v k j := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨j,hj,rfl⟩)
  have hip : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  have hdp : 0<reading v k u := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨u,hu,rfl⟩)
  have hmargin := core_margin (reading v k g) (reading v k j) (reading v k i) R hgp hjp hip
    hsg hgj hjg hwg hwj hwi horder hret
  change ∀ q∈({reading v k g,reading v k j,reading v k i} : Finset ℝ), q ≤ reading v k i ∧
    ∃ J : ℤ, (J : ℝ)+1/8 ≤ q*V ∧ q*V ≤ (J : ℝ)+19/24 at hmargin
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  change reading v k u*V=(K : ℝ) at hdV
  have hV : 0<V := by nlinarith only [hdV,hKr,hdp]
  have hsV := handoff_identity hv k i (handoffOpening v k (handoffOpening v k R g) j) hi
  change reading v k i*V=(label (reading v k i*handoffOpening v k (handoffOpening v k R g) j) : ℝ)+1/8 at hsV
  have hlargeR : 2*(label (reading v k i*handoffOpening v k (handoffOpening v k R g) j) : ℝ)+1 ≤ (K : ℝ) := by exact_mod_cast hlarge
  have hspeed : 2*reading v k i ≤ reading v k u := by nlinarith only [hsV,hdV,hlargeR,hV]
  refine ⟨hv,V,u,K,hu,hK,hdV,?_⟩
  intro q hq hne
  by_cases hcore : reading v k q∈({reading v k g,reading v k j,reading v k i} : Finset ℝ)
  · obtain ⟨hle,J,hlo,hhi⟩ := hmargin _ hcore
    exact Or.inl (margin_into_retained _ _ _ J hdp (by linarith only [hle,hspeed]) hlo hhi)
  have hnot : reading v k q∉({reading v k g,reading v k j,reading v k i,reading v k u} : Finset ℝ) := by
    simpa only [Finset.mem_insert,Finset.mem_singleton] using (show ¬(reading v k q=reading v k g ∨ reading v k q=reading v k j ∨ reading v k q=reading v k i ∨ reading v k q=reading v k u) from by
      intro hh
      rcases hh with hh|hh|hh|hh
      · exact hcore (by simp only [Finset.mem_insert,Finset.mem_singleton]; exact Or.inl hh)
      · exact hcore (by simp only [Finset.mem_insert,Finset.mem_singleton]; exact Or.inr (Or.inl hh))
      · exact hcore (by simp only [Finset.mem_insert,Finset.mem_singleton]; exact Or.inr (Or.inr hh))
      · exact hne hh)
  rcases houtside q hq hnot with hquiet|hgrid
  · change 1/8 ≤ reading v k q*V ∧ reading v k q*V ≤ 1/2 at hquiet
    have hqratio : 2*reading v k q ≤ reading v k u := by nlinarith only [hquiet.2,hdV,hKr,hV]
    exact Or.inl (margin_into_retained _ _ _ 0 hdp hqratio (by simpa using hquiet.1)
      (by norm_num; linarith only [hquiet.2]))
  · exact Or.inr hgrid

theorem returned_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ReturnedClass v k) : Isolation v k :=
  class_isolation (returned_into_class h)

-- STANDING: DEFINITION
noncomputable def ReturnedScaledClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ c : ℝ, 0<c ∧ ReturnedClass (fun i=>c*v i) k

theorem returned_scaled_into_scaled {v : Fin 8 → ℝ} {k : Fin 8}
    (h : ReturnedScaledClass v k) : ScaledClass v k := by
  obtain ⟨hv,c,hc,hbase⟩ := h
  exact ⟨hv,c,hc,returned_into_class hbase⟩

theorem returned_scaled_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : ReturnedScaledClass v k) : Isolation v k :=
  scaled_isolation (returned_scaled_into_scaled h)

#print axioms returned_scaled_into_scaled
#print axioms returned_scaled_isolation

#print axioms margin_into_retained
#print axioms class_into_canonical
#print axioms class_isolation
#print axioms scaled_isolation
#print axioms returned_into_class
#print axioms returned_isolation
end Fresh.NativeDoubleGridArrangement
