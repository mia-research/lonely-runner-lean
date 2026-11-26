import Fresh.NativeCohortReturns

/-! After a common cohort opening, the actual next setter is an original
outsider. The original cohort's retained-closing duties coalesce to its
fastest physical member. Later positive returns remain independently tracked. -/
namespace Fresh.NativeCohortOutsiderRelay
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement Fresh.NativeReturnClosingOrder
  Fresh.NativeCapturedPartnerJoin Fresh.NativeCohortReturns

theorem label_at_opening (s T : ℝ) (K : ℤ) (ho : s*T=(K : ℝ)+1/8) : label (s*T)=K := by
  apply (entry_iff_label s T K).1
  exact Or.inl (by constructor <;> linarith only [ho])

theorem zero_from_opening_iff (s T U : ℝ) (K : ℤ) (hs : 0 ≤ s) (hTU : T ≤ U)
    (ho : s*T=(K : ℝ)+1/8) : advance s T U=0 ↔ 4*s*(U-T) ≤ 3 := by
  rw [zero_iff_original_upper s T U hs hTU,label_at_opening s T K ho]
  constructor <;> intro hh <;> nlinarith only [hh,ho]

theorem capture_from_opening_iff (s T U : ℝ) (K : ℤ) (hs : 0 ≤ s) (hTU : T ≤ U)
    (ho : s*T=(K : ℝ)+1/8) :
    InWay s U ↔ (advance s T U : ℝ)-1/4<s*(U-T) ∧ s*(U-T)<(advance s T U : ℝ) := by
  have hid := advance_identity s T U hs hTU
  rw [label_at_opening s T K ho] at hid
  have hb := (entry_interval s U _).1 (label_entry s U)
  rw [hid] at hb
  push_cast at hb
  rw [inWay_iff_lower_not_passed,hid]
  push_cast
  constructor
  · intro hh
    constructor <;> nlinarith only [hh,hb.1,ho]
  · intro hh
    nlinarith only [hh.2,ho]

theorem cohort_opening_identity {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R : ℝ) (c : Fin 8)
    (h : Cohort v k R c) (i : Fin 8) (hi : i≠k) (hw : InWay (reading v k i) R) :
    reading v k i*handoffOpening v k R c=(label (reading v k i*R) : ℝ)+1/8 := by
  have hid := handoff_identity hv k i R hi
  rw [h.2.2 i hi hw] at hid
  exact hid

theorem clear_from_opening_iff (s T U : ℝ) (K : ℤ) (hs : 0 ≤ s) (hTU : T ≤ U)
    (ho : s*T=(K : ℝ)+1/8) :
    ¬InWay s U ↔ (advance s T U : ℝ) ≤ s*(U-T) := by
  have hid := advance_identity s T U hs hTU
  rw [label_at_opening s T K ho] at hid
  rw [inWay_iff_lower_not_passed,hid]
  push_cast
  rw [not_lt]
  constructor <;> intro hh <;> nlinarith only [hh,ho]

theorem cohort_recovery_iff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R U : ℝ) (c : Fin 8)
    (h : Cohort v k R c) (hTU : handoffOpening v k R c ≤ U) (i : Fin 8) (hi : i≠k)
    (hw : InWay (reading v k i) R) :
    ¬InWay (reading v k i) U ↔
      (advance (reading v k i) (handoffOpening v k R c) U : ℝ) ≤
        reading v k i*(U-handoffOpening v k R c) :=
  clear_from_opening_iff _ _ U _ (abs_nonneg _) hTU (cohort_opening_identity hv k R c h i hi hw)

noncomputable def FastestCohort (v : Fin 8 → ℝ) (k : Fin 8) (R : ℝ) (f : Fin 8) : Prop :=
  f≠k ∧ InWay (reading v k f) R ∧
    ∀ i : Fin 8, i≠k → InWay (reading v k i) R → reading v k i ≤ reading v k f

theorem exists_fastest {v : Fin 8 → ℝ} (k : Fin 8) (R : ℝ) (c : Fin 8)
    (h : Cohort v k R c) : ∃ f : Fin 8, FastestCohort v k R f := by
  classical
  let S := Finset.univ.filter (fun i : Fin 8=>i≠k ∧ InWay (reading v k i) R)
  have hc : c∈S := by simp [S,h.1,h.2.1]
  obtain ⟨f,hf,hmax⟩ := Finset.exists_max_image S (reading v k) ⟨c,hc⟩
  have hfm := (Finset.mem_filter.mp hf).2
  exact ⟨f,hfm.1,hfm.2,fun i hi hw=>hmax i (by simp [S,hi,hw])⟩

theorem fastest_retention_iff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R U : ℝ) (c f : Fin 8)
    (h : Cohort v k R c) (hf : FastestCohort v k R f) (hTU : handoffOpening v k R c ≤ U) :
    (∀ i : Fin 8, i≠k → InWay (reading v k i) R →
      advance (reading v k i) (handoffOpening v k R c) U=0) ↔
      4*reading v k f*(U-handoffOpening v k R c) ≤ 3 := by
  constructor
  · intro hz
    exact (zero_from_opening_iff _ _ U _ (abs_nonneg _) hTU
      (cohort_opening_identity hv k R c h f hf.1 hf.2.1)).1 (hz f hf.1 hf.2.1)
  · intro hh i hi hw
    apply (zero_from_opening_iff _ _ U _ (abs_nonneg _) hTU
      (cohort_opening_identity hv k R c h i hi hw)).2
    have hle := mul_le_mul_of_nonneg_right (hf.2.2 i hi hw) (sub_nonneg.mpr hTU)
    change 4*reading v k i*(U-handoffOpening v k R c) ≤ 3
    nlinarith only [hle,hh]

theorem outsider_forces_move {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R : ℝ) (c g : Fin 8)
    (h : Cohort v k R c) (hg : g≠k) (hwg : InWay (reading v k g) (handoffOpening v k R c))
    (horder : ∀ i : Fin 8, i≠k → ¬InWay (reading v k i) R →
      InWay (reading v k i) (handoffOpening v k R c) →
      handoffOpening v k (handoffOpening v k R c) i ≤ handoffOpening v k (handoffOpening v k R c) g) :
    handoffOpening v k R c < handoffOpening v k (handoffOpening v k R c) g ∧
      IsMove (disparitySet v k) (handoffOpening v k R c) (handoffOpening v k (handoffOpening v k R c) g) := by
  have hp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  constructor
  · have hh := lt_nextOpening hp hwg
    rw [next_at_label _ _ hwg] at hh
    exact hh
  · refine Or.inr ⟨reading v k g,mem_disparitySet.mpr ⟨g,hg,rfl⟩,hwg,(next_at_label _ _ hwg).symm,?_⟩
    intro s hs hws
    obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hs
    change InWay (reading v k i) (handoffOpening v k R c) at hws
    change nextOpening (reading v k i) (handoffOpening v k R c) ≤ _
    rw [next_at_label _ _ hws]
    exact horder i hi (cohort_capture_outside hv k R c h i hi hws) hws

theorem guard_of_ratio {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (T : ℝ) (f g : Fin 8)
    (hg : g≠k) (hw : InWay (reading v k g) T) (hr : reading v k f ≤ 3*reading v k g) :
    4*reading v k f*(handoffOpening v k T g-T)<3 := by
  have hp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have hc := capture_at_label (reading v k g) T hw
  have ha := Fresh.NativeOpeningRetention.capture_advance _ T _ _ hp
    (handoff_identity hv k g T hg) hc.1 hc.2
  have hm := mul_le_mul_of_nonneg_right hr ha.1.le
  nlinarith only [ha.2,hm]

theorem returned_cohort_forces_slow_setter {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R : ℝ) (c f g : Fin 8)
    (h : Cohort v k R c) (hf : FastestCohort v k R f) (hg : g≠k)
    (hw : InWay (reading v k g) (handoffOpening v k R c))
    (hr : ¬∀ i : Fin 8, i≠k → InWay (reading v k i) R →
      advance (reading v k i) (handoffOpening v k R c) (handoffOpening v k (handoffOpening v k R c) g)=0) :
    3*reading v k g<reading v k f := by
  by_contra hn
  have hguard := guard_of_ratio hv k (handoffOpening v k R c) f g hg hw (le_of_not_gt hn)
  have hp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have htime := lt_nextOpening hp hw
  rw [next_at_label _ _ hw] at htime
  exact hr ((fastest_retention_iff hv k R _ c f h hf htime.le).2 hguard.le)

noncomputable def OutsiderFaces (v : Fin 8 → ℝ) (k : Fin 8) (R : ℝ) (c f g : Fin 8) : Prop :=
  4*reading v k f*(handoffOpening v k (handoffOpening v k R c) g-handoffOpening v k R c) ≤ 3 ∧
    ∀ i : Fin 8, i≠k → ¬InWay (reading v k i) R →
      (InWay (reading v k i) (handoffOpening v k R c) →
        reading v k i ≤ 3*reading v k g ∨
          handoffOpening v k (handoffOpening v k R c) i=handoffOpening v k (handoffOpening v k R c) g) ∧
      (¬InWay (reading v k i) (handoffOpening v k R c) →
        handoffOpening v k (handoffOpening v k R c) g ≤ closing (reading v k i) (handoffOpening v k R c))

theorem partner_iff_outsider_faces {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R : ℝ) (c f g : Fin 8)
    (h : Cohort v k R c) (hf : FastestCohort v k R f)
    (hTU : handoffOpening v k R c ≤ handoffOpening v k (handoffOpening v k R c) g) :
    PartnerConditions v k (handoffOpening v k R c) g ↔ OutsiderFaces v k R c f g := by
  have hclear : ∀ i : Fin 8, i≠k → InWay (reading v k i) R →
      ¬InWay (reading v k i) (handoffOpening v k R c) := by
    intro i hi hw hn
    exact (cohort_capture_outside hv k R c h i hi hn) hw
  constructor
  · intro hb
    refine ⟨?_,fun i hi hold=>hb i hi⟩
    apply (fastest_retention_iff hv k R _ c f h hf hTU).1
    intro i hi hw
    have hp : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
    apply (zero_iff_original_upper _ _ _ hp.le hTU).2
    have hh := (le_div_iff₀ hp).1 ((hb i hi).2 (hclear i hi hw))
    simpa only [closing,mul_comm] using hh
  · intro hb i hi
    by_cases hw : InWay (reading v k i) R
    · refine ⟨fun hn=>(hclear i hi hw hn).elim,fun _=>?_⟩
      have hp : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
      have hz := (fastest_retention_iff hv k R _ c f h hf hTU).2 hb.1 i hi hw
      have hu := (zero_iff_original_upper _ _ _ hp.le hTU).1 hz
      apply (le_div_iff₀ hp).2
      simpa only [closing,mul_comm] using hu
    · exact hb.2 i hi hw

-- STANDING: DEFINITION
noncomputable def OutsiderPartnerClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (R : ℝ) (c f g : Fin 8), 0<R ∧ Cohort v k R c ∧ FastestCohort v k R f ∧
    g≠k ∧ InWay (reading v k g) (handoffOpening v k R c) ∧
    (∀ i : Fin 8, i≠k → ¬InWay (reading v k i) R →
      InWay (reading v k i) (handoffOpening v k R c) →
      handoffOpening v k (handoffOpening v k R c) i ≤ handoffOpening v k (handoffOpening v k R c) g) ∧
    OutsiderFaces v k R c f g

theorem outsiderPartner_into_partner {v : Fin 8 → ℝ} {k : Fin 8} (h : OutsiderPartnerClass v k) : PartnerClass v k := by
  obtain ⟨hv,R,c,f,g,hR,hco,hf,hg,hwg,ho,hfaces⟩ := h
  have ht := outsider_forces_move hv k R c g hco hg hwg ho
  have hRT := le_of_isMove (disparitySet_pos hv k) (cohort_move hv k R c hco.1 hco.2.1 hco.2.2)
  exact ⟨hv,handoffOpening v k R c,g,lt_of_lt_of_le hR hRT,hg,hwg,ht.2,
    (partner_iff_outsider_faces hv k R c f g hco hf ht.1.le).2 hfaces⟩

theorem outsiderPartner_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : OutsiderPartnerClass v k) : Isolation v k :=
  partner_isolation (outsiderPartner_into_partner h)

-- STANDING: DEFINITION
noncomputable def OutsiderRecoveryClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (R : ℝ) (c g : Fin 8), 0<R ∧ Cohort v k R c ∧
    g≠k ∧ InWay (reading v k g) (handoffOpening v k R c) ∧
    (∀ i : Fin 8, i≠k → ¬InWay (reading v k i) R →
      InWay (reading v k i) (handoffOpening v k R c) →
      handoffOpening v k (handoffOpening v k R c) i ≤ handoffOpening v k (handoffOpening v k R c) g) ∧
    (∀ i : Fin 8, i≠k → InWay (reading v k i) R →
      (advance (reading v k i) (handoffOpening v k R c) (handoffOpening v k (handoffOpening v k R c) g) : ℝ) ≤
        reading v k i*(handoffOpening v k (handoffOpening v k R c) g-handoffOpening v k R c)) ∧
    (∀ i : Fin 8, i≠k → ¬InWay (reading v k i) R →
      0<advance (reading v k i) (handoffOpening v k R c) (handoffOpening v k (handoffOpening v k R c) g) →
      reading v k g*((label (reading v k i*handoffOpening v k (handoffOpening v k R c) g) : ℝ)+1/8) ≤
        reading v k i*((label (reading v k g*handoffOpening v k R c) : ℝ)+1/8))

theorem outsiderRecovery_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : OutsiderRecoveryClass v k) :
    Fresh.NativeCanonicalReturn.CanonicalReturnClass v k := by
  obtain ⟨hv,R,c,g,hR,hco,hg,hw,ho,hrec,hout⟩ := h
  have ht := outsider_forces_move hv k R c g hco hg hw ho
  have hRT := le_of_isMove (disparitySet_pos hv k) (cohort_move hv k R c hco.1 hco.2.1 hco.2.2)
  have hcap := capture_at_label (reading v k g) (handoffOpening v k R c) hw
  refine ⟨hv,g,handoffOpening v k R c,label (reading v k g*handoffOpening v k R c),hg,
    lt_of_lt_of_le hR hRT,hcap.1,hcap.2,ht.2,?_⟩
  intro i hi ha
  by_cases hold : InWay (reading v k i) R
  · have hclear := (cohort_recovery_iff hv k R _ c hco ht.1.le i hi hold).2 (hrec i hi hold)
    have hlower := le_of_not_gt (fun hh=>hclear ((inWay_iff_lower_not_passed _ _).2 hh))
    have hp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
    have hm := mul_le_mul_of_nonneg_left hlower hp.le
    have hopen := handoff_identity hv k g (handoffOpening v k R c) hg
    have hid := congrArg (fun x : ℝ=>reading v k i*x) hopen
    change reading v k g*((label (reading v k i*handoffOpening v k (handoffOpening v k R c) g) : ℝ)+1/8) ≤
      reading v k i*((label (reading v k g*handoffOpening v k R c) : ℝ)+1/8)
    nlinarith only [hm,hid]
  · exact hout i hi hold ha

theorem outsiderRecovery_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : OutsiderRecoveryClass v k) : Isolation v k :=
  Fresh.NativeCanonicalReturn.canonical_isolation (outsiderRecovery_into_canonical h)

#print axioms outsiderRecovery_into_canonical

#print axioms clear_from_opening_iff
#print axioms cohort_recovery_iff
#print axioms outsiderRecovery_isolation

#print axioms guard_of_ratio
#print axioms returned_cohort_forces_slow_setter
#print axioms label_at_opening
#print axioms zero_from_opening_iff
#print axioms capture_from_opening_iff
#print axioms cohort_opening_identity
#print axioms exists_fastest
#print axioms fastest_retention_iff
#print axioms outsider_forces_move
#print axioms partner_iff_outsider_faces
#print axioms outsiderPartner_into_partner
#print axioms outsiderPartner_isolation
end Fresh.NativeCohortOutsiderRelay
