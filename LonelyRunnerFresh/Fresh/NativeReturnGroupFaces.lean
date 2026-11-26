import Fresh.NativeReturnFaceHandoff

/-! Mixed recovered/captured return groups have their own first current
closing boundary. Its native sharp face characterizes group reset exactly;
the original nonreturner boundary remains the independent second front. -/
namespace Fresh.NativeReturnGroupFaces
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement Fresh.NativeReturnClosingOrder
  Fresh.NativeReturnGroupRelay Fresh.NativeReturnGroupArrangement

noncomputable def GroupFirst (v : Fin 8 → ℝ) (k : Fin 8) (P R : ℝ) (g : Fin 8) : Prop :=
  g≠k ∧ 0 < advance (reading v k g) P R ∧
    ∀ i : Fin 8, i≠k → 0 < advance (reading v k i) P R →
      reading v k i*((label (reading v k g*R) : ℝ)+7/8)≤reading v k g*((label (reading v k i*R) : ℝ)+7/8)

noncomputable def SharpGroup (v : Fin 8 → ℝ) (k : Fin 8) (P R : ℝ) (c g : Fin 8) : Prop :=
  GroupFirst v k P R g ∧ reading v k g*((label (reading v k c*R) : ℝ)+1/8-reading v k c*R)≤
    reading v k c*((label (reading v k g*R) : ℝ)+7/8-reading v k g*R)

noncomputable def QuarterGroup (v : Fin 8 → ℝ) (k : Fin 8) (P R : ℝ) (c g : Fin 8) : Prop :=
  GroupFirst v k P R g ∧ reading v k g/4≤reading v k c*((label (reading v k g*R) : ℝ)+7/8-reading v k g*R)

theorem exists_group_first {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ) (c : Fin 8)
    (hc : Survivor v k P R c) : ∃ g : Fin 8, GroupFirst v k P R g := by
  classical
  let S := Finset.univ.filter (fun i : Fin 8=>i≠k ∧ 0 < advance (reading v k i) P R)
  have hne : S.Nonempty := ⟨c,by simp [S,hc.1,hc.2.1]⟩
  obtain ⟨g,hg,hmin⟩ := Finset.exists_min_image S (fun i=>closing (reading v k i) R) hne
  have hgm := (Finset.mem_filter.mp hg).2
  refine ⟨g,hgm.1,hgm.2,?_⟩
  intro i hi ha
  have hgp : 0 < reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hgm.1,rfl⟩)
  have hip : 0 < reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  have hh := hmin i (by simp [S,hi,ha])
  dsimp [closing] at hh
  have hm := (div_le_div_iff₀ hgp hip).1 hh
  nlinarith only [hm]

theorem sharp_iff_group_zero {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c g : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (hg : GroupFirst v k P R g) :
    SharpGroup v k P R c g ↔ ∀ i : Fin 8, i≠k → 0 < advance (reading v k i) P R →
      advance (reading v k i) R (handoffOpening v k R c)=0 := by
  have ht := forced_handoff hv k P R hm c hc ho
  have hd : 0 < reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc.1,rfl⟩)
  have hgp : 0 < reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg.1,rfl⟩)
  have heq := Fresh.NativeFirstClosing.deficit_iff_upper (reading v k c) (reading v k g) R _
    (label (reading v k c*R)) (label (reading v k g*R)) hd (handoff_identity hv k c R hc.1)
  constructor
  · intro hs i hi ha
    apply (zero_iff_original_upper (reading v k i) R _ (abs_nonneg _) ht.1.le).2
    exact Fresh.NativeFirstClosing.propagate_upper _ _ _ _ _ (abs_nonneg _) hgp (heq.1 hs.2) (hg.2.2 i hi ha)
  · intro hz
    have hu := (zero_iff_original_upper (reading v k g) R _ (abs_nonneg _) ht.1.le).1 (hz g hg.1 hg.2.1)
    exact ⟨hg,heq.2 hu⟩

theorem sharp_into_reset {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c g : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (hs : SharpGroup v k P R c g) : Reset v k P R c :=
  ⟨hc,ho,(sharp_iff_group_zero hv k P R hm c g hc ho hs.1).1 hs⟩

theorem quarter_into_sharp {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c g : Fin 8) (hc : Survivor v k P R c)
    (hq : QuarterGroup v k P R c g) : SharpGroup v k P R c g := by
  have hcap := capture_at_label (reading v k c) R ((survivor_iff hv k P R hm c).1 hc).2
  exact ⟨hq.1,Fresh.NativeFirstClosing.quarter_implies_deficit _ _ R _ _ (abs_nonneg _) hcap.1 hq.2⟩

theorem compact_exists_quarter {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hb : CompactEntry v k P R c) :
    ∃ g : Fin 8, QuarterGroup v k P R c g := by
  obtain ⟨g,hg⟩ := exists_group_first hv k P R c hb.1
  have hh := hb.2.2 g hg.1 hg.2.1
  have hcap := capture_at_label (reading v k g) R hh.1
  have hd : 0≤reading v k c := abs_nonneg _
  have hmul := mul_nonneg hd (sub_nonneg.mpr hcap.2.le)
  exact ⟨g,hg,by nlinarith only [hmul,hh.2]⟩

-- STANDING: DEFINITION
noncomputable def SharpClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (Q P : ℝ) (j c g : Fin 8), HandoffEntry v k Q P j ∧
    Survivor v k P (handoffOpening v k P j) c ∧ OpeningOrder v k P (handoffOpening v k P j) c ∧
    SharpGroup v k P (handoffOpening v k P j) c g ∧ GroupFits v k P (handoffOpening v k P j) c

-- STANDING: DEFINITION
noncomputable def QuarterClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (Q P : ℝ) (j c g : Fin 8), HandoffEntry v k Q P j ∧
    Survivor v k P (handoffOpening v k P j) c ∧ OpeningOrder v k P (handoffOpening v k P j) c ∧
    QuarterGroup v k P (handoffOpening v k P j) c g ∧ GroupFits v k P (handoffOpening v k P j) c

theorem sharp_into_reset_class {v : Fin 8 → ℝ} {k : Fin 8} (h : SharpClass v k) : ResetClass v k := by
  obtain ⟨hv,Q,P,j,c,g,he,hc,ho,hs,hfit⟩ := h
  have ht := forced_handoff hv k Q P he.2.1 j he.2.2.1 he.2.2.2
  exact ⟨hv,Q,P,j,c,he,sharp_into_reset hv k P _ ht.2 c g hc ho hs,hfit⟩

theorem reset_class_into_sharp {v : Fin 8 → ℝ} {k : Fin 8} (h : ResetClass v k) : SharpClass v k := by
  obtain ⟨hv,Q,P,j,c,he,hr,hfit⟩ := h
  have ht := forced_handoff hv k Q P he.2.1 j he.2.2.1 he.2.2.2
  obtain ⟨g,hg⟩ := exists_group_first hv k P _ c hr.1
  exact ⟨hv,Q,P,j,c,g,he,hr.1,hr.2.1,(sharp_iff_group_zero hv k P _ ht.2 c g hr.1 hr.2.1 hg).2 hr.2.2,hfit⟩

theorem quarter_into_sharp_class {v : Fin 8 → ℝ} {k : Fin 8} (h : QuarterClass v k) : SharpClass v k := by
  obtain ⟨hv,Q,P,j,c,g,he,hc,ho,hq,hfit⟩ := h
  have ht := forced_handoff hv k Q P he.2.1 j he.2.2.1 he.2.2.2
  exact ⟨hv,Q,P,j,c,g,he,hc,ho,quarter_into_sharp hv k P _ ht.2 c g hc hq,hfit⟩

theorem compact_into_quarter_class {v : Fin 8 → ℝ} {k : Fin 8} (h : CompactClass v k) : QuarterClass v k := by
  obtain ⟨hv,Q,P,j,c,he,hb,hfit⟩ := h
  have ht := forced_handoff hv k Q P he.2.1 j he.2.2.1 he.2.2.2
  obtain ⟨g,hg⟩ := compact_exists_quarter hv k P _ ht.2 c hb
  exact ⟨hv,Q,P,j,c,g,he,hb.1,hb.2.1,hg,hfit⟩

theorem sharp_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : SharpClass v k) : Isolation v k :=
  handoff_noReturn_isolation (reset_into_noReturn (sharp_into_reset_class h))

theorem quarter_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : QuarterClass v k) : Isolation v k :=
  sharp_isolation (quarter_into_sharp_class h)

#print axioms exists_group_first
#print axioms sharp_iff_group_zero
#print axioms sharp_into_reset
#print axioms quarter_into_sharp
#print axioms compact_exists_quarter
#print axioms sharp_into_reset_class
#print axioms reset_class_into_sharp
#print axioms quarter_into_sharp_class
#print axioms compact_into_quarter_class
#print axioms sharp_isolation
#print axioms quarter_isolation
end Fresh.NativeReturnGroupFaces
