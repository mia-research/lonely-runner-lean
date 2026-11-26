import Fresh.NativeCohortOutsiderRelay

/-! Recaptured members of a prior shared-opening cohort have openings
T + m_i/s_i, retaining independent unbounded return labels. Their exact
order joins the original outsiders' actual openings in all three fronts. -/
namespace Fresh.NativeCohortReturnOrder
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement Fresh.NativeReturnClosingOrder
  Fresh.NativeCapturedPartnerJoin Fresh.NativeCohortReturns Fresh.NativeCohortOutsiderRelay

theorem return_opening {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R U : ℝ) (c i : Fin 8)
    (h : Cohort v k R c) (hTU : handoffOpening v k R c ≤ U) (hi : i≠k) (hw : InWay (reading v k i) R) :
    handoffOpening v k U i=handoffOpening v k R c+
      (advance (reading v k i) (handoffOpening v k R c) U : ℝ)/reading v k i := by
  have hp : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  have hT := cohort_opening_identity hv k R c h i hi hw
  have hl := advance_identity (reading v k i) (handoffOpening v k R c) U hp.le hTU
  rw [label_at_opening _ _ _ hT] at hl
  have hlR : (label (reading v k i*U) : ℝ)=(label (reading v k i*R) : ℝ)+
      (advance (reading v k i) (handoffOpening v k R c) U : ℝ) := by exact_mod_cast hl
  have hU := handoff_identity hv k i U hi
  rw [hlR] at hU
  have he : handoffOpening v k U i-handoffOpening v k R c=
      (advance (reading v k i) (handoffOpening v k R c) U : ℝ)/reading v k i := by
    apply (eq_div_iff hp.ne').2
    nlinarith only [hT,hU]
  linarith only [he]

theorem return_order_iff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R U : ℝ) (c i j : Fin 8)
    (h : Cohort v k R c) (hTU : handoffOpening v k R c ≤ U) (hi : i≠k) (hj : j≠k)
    (hwi : InWay (reading v k i) R) (hwj : InWay (reading v k j) R) :
    handoffOpening v k U i ≤ handoffOpening v k U j ↔
      (advance (reading v k i) (handoffOpening v k R c) U : ℝ)*reading v k j ≤
        (advance (reading v k j) (handoffOpening v k R c) U : ℝ)*reading v k i := by
  have hip : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  have hjp : 0<reading v k j := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨j,hj,rfl⟩)
  rw [return_opening hv k R U c i h hTU hi hwi,return_opening hv k R U c j h hTU hj hwj,
    add_le_add_iff_left,div_le_div_iff₀ hip hjp]

theorem return_opening_le_iff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R U V : ℝ) (c i : Fin 8)
    (h : Cohort v k R c) (hTU : handoffOpening v k R c ≤ U) (hi : i≠k) (hw : InWay (reading v k i) R) :
    handoffOpening v k U i ≤ V ↔
      (advance (reading v k i) (handoffOpening v k R c) U : ℝ) ≤ reading v k i*(V-handoffOpening v k R c) := by
  have hp : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  rw [return_opening hv k R U c i h hTU hi hw]
  have hh := (div_le_iff₀ hp :
    (advance (reading v k i) (handoffOpening v k R c) U : ℝ)/reading v k i ≤ V-handoffOpening v k R c ↔
      (advance (reading v k i) (handoffOpening v k R c) U : ℝ) ≤ (V-handoffOpening v k R c)*reading v k i)

  constructor
  · intro he
    have hle : (advance (reading v k i) (handoffOpening v k R c) U : ℝ)/reading v k i ≤ V-handoffOpening v k R c := by linarith only [he]
    have hx := hh.1 hle
    nlinarith only [hx]
  · intro he
    have hle := hh.2 (by nlinarith only [he])
    linarith only [hle]

theorem same_level_order {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R U : ℝ) (c i j : Fin 8)
    (h : Cohort v k R c) (hTU : handoffOpening v k R c ≤ U) (hi : i≠k) (hj : j≠k)
    (hwi : InWay (reading v k i) R) (hwj : InWay (reading v k j) R)
    (hm : advance (reading v k i) (handoffOpening v k R c) U=
      advance (reading v k j) (handoffOpening v k R c) U)
    (hpos : 0<advance (reading v k j) (handoffOpening v k R c) U) :
    handoffOpening v k U i ≤ handoffOpening v k U j ↔ reading v k j ≤ reading v k i := by
  rw [return_order_iff hv k R U c i j h hTU hi hj hwi hwj,hm]
  have hp : (0 : ℝ)<(advance (reading v k j) (handoffOpening v k R c) U : ℝ) := by exact_mod_cast hpos
  constructor <;> intro hh <;> nlinarith only [hh,hp]

theorem recapture_positive {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R U : ℝ) (c i : Fin 8)
    (h : Cohort v k R c) (hTU : handoffOpening v k R c ≤ U) (hi : i≠k)
    (hold : InWay (reading v k i) R) (hnow : InWay (reading v k i) U) :
    0<advance (reading v k i) (handoffOpening v k R c) U := by
  have hh := (capture_from_opening_iff _ _ U _ (show 0 ≤ reading v k i from abs_nonneg _) hTU
    (cohort_opening_identity hv k R c h i hi hold)).1 hnow
  have hn := mul_nonneg (show 0 ≤ reading v k i from abs_nonneg _) (sub_nonneg.mpr hTU)
  have hp : (0 : ℝ)<(advance (reading v k i) (handoffOpening v k R c) U : ℝ) := lt_of_le_of_lt hn hh.2
  exact_mod_cast hp

noncomputable def LevelFrontier (v : Fin 8 → ℝ) (k : Fin 8) (R U : ℝ) (c i : Fin 8) : Prop :=
  i≠k ∧ InWay (reading v k i) R ∧ InWay (reading v k i) U ∧
    ∀ j : Fin 8, j≠k → InWay (reading v k j) R → InWay (reading v k j) U →
      advance (reading v k j) (handoffOpening v k R c) U=advance (reading v k i) (handoffOpening v k R c) U →
      reading v k i ≤ reading v k j

theorem exists_level_frontier {v : Fin 8 → ℝ} (k : Fin 8) (R U : ℝ) (c i : Fin 8)
    (hi : i≠k) (hold : InWay (reading v k i) R) (hnow : InWay (reading v k i) U) :
    ∃ j : Fin 8, LevelFrontier v k R U c j ∧
      advance (reading v k i) (handoffOpening v k R c) U=advance (reading v k j) (handoffOpening v k R c) U := by
  classical
  let S := Finset.univ.filter (fun j : Fin 8=>j≠k ∧ InWay (reading v k j) R ∧ InWay (reading v k j) U ∧
    advance (reading v k j) (handoffOpening v k R c) U=advance (reading v k i) (handoffOpening v k R c) U)
  have himem : i∈S := by simp [S,hi,hold,hnow]
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image S (reading v k) ⟨i,himem⟩
  have hjm := (Finset.mem_filter.mp hj).2
  refine ⟨j,⟨hjm.1,hjm.2.1,hjm.2.2.1,?_⟩,hjm.2.2.2.symm⟩
  intro q hq hqold hqnow hlevel
  apply hmin q
  simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨hq,hqold,hqnow,hlevel.trans hjm.2.2.2⟩

theorem frontier_order_iff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R U V : ℝ) (c : Fin 8)
    (h : Cohort v k R c) (hTU : handoffOpening v k R c ≤ U) :
    (∀ i : Fin 8, i≠k → InWay (reading v k i) R → InWay (reading v k i) U → handoffOpening v k U i ≤ V) ↔
      ∀ j : Fin 8, LevelFrontier v k R U c j → handoffOpening v k U j ≤ V := by
  constructor
  · intro hall j hj
    exact hall j hj.1 hj.2.1 hj.2.2.1
  · intro hfront i hi hold hnow
    obtain ⟨j,hj,hm⟩ := exists_level_frontier k R U c i hi hold hnow
    have hpos := recapture_positive hv k R U c j h hTU hj.1 hj.2.1 hj.2.2.1
    have hle := (same_level_order hv k R U c i j h hTU hi hj.1 hold hj.2.1 hm hpos).2
      (hj.2.2.2 i hi hold hnow hm)
    exact le_trans hle (hfront j hj)

noncomputable def ReturnOrder (v : Fin 8 → ℝ) (k : Fin 8) (R U : ℝ) (c g : Fin 8) : Prop :=
  ∀ i : Fin 8, i≠k → InWay (reading v k i) U →
    (InWay (reading v k i) R →
      (advance (reading v k i) (handoffOpening v k R c) U : ℝ) ≤
        reading v k i*(handoffOpening v k U g-handoffOpening v k R c)) ∧
    (¬InWay (reading v k i) R → handoffOpening v k U i ≤ handoffOpening v k U g)

theorem return_order_forces_move {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R U : ℝ) (c g : Fin 8)
    (h : Cohort v k R c) (hTU : handoffOpening v k R c ≤ U) (hg : g≠k)
    (hwg : InWay (reading v k g) U) (ho : ReturnOrder v k R U c g) :
    U<handoffOpening v k U g ∧ IsMove (disparitySet v k) U (handoffOpening v k U g) := by
  have hp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  constructor
  · have hh := lt_nextOpening hp hwg
    rw [next_at_label _ _ hwg] at hh
    exact hh
  · refine Or.inr ⟨reading v k g,mem_disparitySet.mpr ⟨g,hg,rfl⟩,hwg,(next_at_label _ _ hwg).symm,?_⟩
    intro s hs hws
    obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hs
    change InWay (reading v k i) U at hws
    change nextOpening (reading v k i) U ≤ _
    rw [next_at_label _ _ hws]
    by_cases hold : InWay (reading v k i) R
    · exact (return_opening_le_iff hv k R U _ c i h hTU hi hold).2 ((ho i hi hws).1 hold)
    · exact (ho i hi hws).2 hold

theorem same_level_forces_move {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R U : ℝ) (c g : Fin 8)
    (h : Cohort v k R c) (hTU : handoffOpening v k R c ≤ U) (hg : g≠k)
    (hwg : InWay (reading v k g) U)
    (horig : ∀ i : Fin 8, i≠k → InWay (reading v k i) U → InWay (reading v k i) R)
    (hm : ∀ i : Fin 8, i≠k → InWay (reading v k i) U →
      advance (reading v k i) (handoffOpening v k R c) U=advance (reading v k g) (handoffOpening v k R c) U)
    (hslow : ∀ i : Fin 8, i≠k → InWay (reading v k i) U → reading v k g ≤ reading v k i) :
    U<handoffOpening v k U g ∧ IsMove (disparitySet v k) U (handoffOpening v k U g) := by
  apply return_order_forces_move hv k R U c g h hTU hg hwg
  intro i hi hw
  have hh := return_opening hv k R U c i h hTU hi (horig i hi hw)
  have hgopen := return_opening hv k R U c g h hTU hg (horig g hg hwg)
  have hnon : (0 : ℝ) ≤ (advance (reading v k g) (handoffOpening v k R c) U : ℝ) := by positivity
  have hip : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  have hgp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have hdiv := div_le_div_of_nonneg_left hnon hgp (hslow i hi hw)
  have hle : handoffOpening v k U i ≤ handoffOpening v k U g := by rw [hh,hgopen,hm i hi hw]; linarith only [hdiv]
  exact ⟨fun hold=>(return_opening_le_iff hv k R U _ c i h hTU hi hold).1 hle,
    fun hn=>(hn (horig i hi hw)).elim⟩

theorem frontier_forces_move {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R U : ℝ) (c g : Fin 8)
    (h : Cohort v k R c) (hTU : handoffOpening v k R c ≤ U) (hg : g≠k) (hw : InWay (reading v k g) U)
    (hf : ∀ i : Fin 8, LevelFrontier v k R U c i → handoffOpening v k U i ≤ handoffOpening v k U g)
    (he : ∀ i : Fin 8, i≠k → ¬InWay (reading v k i) R → InWay (reading v k i) U →
      handoffOpening v k U i ≤ handoffOpening v k U g) :
    U<handoffOpening v k U g ∧ IsMove (disparitySet v k) U (handoffOpening v k U g) := by
  apply return_order_forces_move hv k R U c g h hTU hg hw
  intro i hi hnow
  exact ⟨fun hold=>(return_opening_le_iff hv k R U _ c i h hTU hi hold).1
    ((frontier_order_iff hv k R U _ c h hTU).2 hf i hi hold hnow),fun hold=>he i hi hold hnow⟩

-- STANDING: DEFINITION
noncomputable def ReturnPartnerClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (R U : ℝ) (c g : Fin 8), 0<R ∧ Cohort v k R c ∧
    handoffOpening v k R c ≤ U ∧ g≠k ∧ InWay (reading v k g) U ∧
    ReturnOrder v k R U c g ∧ PartnerConditions v k U g

theorem returnPartner_into_partner {v : Fin 8 → ℝ} {k : Fin 8} (h : ReturnPartnerClass v k) : PartnerClass v k := by
  obtain ⟨hv,R,U,c,g,hR,hco,hTU,hg,hw,ho,hp⟩ := h
  have ht := return_order_forces_move hv k R U c g hco hTU hg hw ho
  have hRT := le_of_isMove (disparitySet_pos hv k) (cohort_move hv k R c hco.1 hco.2.1 hco.2.2)
  exact ⟨hv,U,g,lt_of_lt_of_le hR (le_trans hRT hTU),hg,hw,ht.2,hp⟩

theorem returnPartner_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ReturnPartnerClass v k) : Isolation v k :=
  partner_isolation (returnPartner_into_partner h)

-- STANDING: DEFINITION
noncomputable def ReturnRecoveryClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (R U : ℝ) (c g : Fin 8), 0<R ∧ Cohort v k R c ∧
    handoffOpening v k R c ≤ U ∧ g≠k ∧ InWay (reading v k g) U ∧ ReturnOrder v k R U c g ∧
    (∀ i : Fin 8, i≠k → InWay (reading v k i) R →
      (advance (reading v k i) (handoffOpening v k R c) (handoffOpening v k U g) : ℝ) ≤
        reading v k i*(handoffOpening v k U g-handoffOpening v k R c)) ∧
    (∀ i : Fin 8, i≠k → ¬InWay (reading v k i) R → 0<advance (reading v k i) U (handoffOpening v k U g) →
      reading v k g*((label (reading v k i*handoffOpening v k U g) : ℝ)+1/8) ≤
        reading v k i*((label (reading v k g*U) : ℝ)+1/8))

theorem returnRecovery_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : ReturnRecoveryClass v k) :
    Fresh.NativeCanonicalReturn.CanonicalReturnClass v k := by
  obtain ⟨hv,R,U,c,g,hR,hco,hTU,hg,hw,ho,hrec,hout⟩ := h
  have ht := return_order_forces_move hv k R U c g hco hTU hg hw ho
  have hRT := le_of_isMove (disparitySet_pos hv k) (cohort_move hv k R c hco.1 hco.2.1 hco.2.2)
  have hcap := capture_at_label (reading v k g) U hw
  refine ⟨hv,g,U,label (reading v k g*U),hg,lt_of_lt_of_le hR (le_trans hRT hTU),hcap.1,hcap.2,ht.2,?_⟩
  intro i hi ha
  by_cases hold : InWay (reading v k i) R
  · have hclear := (cohort_recovery_iff hv k R _ c hco (le_trans hTU ht.1.le) i hi hold).2 (hrec i hi hold)
    have hlower := le_of_not_gt (fun hh=>hclear ((inWay_iff_lower_not_passed _ _).2 hh))
    have hp : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
    have hm := mul_le_mul_of_nonneg_left hlower hp.le
    have hid := congrArg (fun x : ℝ=>reading v k i*x) (handoff_identity hv k g U hg)
    change reading v k g*((label (reading v k i*handoffOpening v k U g) : ℝ)+1/8) ≤
      reading v k i*((label (reading v k g*U) : ℝ)+1/8)
    nlinarith only [hm,hid]
  · exact hout i hi hold ha

theorem returnRecovery_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ReturnRecoveryClass v k) : Isolation v k :=
  Fresh.NativeCanonicalReturn.canonical_isolation (returnRecovery_into_canonical h)

theorem return_closing {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R U : ℝ) (c i : Fin 8)
    (h : Cohort v k R c) (hTU : handoffOpening v k R c ≤ U) (hi : i≠k) (hw : InWay (reading v k i) R) :
    closing (reading v k i) U=handoffOpening v k R c+
      ((advance (reading v k i) (handoffOpening v k R c) U : ℝ)+3/4)/reading v k i := by
  have hp : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  have hT := cohort_opening_identity hv k R c h i hi hw
  have hl := advance_identity (reading v k i) (handoffOpening v k R c) U hp.le hTU
  rw [label_at_opening _ _ _ hT] at hl
  have hlR : (label (reading v k i*U) : ℝ)=(label (reading v k i*R) : ℝ)+
      (advance (reading v k i) (handoffOpening v k R c) U : ℝ) := by exact_mod_cast hl
  dsimp [closing]
  apply (div_eq_iff hp.ne').2
  have hcancel := div_mul_cancel₀
    ((advance (reading v k i) (handoffOpening v k R c) U : ℝ)+3/4) hp.ne'
  nlinarith only [hT,hlR,hcancel]

noncomputable def ClosingFrontier (v : Fin 8 → ℝ) (k : Fin 8) (R U : ℝ) (c i : Fin 8) : Prop :=
  i≠k ∧ InWay (reading v k i) R ∧
    ∀ j : Fin 8, j≠k → InWay (reading v k j) R →
      advance (reading v k j) (handoffOpening v k R c) U=advance (reading v k i) (handoffOpening v k R c) U →
      reading v k j ≤ reading v k i

theorem exists_closing_frontier {v : Fin 8 → ℝ} (k : Fin 8) (R U : ℝ) (c i : Fin 8)
    (hi : i≠k) (hold : InWay (reading v k i) R) :
    ∃ j : Fin 8, ClosingFrontier v k R U c j ∧
      advance (reading v k i) (handoffOpening v k R c) U=advance (reading v k j) (handoffOpening v k R c) U := by
  classical
  let S := Finset.univ.filter (fun j : Fin 8=>j≠k ∧ InWay (reading v k j) R ∧
    advance (reading v k j) (handoffOpening v k R c) U=advance (reading v k i) (handoffOpening v k R c) U)
  have himem : i∈S := by simp [S,hi,hold]
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image S (reading v k) ⟨i,himem⟩
  have hjm := (Finset.mem_filter.mp hj).2
  refine ⟨j,⟨hjm.1,hjm.2.1,?_⟩,hjm.2.2.symm⟩
  intro q hq hqold hlevel
  apply hmax q
  simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨hq,hqold,hlevel.trans hjm.2.2⟩

theorem frontier_closing_iff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R U V : ℝ) (c : Fin 8)
    (h : Cohort v k R c) (hTU : handoffOpening v k R c ≤ U) :
    (∀ i : Fin 8, i≠k → InWay (reading v k i) R → V ≤ closing (reading v k i) U) ↔
      ∀ j : Fin 8, ClosingFrontier v k R U c j → V ≤ closing (reading v k j) U := by
  constructor
  · intro hall j hj
    exact hall j hj.1 hj.2.1
  · intro hfront i hi hold
    obtain ⟨j,hj,hm⟩ := exists_closing_frontier k R U c i hi hold
    have hip : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
    have hjp : 0<reading v k j := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨j,hj.1,rfl⟩)
    have hn : (0 : ℝ) ≤ (advance (reading v k j) (handoffOpening v k R c) U : ℝ)+3/4 := by positivity
    have hdiv := div_le_div_of_nonneg_left hn hip (hj.2.2 i hi hold hm)
    have hle : closing (reading v k j) U ≤ closing (reading v k i) U := by
      rw [return_closing hv k R U c i h hTU hi hold,return_closing hv k R U c j h hTU hj.1 hj.2.1,hm]
      linarith only [hdiv]
    exact le_trans (hfront j hj) hle

-- STANDING: DEFINITION
noncomputable def FrontierRetainedClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (R U : ℝ) (c g : Fin 8), 0<R ∧ Cohort v k R c ∧
    handoffOpening v k R c ≤ U ∧ g≠k ∧ InWay (reading v k g) U ∧
    (∀ i : Fin 8, LevelFrontier v k R U c i → handoffOpening v k U i ≤ handoffOpening v k U g) ∧
    (∀ i : Fin 8, i≠k → ¬InWay (reading v k i) R → InWay (reading v k i) U → handoffOpening v k U i ≤ handoffOpening v k U g) ∧
    (∀ i : Fin 8, ClosingFrontier v k R U c i → handoffOpening v k U g ≤ closing (reading v k i) U) ∧
    (∀ i : Fin 8, i≠k → ¬InWay (reading v k i) R → handoffOpening v k U g ≤ closing (reading v k i) U)

theorem frontierRetained_into_noReturn {v : Fin 8 → ℝ} {k : Fin 8} (h : FrontierRetainedClass v k) :
    Fresh.NativeCanonicalReturn.NoReturnClass v k := by
  obtain ⟨hv,R,U,c,g,hR,hco,hTU,hg,hw,hf,he,hclose,hout⟩ := h
  have ht := frontier_forces_move hv k R U c g hco hTU hg hw hf he
  have hRT := le_of_isMove (disparitySet_pos hv k) (cohort_move hv k R c hco.1 hco.2.1 hco.2.2)
  have hcap := capture_at_label (reading v k g) U hw
  refine ⟨hv,g,U,label (reading v k g*U),hg,lt_of_lt_of_le hR (le_trans hRT hTU),hcap.1,hcap.2,ht.2,?_⟩
  intro i hi
  have hp : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  have hci : handoffOpening v k U g ≤ closing (reading v k i) U := by
    by_cases hold : InWay (reading v k i) R
    · exact (frontier_closing_iff hv k R U _ c hco hTU).2 hclose i hi hold
    · exact hout i hi hold
  apply (zero_iff_original_upper _ _ _ hp.le ht.1.le).2
  have hh := (le_div_iff₀ hp).1 hci
  simpa only [closing,mul_comm] using hh

theorem frontierRetained_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : FrontierRetainedClass v k) : Isolation v k :=
  Fresh.NativeCanonicalReturn.noReturn_isolation (frontierRetained_into_noReturn h)

#print axioms return_closing
#print axioms exists_closing_frontier
#print axioms frontier_closing_iff
#print axioms frontierRetained_into_noReturn
#print axioms frontierRetained_isolation

#print axioms recapture_positive
#print axioms exists_level_frontier
#print axioms frontier_order_iff
#print axioms frontier_forces_move
#print axioms return_opening
#print axioms return_order_iff
#print axioms return_opening_le_iff
#print axioms same_level_order
#print axioms return_order_forces_move
#print axioms same_level_forces_move
#print axioms returnPartner_into_partner
#print axioms returnPartner_isolation
#print axioms returnRecovery_into_canonical
#print axioms returnRecovery_isolation
end Fresh.NativeCohortReturnOrder
