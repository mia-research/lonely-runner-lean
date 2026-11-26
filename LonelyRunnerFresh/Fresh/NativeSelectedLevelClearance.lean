import Fresh.NativeCohortReturnOrder

/-! Equal positive return levels force compact disparities. An actual setter
clears its entire currently captured level, independently of other levels and
outsiders. This is a local discharge, not a decreasing-level assertion. -/
namespace Fresh.NativeSelectedLevelClearance
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement Fresh.NativeReturnClosingOrder
  Fresh.NativeCapturedPartnerJoin Fresh.NativeCohortReturns Fresh.NativeCohortOutsiderRelay
  Fresh.NativeCohortReturnOrder

theorem equal_level_compact (s d q : ℝ) (m : ℕ) (hm : 0 < m) (hq : 0 ≤ q)
    (hs : (m : ℝ)-1/4<s*q ∧ s*q<(m : ℝ))
    (hd : (m : ℝ)-1/4<d*q ∧ d*q<(m : ℝ)) : 3*s<4*d := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  by_contra hn
  have hx := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hq
  nlinarith only [hs.2,hd.1,hx,hmR]

theorem equal_level_sharp (s d q : ℝ) (m : ℕ) (hm : 0 < m) (hq : 0 ≤ q)
    (hs : (m : ℝ)-1/4<s*q ∧ s*q<(m : ℝ))
    (hd : (m : ℝ)-1/4<d*q ∧ d*q<(m : ℝ)) :
    (4*(m : ℝ)-1)*s<4*(m : ℝ)*d := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsx := mul_lt_mul_of_pos_left hs.2 (by linarith : 0<4*(m : ℝ)-1)
  have hdx := mul_lt_mul_of_pos_left hd.1 (by linarith : 0<4*(m : ℝ))
  by_contra hn
  have hx := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hq
  nlinarith only [hsx,hdx,hx]

theorem same_level_compact {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R U : ℝ) (c i g : Fin 8)
    (h : Cohort v k R c) (hTU : handoffOpening v k R c ≤ U) (hi : i≠k) (hg : g≠k)
    (hiold : InWay (reading v k i) R) (hgold : InWay (reading v k g) R)
    (hinow : InWay (reading v k i) U) (hgnow : InWay (reading v k g) U)
    (hm : advance (reading v k i) (handoffOpening v k R c) U=
      advance (reading v k g) (handoffOpening v k R c) U) : 3*reading v k i<4*reading v k g := by
  have hip := (capture_from_opening_iff _ _ U _ (show 0 ≤ reading v k i from abs_nonneg _) hTU
    (cohort_opening_identity hv k R c h i hi hiold)).1 hinow
  have hgp := (capture_from_opening_iff _ _ U _ (show 0 ≤ reading v k g from abs_nonneg _) hTU
    (cohort_opening_identity hv k R c h g hg hgold)).1 hgnow
  rw [hm] at hip
  exact equal_level_compact _ _ _ _ (recapture_positive hv k R U c g h hTU hg hgold hgnow)
    (sub_nonneg.mpr hTU) hip hgp

theorem selected_level_zero {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R U : ℝ) (c i g : Fin 8)
    (h : Cohort v k R c) (hTU : handoffOpening v k R c ≤ U) (hi : i≠k) (hg : g≠k)
    (hiold : InWay (reading v k i) R) (hgold : InWay (reading v k g) R)
    (hinow : InWay (reading v k i) U) (hgnow : InWay (reading v k g) U)
    (hm : advance (reading v k i) (handoffOpening v k R c) U=
      advance (reading v k g) (handoffOpening v k R c) U)
    (hmove : IsMove (disparitySet v k) U (handoffOpening v k U g)) :
    advance (reading v k i) U (handoffOpening v k U g)=0 := by
  have hd : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have hc := same_level_compact hv k R U c i g h hTU hi hg hiold hgold hinow hgnow hm
  have hratio : reading v k i ≤ 3*reading v k g := by nlinarith only [hc,hd]
  have hcg := capture_at_label (reading v k g) U hgnow
  have hci := capture_at_label (reading v k i) U hinow
  have hid := handoff_identity hv k g U hg
  have hmem : reading v k i∈disparitySet v k := mem_disparitySet.mpr ⟨i,hi,rfl⟩
  have horder := Fresh.FastestCaptureRecovery.captured_order_of_move _ _ hmove hmem hd
    (disparitySet_pos hv k _ hmem) hid hci.1 hci.2
  have hw := Fresh.NativeRelativeCapture.captured_window _ _ U _ _ _ hd hratio hid hcg.1 hcg.2 hci.2 horder
  have hl := (entry_iff_label _ _ _).1 (Or.inl ⟨hw.1,hw.2.le⟩)
  simp only [advance,hl,sub_self,Int.toNat_zero]

theorem selected_level_clear {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R U : ℝ) (c i g : Fin 8)
    (h : Cohort v k R c) (hTU : handoffOpening v k R c ≤ U) (hi : i≠k) (hg : g≠k)
    (hiold : InWay (reading v k i) R) (hgold : InWay (reading v k g) R)
    (hinow : InWay (reading v k i) U) (hgnow : InWay (reading v k g) U)
    (hm : advance (reading v k i) (handoffOpening v k R c) U=
      advance (reading v k g) (handoffOpening v k R c) U)
    (hmove : IsMove (disparitySet v k) U (handoffOpening v k U g)) :
    ¬InWay (reading v k i) (handoffOpening v k U g) :=
  not_lt.mpr (nonreturning_clear hv k U _ hmove i hi
    (selected_level_zero hv k R U c i g h hTU hi hg hiold hgold hinow hgnow hm hmove))

theorem next_capture_sources {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R U : ℝ) (c i g : Fin 8)
    (h : Cohort v k R c) (hTU : handoffOpening v k R c ≤ U) (hi : i≠k) (hg : g≠k)
    (hgold : InWay (reading v k g) R) (hgnow : InWay (reading v k g) U)
    (hmove : IsMove (disparitySet v k) U (handoffOpening v k U g))
    (hafter : InWay (reading v k i) (handoffOpening v k U g)) :
    ¬InWay (reading v k i) R ∨ ¬InWay (reading v k i) U ∨
      advance (reading v k i) (handoffOpening v k R c) U≠advance (reading v k g) (handoffOpening v k R c) U := by
  by_cases hold : InWay (reading v k i) R
  · by_cases hnow : InWay (reading v k i) U
    · exact Or.inr (Or.inr (fun hm=>(selected_level_clear hv k R U c i g h hTU hi hg hold hgold hnow hgnow hm hmove) hafter))
    · exact Or.inr (Or.inl hnow)
  · exact Or.inl hold

theorem homogeneous_forces_move {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R U : ℝ) (c : Fin 8) (m : ℕ)
    (h : Cohort v k R c) (hTU : handoffOpening v k R c ≤ U)
    (hne : ∃ i : Fin 8, i≠k ∧ InWay (reading v k i) U)
    (hlevel : ∀ i : Fin 8, i≠k → InWay (reading v k i) U →
      InWay (reading v k i) R ∧ advance (reading v k i) (handoffOpening v k R c) U=m) :
    ∃ g : Fin 8, g≠k ∧ InWay (reading v k g) U ∧ U<handoffOpening v k U g ∧
      IsMove (disparitySet v k) U (handoffOpening v k U g) ∧
      ∀ i : Fin 8, i≠k → InWay (reading v k i) U → advance (reading v k i) U (handoffOpening v k U g)=0 := by
  classical
  let S := Finset.univ.filter (fun i : Fin 8=>i≠k ∧ InWay (reading v k i) U)
  obtain ⟨q,hq,hwq⟩ := hne
  have hqmem : q∈S := by simp [S,hq,hwq]
  obtain ⟨g,hg,hmin⟩ := Finset.exists_min_image S (reading v k) ⟨q,hqmem⟩
  have hgm := (Finset.mem_filter.mp hg).2
  have hm : ∀ i : Fin 8, i≠k → InWay (reading v k i) U →
      advance (reading v k i) (handoffOpening v k R c) U=advance (reading v k g) (handoffOpening v k R c) U :=
    fun i hi hw=>(hlevel i hi hw).2.trans (hlevel g hgm.1 hgm.2).2.symm
  have ht := same_level_forces_move hv k R U c g h hTU hgm.1 hgm.2
    (fun i hi hw=>(hlevel i hi hw).1) hm (fun i hi hw=>hmin i (by simp [S,hi,hw]))
  exact ⟨g,hgm.1,hgm.2,ht.1,ht.2,fun i hi hw=>selected_level_zero hv k R U c i g h hTU hi hgm.1
    (hlevel i hi hw).1 (hlevel g hgm.1 hgm.2).1 hw hgm.2 (hm i hi hw) ht.2⟩

-- STANDING: DEFINITION
noncomputable def HomogeneousRetainedClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (R U : ℝ) (c : Fin 8) (m : ℕ), 0<R ∧ Cohort v k R c ∧ handoffOpening v k R c ≤ U ∧
    (∃ i : Fin 8, i≠k ∧ InWay (reading v k i) U) ∧
    (∀ i : Fin 8, i≠k → InWay (reading v k i) U →
      InWay (reading v k i) R ∧ advance (reading v k i) (handoffOpening v k R c) U=m) ∧
    (∀ i : Fin 8, i≠k → ¬InWay (reading v k i) U → ∀ j : Fin 8, j≠k → InWay (reading v k j) U →
      handoffOpening v k U j ≤ closing (reading v k i) U)

theorem homogeneousRetained_into_noReturn {v : Fin 8 → ℝ} {k : Fin 8} (h : HomogeneousRetainedClass v k) :
    Fresh.NativeCanonicalReturn.NoReturnClass v k := by
  obtain ⟨hv,R,U,c,m,hR,hco,hTU,hne,hlevel,hclose⟩ := h
  obtain ⟨g,hg,hw,ht,hm,hzero⟩ := homogeneous_forces_move hv k R U c m hco hTU hne hlevel
  have hRT := le_of_isMove (disparitySet_pos hv k) (cohort_move hv k R c hco.1 hco.2.1 hco.2.2)
  have hcap := capture_at_label (reading v k g) U hw
  refine ⟨hv,g,U,label (reading v k g*U),hg,lt_of_lt_of_le hR (le_trans hRT hTU),hcap.1,hcap.2,hm,?_⟩
  intro i hi
  by_cases hwi : InWay (reading v k i) U
  · exact hzero i hi hwi
  · have hp : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
    apply (zero_iff_original_upper _ _ _ hp.le ht.le).2
    have hh := (le_div_iff₀ hp).1 (hclose i hi hwi g hg hw)
    simpa only [closing,mul_comm] using hh

theorem homogeneousRetained_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : HomogeneousRetainedClass v k) : Isolation v k :=
  Fresh.NativeCanonicalReturn.noReturn_isolation (homogeneousRetained_into_noReturn h)

#print axioms equal_level_sharp
#print axioms equal_level_compact
#print axioms same_level_compact
#print axioms selected_level_zero
#print axioms selected_level_clear
#print axioms next_capture_sources
#print axioms homogeneous_forces_move
#print axioms homogeneousRetained_into_noReturn
#print axioms homogeneousRetained_isolation
end Fresh.NativeSelectedLevelClearance
