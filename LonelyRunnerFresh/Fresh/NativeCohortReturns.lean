import Fresh.NativeCapturedPartnerJoin

/-! A captured cohort sharing one opening clears as a whole regardless of
outsider returns. Any capture after that move must come from a previously
clear physical reading; their original closing order still describes returns. -/
namespace Fresh.NativeCohortReturns
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement Fresh.NativeReturnClosingOrder
  Fresh.NativeCapturedPartnerJoin

noncomputable def Cohort (v : Fin 8 → ℝ) (k : Fin 8) (R : ℝ) (c : Fin 8) : Prop :=
  c≠k ∧ InWay (reading v k c) R ∧
    ∀ i : Fin 8, i≠k → InWay (reading v k i) R → handoffOpening v k R i=handoffOpening v k R c

theorem cohort_member_zero {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R : ℝ) (c : Fin 8)
    (h : Cohort v k R c) (i : Fin 8) (hi : i≠k) (hw : InWay (reading v k i) R) :
    advance (reading v k i) R (handoffOpening v k R c)=0 := by
  have hcap := capture_at_label (reading v k i) R hw
  have hid := handoff_identity hv k i R hi
  rw [h.2.2 i hi hw] at hid
  exact selected_advance_zero _ R _ _ hcap.1 hcap.2 hid

theorem cohort_return_iff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R : ℝ) (c : Fin 8)
    (h : Cohort v k R c) (i : Fin 8) (hi : i≠k) :
    0 < advance (reading v k i) R (handoffOpening v k R c) ↔
      ¬InWay (reading v k i) R ∧ closing (reading v k i) R<handoffOpening v k R c := by
  have hm := cohort_move hv k R c h.1 h.2.1 h.2.2
  have hRT := le_of_isMove (disparitySet_pos hv k) hm
  have hip : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  constructor
  · intro ha
    refine ⟨?_,(positive_iff_closing_passed _ R _ hip hRT).1 ha⟩
    intro hw
    have hz := cohort_member_zero hv k R c h i hi hw
    omega
  · intro hh
    exact (positive_iff_closing_passed _ R _ hip hRT).2 hh.2

theorem cohort_capture_outside {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R : ℝ) (c : Fin 8)
    (h : Cohort v k R c) (i : Fin 8) (hi : i≠k)
    (hw : InWay (reading v k i) (handoffOpening v k R c)) :
    ¬InWay (reading v k i) R := by
  have hm := cohort_move hv k R c h.1 h.2.1 h.2.2
  have ha := captured_implies_return hv k R _ hm i hi hw
  exact ((cohort_return_iff hv k R c h i hi).1 ha).1

theorem cohort_isolated_iff_outsiders {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R : ℝ) (c : Fin 8)
    (h : Cohort v k R c) : IsolatedAt v k (handoffOpening v k R c) ↔
      ∀ i : Fin 8, i≠k → ¬InWay (reading v k i) R → ¬InWay (reading v k i) (handoffOpening v k R c) := by
  constructor
  · intro hiso i hi hold
    have hh := hiso i hi
    rw [←Fresh.Localisation.distInt_abs_mul] at hh
    exact not_lt.mpr hh
  · intro hout i hi
    rw [←Fresh.Localisation.distInt_abs_mul]
    by_cases hw : InWay (reading v k i) R
    · exact nonreturning_clear hv k R _ (cohort_move hv k R c h.1 h.2.1 h.2.2) i hi (cohort_member_zero hv k R c h i hi hw)
    · exact not_lt.mp (hout i hi hw)

-- STANDING: DEFINITION
noncomputable def RecoveredCohortClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (R : ℝ) (c : Fin 8), 0<R ∧ Cohort v k R c ∧
    ∀ i : Fin 8, i≠k → ¬InWay (reading v k i) R →
      0 < advance (reading v k i) R (handoffOpening v k R c) →
      reading v k c*((label (reading v k i*handoffOpening v k R c) : ℝ)+1/8) ≤
        reading v k i*((label (reading v k c*R) : ℝ)+1/8)

theorem recovered_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : RecoveredCohortClass v k) :
    Fresh.NativeCanonicalReturn.CanonicalReturnClass v k := by
  obtain ⟨hv,R,c,hR,hco,hpassed⟩ := h
  have hcap := capture_at_label (reading v k c) R hco.2.1
  refine ⟨hv,c,R,label (reading v k c*R),hco.1,hR,hcap.1,hcap.2,
    cohort_move hv k R c hco.1 hco.2.1 hco.2.2,?_⟩
  intro i hi ha
  exact hpassed i hi ((cohort_return_iff hv k R c hco i hi).1 ha).1 ha

theorem retained_into_recovered {v : Fin 8 → ℝ} {k : Fin 8} (h : CohortClass v k) : RecoveredCohortClass v k := by
  obtain ⟨hv,R,c,hR,hc,hw,htie,hclear⟩ := h
  have hco : Cohort v k R c := ⟨hc,hw,htie⟩
  refine ⟨hv,R,c,hR,hco,?_⟩
  intro i hi hold ha
  have hret := ((cohort_return_iff hv k R c hco i hi).1 ha).2
  exact (not_lt_of_ge (hclear i hi hold) hret).elim

theorem recovered_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : RecoveredCohortClass v k) : Isolation v k :=
  Fresh.NativeCanonicalReturn.canonical_isolation (recovered_into_canonical h)

#print axioms cohort_member_zero
#print axioms cohort_return_iff
#print axioms cohort_capture_outside
#print axioms cohort_isolated_iff_outsiders
#print axioms recovered_into_canonical
#print axioms retained_into_recovered
#print axioms recovered_isolation
end Fresh.NativeCohortReturns
