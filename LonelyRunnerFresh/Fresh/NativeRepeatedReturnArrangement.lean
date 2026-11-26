import Fresh.NativeRepeatedReturn

/-! The two native closing prefixes force a repeated single disparity
into the already proved single-return recovery or relay families. -/
namespace Fresh.NativeRepeatedReturnArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement Fresh.NativeReturnClosingOrder
  Fresh.NativeRepeatedReturn

noncomputable def RepeatedSingleEntry (v : Fin 8 → ℝ) (k : Fin 8) (P R : ℝ) (c g : Fin 8) : Prop :=
  g≠k ∧ 0 < advance (reading v k g) P R ∧ closing (reading v k g) R<handoffOpening v k R c ∧
    ∀ i : Fin 8, i≠k → reading v k i≠reading v k g →
      (0 < advance (reading v k i) P R → handoffOpening v k R c≤closing (reading v k i) R) ∧
      (advance (reading v k i) P R=0 → handoffOpening v k R c≤closing (reading v k i) P)

theorem two_prefixes_return_iff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (i : Fin 8) (hi : i≠k) :
    0 < advance (reading v k i) R (handoffOpening v k R c) ↔
      (0 < advance (reading v k i) P R ∧ closing (reading v k i) R<handoffOpening v k R c) ∨
      (advance (reading v k i) P R=0 ∧ closing (reading v k i) P<handoffOpening v k R c) := by
  have ht := forced_handoff hv k P R hm c hc ho
  have hip : 0 < reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  have hn := positive_iff_closing_passed (reading v k i) R _ hip ht.1.le
  by_cases hz : advance (reading v k i) P R=0
  · have hl := advance_identity (reading v k i) P R hip.le (le_of_isMove (disparitySet_pos hv k) hm)
    simp only [hz,Nat.cast_zero,add_zero] at hl
    have heq : closing (reading v k i) R=closing (reading v k i) P := by simp only [closing,hl]
    constructor
    · intro ha
      exact Or.inr ⟨hz,by simpa only [heq] using hn.1 ha⟩
    · intro hh
      rcases hh with hh|hh
      · omega
      · apply hn.2
        simpa only [heq] using hh.2
  · constructor
    · intro ha
      exact Or.inl ⟨by omega,hn.1 ha⟩
    · intro hh
      rcases hh with hh|hh
      · exact hn.2 hh.2
      · exact (hz hh.1).elim

theorem entry_into_single {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c g : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (he : RepeatedSingleEntry v k P R c g) :
    Fresh.NativeSingleReturnRelay.SingleReturn v k R (handoffOpening v k R c) g := by
  have ht := forced_handoff hv k P R hm c hc ho
  have hgp : 0 < reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,he.1,rfl⟩)
  refine ⟨he.1,(positive_iff_closing_passed _ R _ hgp ht.1.le).2 he.2.2.1,?_⟩
  intro i hi ha
  by_contra hneq
  have hb := he.2.2.2 i hi hneq
  rcases (two_prefixes_return_iff hv k P R hm c hc ho i hi).1 ha with hh|hh
  · exact not_lt_of_ge (hb.1 hh.1) hh.2
  · exact not_lt_of_ge (hb.2 hh.1) hh.2

theorem single_into_entry {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c g : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c)
    (hs : Fresh.NativeSingleReturnRelay.SingleReturn v k R (handoffOpening v k R c) g)
    (hold : 0 < advance (reading v k g) P R) : RepeatedSingleEntry v k P R c g := by
  have ht := forced_handoff hv k P R hm c hc ho
  have hgp : 0 < reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hs.1,rfl⟩)
  refine ⟨hs.1,hold,(positive_iff_closing_passed _ R _ hgp ht.1.le).1 hs.2.1,?_⟩
  intro i hi hneq
  have hn : ¬0 < advance (reading v k i) R (handoffOpening v k R c) := fun ha=>hneq (hs.2.2 i hi ha)
  constructor
  · intro ha
    by_contra hh
    exact hn ((two_prefixes_return_iff hv k P R hm c hc ho i hi).2 (Or.inl ⟨ha,lt_of_not_ge hh⟩))
  · intro hz
    by_contra hh
    exact hn ((two_prefixes_return_iff hv k P R hm c hc ho i hi).2 (Or.inr ⟨hz,lt_of_not_ge hh⟩))

theorem repeated_dichotomy {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c g : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (he : RepeatedSingleEntry v k P R c g) :
    IsolatedAt v k (handoffOpening v k R c) ∨
      (InWay (reading v k g) (handoffOpening v k R c) ∧
        handoffOpening v k R c<handoffOpening v k (handoffOpening v k R c) g ∧
        IsMove (disparitySet v k) (handoffOpening v k R c) (handoffOpening v k (handoffOpening v k R c) g)) := by
  have ht := forced_handoff hv k P R hm c hc ho
  exact Fresh.NativeSingleReturnRelay.single_dichotomy hv k R _ ht.2 g (entry_into_single hv k P R hm c g hc ho he)

-- STANDING: DEFINITION
noncomputable def RecoveryClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (P R : ℝ) (c g : Fin 8), 0<P ∧ IsMove (disparitySet v k) P R ∧
    Survivor v k P R c ∧ OpeningOrder v k P R c ∧ RepeatedSingleEntry v k P R c g ∧
      ¬InWay (reading v k g) (handoffOpening v k R c)

-- STANDING: DEFINITION
noncomputable def RelayClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (P R : ℝ) (c g : Fin 8), 0<P ∧ IsMove (disparitySet v k) P R ∧
    Survivor v k P R c ∧ OpeningOrder v k P R c ∧ RepeatedSingleEntry v k P R c g ∧
    InWay (reading v k g) (handoffOpening v k R c) ∧
      Fresh.NativeSingleReturnRelay.OriginalFits v k R (handoffOpening v k R c) g

theorem recovery_into_single {v : Fin 8 → ℝ} {k : Fin 8} (h : RecoveryClass v k) :
    Fresh.NativeSingleReturnArrangement.RecoveryClass v k := by
  obtain ⟨hv,P,R,c,g,hP,hm,hc,ho,he,hclear⟩ := h
  have ht := forced_handoff hv k P R hm c hc ho
  have hs := entry_into_single hv k P R hm c g hc ho he
  exact ⟨hv,P,R,c,g,⟨hP,hm,hc,ho⟩,
    (Fresh.NativeSingleReturnRelay.entry_iff_single hv k R _ ht.1.le g).2 hs,hclear⟩

theorem relay_into_single {v : Fin 8 → ℝ} {k : Fin 8} (h : RelayClass v k) :
    Fresh.NativeSingleReturnArrangement.RelayClass v k := by
  obtain ⟨hv,P,R,c,g,hP,hm,hc,ho,he,hcap,hfit⟩ := h
  have ht := forced_handoff hv k P R hm c hc ho
  have hs := entry_into_single hv k P R hm c g hc ho he
  exact ⟨hv,P,R,c,g,⟨hP,hm,hc,ho⟩,
    (Fresh.NativeSingleReturnRelay.entry_iff_single hv k R _ ht.1.le g).2 hs,hcap,hfit⟩

theorem recovery_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : RecoveryClass v k) : Isolation v k :=
  Fresh.NativeSingleReturnArrangement.recovery_isolation (recovery_into_single h)

theorem relay_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : RelayClass v k) : Isolation v k :=
  Fresh.NativeSingleReturnArrangement.relay_isolation (relay_into_single h)

-- STANDING: DEFINITION
noncomputable def RecoveredRelayClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (P R : ℝ) (c g : Fin 8), 0<P ∧ IsMove (disparitySet v k) P R ∧
    Survivor v k P R c ∧ OpeningOrder v k P R c ∧ RepeatedSingleEntry v k P R c g ∧
    InWay (reading v k g) (handoffOpening v k R c) ∧ RecoveredSecond v k (handoffOpening v k R c) g

theorem recoveredRelay_into_handoff {v : Fin 8 → ℝ} {k : Fin 8} (h : RecoveredRelayClass v k) : HandoffRecoveredClass v k := by
  obtain ⟨hv,P,R,c,g,hP,hm,hc,ho,he,hcap,hpassed⟩ := h
  have ht := forced_handoff hv k P R hm c hc ho
  have hs := entry_into_single hv k P R hm c g hc ho he
  have hsur := (survivor_iff hv k R _ ht.2 g).2 ⟨hs.1,hcap⟩
  have hR := lt_of_lt_of_le hP (le_of_isMove (disparitySet_pos hv k) hm)
  exact ⟨hv,R,handoffOpening v k R c,g,⟨hR,ht.2,hsur,equal_readings_order k R _ g
    (fun i hi=>hs.2.2 i hi.1 hi.2.1)⟩,hpassed⟩

theorem relay_into_recoveredRelay {v : Fin 8 → ℝ} {k : Fin 8} (h : RelayClass v k) : RecoveredRelayClass v k := by
  obtain ⟨hv,P,R,c,g,hP,hm,hc,ho,he,hcap,hfit⟩ := h
  have ht := forced_handoff hv k P R hm c hc ho
  have hs := entry_into_single hv k P R hm c g hc ho he
  have hz := (Fresh.NativeSingleReturnRelay.relay_zero_iff_fits hv k R _ ht.2 g hs hcap).2 hfit
  refine ⟨hv,P,R,c,g,hP,hm,hc,ho,he,hcap,?_⟩
  intro i hi ha
  have hzero := hz i hi
  omega

theorem recoveredRelay_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : RecoveredRelayClass v k) : Isolation v k :=
  handoff_recovered_isolation (recoveredRelay_into_handoff h)

#print axioms recoveredRelay_into_handoff
#print axioms relay_into_recoveredRelay
#print axioms recoveredRelay_isolation
#print axioms two_prefixes_return_iff
#print axioms entry_into_single
#print axioms single_into_entry
#print axioms repeated_dichotomy
#print axioms recovery_into_single
#print axioms relay_into_single
#print axioms recovery_isolation
#print axioms relay_isolation
end Fresh.NativeRepeatedReturnArrangement
