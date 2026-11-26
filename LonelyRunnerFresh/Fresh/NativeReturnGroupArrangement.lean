import Fresh.NativeReturnGroupRelay

/-! Compact and synchronized returned groups coalesce at a local reset.
Their forced relay fits exactly when it precedes the first remaining
original closing boundary. Earlier single-return inputs embed here. -/
namespace Fresh.NativeReturnGroupArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement Fresh.NativeReturnClosingOrder
  Fresh.NativeReturnGroupRelay

noncomputable def RemainingFirst (v : Fin 8 → ℝ) (k : Fin 8) (P R : ℝ) (a : Fin 8) : Prop :=
  a≠k ∧ advance (reading v k a) P R=0 ∧
    ∀ i : Fin 8, i≠k → advance (reading v k i) P R=0 → closing (reading v k a) P≤closing (reading v k i) P

theorem exists_remaining_first {v : Fin 8 → ℝ} (k : Fin 8) (P R : ℝ) (j : Fin 8)
    (hj : j≠k) (hz : advance (reading v k j) P R=0) : ∃ a : Fin 8, RemainingFirst v k P R a := by
  classical
  let S := Finset.univ.filter (fun i : Fin 8=>i≠k ∧ advance (reading v k i) P R=0)
  have hne : S.Nonempty := ⟨j,by simp [S,hj,hz]⟩
  obtain ⟨a,ha,hmin⟩ := Finset.exists_min_image S (fun i=>closing (reading v k i) P) hne
  have ham := (Finset.mem_filter.mp ha).2
  refine ⟨a,ham.1,ham.2,?_⟩
  intro i hi hi0
  exact hmin i (by simp [S,hi,hi0])

theorem fits_iff_remaining {v : Fin 8 → ℝ} (k : Fin 8) (P R : ℝ) (c a : Fin 8)
    (ha : RemainingFirst v k P R a) : GroupFits v k P R c ↔ handoffOpening v k R c≤closing (reading v k a) P := by
  constructor
  · intro hf
    exact hf a ha.1 ha.2.1
  · intro hh i hi hi0
    exact le_trans hh (ha.2.2 i hi hi0)

theorem failed_remaining_returns {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c a : Fin 8) (hr : Reset v k P R c)
    (ha : RemainingFirst v k P R a) (hcross : closing (reading v k a) P<handoffOpening v k R c) :
    0 < advance (reading v k a) R (handoffOpening v k R c) :=
  (reset_return_iff hv k P R hm c hr a ha.1).2 ⟨ha.2.1,hcross⟩

-- Internal reset representation; the concrete classes below derive it from entry bands.
noncomputable def ResetClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (Q P : ℝ) (j c : Fin 8), HandoffEntry v k Q P j ∧
    Reset v k P (handoffOpening v k P j) c ∧ GroupFits v k P (handoffOpening v k P j) c

-- STANDING: DEFINITION
noncomputable def CompactClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (Q P : ℝ) (j c : Fin 8), HandoffEntry v k Q P j ∧
    CompactEntry v k P (handoffOpening v k P j) c ∧ GroupFits v k P (handoffOpening v k P j) c

-- STANDING: DEFINITION
noncomputable def CommonClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (Q P : ℝ) (j c : Fin 8), HandoffEntry v k Q P j ∧
    CommonEntry v k P (handoffOpening v k P j) c ∧ GroupFits v k P (handoffOpening v k P j) c

-- STANDING: DEFINITION
noncomputable def AnchorClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (Q P : ℝ) (j c a : Fin 8), HandoffEntry v k Q P j ∧
    CompactEntry v k P (handoffOpening v k P j) c ∧ RemainingFirst v k P (handoffOpening v k P j) a ∧
      handoffOpening v k (handoffOpening v k P j) c≤closing (reading v k a) P

theorem reset_into_noReturn {v : Fin 8 → ℝ} {k : Fin 8} (h : ResetClass v k) : HandoffNoReturnClass v k := by
  obtain ⟨hv,Q,P,j,c,he,hr,hfit⟩ := h
  have ht := forced_handoff hv k Q P he.2.1 j he.2.2.1 he.2.2.2
  have hP := lt_trans he.1 (predecessor_strict hv k Q P he.2.1 j he.2.2.1)
  exact ⟨hv,P,handoffOpening v k P j,c,⟨hP,ht.2,hr.1,hr.2.1⟩,
    (reset_zero_iff_fits hv k P _ ht.2 c hr).2 hfit⟩

theorem compact_into_reset_class {v : Fin 8 → ℝ} {k : Fin 8} (h : CompactClass v k) : ResetClass v k := by
  obtain ⟨hv,Q,P,j,c,he,hb,hfit⟩ := h
  have ht := forced_handoff hv k Q P he.2.1 j he.2.2.1 he.2.2.2
  exact ⟨hv,Q,P,j,c,he,compact_into_reset hv k P _ ht.2 c hb,hfit⟩

theorem common_into_compact_class {v : Fin 8 → ℝ} {k : Fin 8} (h : CommonClass v k) : CompactClass v k := by
  obtain ⟨hv,Q,P,j,c,he,hb,hfit⟩ := h
  have ht := forced_handoff hv k Q P he.2.1 j he.2.2.1 he.2.2.2
  obtain ⟨d,hd,heq⟩ := common_compact_representative hv k P _ ht.2 c hb
  refine ⟨hv,Q,P,j,d,he,hd,?_⟩
  intro i hi hi0
  rw [heq]
  exact hfit i hi hi0

theorem anchor_into_compact_class {v : Fin 8 → ℝ} {k : Fin 8} (h : AnchorClass v k) : CompactClass v k := by
  obtain ⟨hv,Q,P,j,c,a,he,hb,ha,hfit⟩ := h
  exact ⟨hv,Q,P,j,c,he,hb,(fits_iff_remaining k P _ c a ha).2 hfit⟩

theorem compact_into_anchor_class {v : Fin 8 → ℝ} {k : Fin 8} (h : CompactClass v k) : AnchorClass v k := by
  obtain ⟨hv,Q,P,j,c,he,hb,hfit⟩ := h
  have hz := handoff_selected_zero hv k Q P he.2.1 j he.2.2.1
  obtain ⟨a,ha⟩ := exists_remaining_first k P _ j he.2.2.1.1 hz
  exact ⟨hv,Q,P,j,c,a,he,hb,ha,(fits_iff_remaining k P _ c a ha).1 hfit⟩

theorem single_into_compact_class {v : Fin 8 → ℝ} {k : Fin 8}
    (h : Fresh.NativeSingleReturnArrangement.RelayClass v k) : CompactClass v k := by
  obtain ⟨hv,Q,P,j,c,he,hentry,hc,hfit⟩ := h
  have ht := forced_handoff hv k Q P he.2.1 j he.2.2.1 he.2.2.2
  have hs := (Fresh.NativeSingleReturnRelay.entry_iff_single hv k P _ ht.1.le c).1 hentry
  refine ⟨hv,Q,P,j,c,he,single_into_compact hv k P _ ht.2 c hs hc,?_⟩
  intro i hi hi0
  apply hfit i hi
  intro heq
  have ha := hs.2.1
  rw [heq] at hi0
  omega

theorem compact_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : CompactClass v k) : Isolation v k :=
  handoff_noReturn_isolation (reset_into_noReturn (compact_into_reset_class h))

theorem common_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : CommonClass v k) : Isolation v k :=
  compact_isolation (common_into_compact_class h)

theorem anchor_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : AnchorClass v k) : Isolation v k :=
  compact_isolation (anchor_into_compact_class h)

theorem compact_three_moves {v : Fin 8 → ℝ} {k : Fin 8} (h : CompactClass v k) :
    ∃ Q P R T : ℝ, 0<Q ∧ Q<P ∧ P<R ∧ R<T ∧ IsMove (disparitySet v k) Q P ∧
      IsMove (disparitySet v k) P R ∧ IsMove (disparitySet v k) R T ∧ IsolatedAt v k T := by
  obtain ⟨hv,Q,P,j,c,he,hb,hfit⟩ := h
  have ht := forced_handoff hv k Q P he.2.1 j he.2.2.1 he.2.2.2
  have hr := compact_into_reset hv k P _ ht.2 c hb
  have ht2 := reset_move hv k P _ ht.2 c hr
  have hz := (reset_zero_iff_fits hv k P _ ht.2 c hr).2 hfit
  exact ⟨Q,P,handoffOpening v k P j,handoffOpening v k (handoffOpening v k P j) c,
    he.1,predecessor_strict hv k Q P he.2.1 j he.2.2.1,ht.1,ht2.1,he.2.1,ht.2,ht2.2,
    zero_returns_isolated hv k _ _ ht2.2 hz⟩

#print axioms exists_remaining_first
#print axioms fits_iff_remaining
#print axioms failed_remaining_returns
#print axioms reset_into_noReturn
#print axioms compact_into_reset_class
#print axioms common_into_compact_class
#print axioms anchor_into_compact_class
#print axioms compact_into_anchor_class
#print axioms single_into_compact_class
#print axioms compact_isolation
#print axioms common_isolation
#print axioms anchor_isolation
#print axioms compact_three_moves
end Fresh.NativeReturnGroupArrangement
