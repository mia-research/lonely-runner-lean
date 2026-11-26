import Fresh.NativeSingleReturnRelay

/-! Single returned groups join prior isolation families when their forced
relay fits the first remaining ORIGINAL closing boundary. All physical
identities, independent integer labels and closed equality faces are kept. -/
namespace Fresh.NativeSingleReturnArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement Fresh.NativeReturnClosingOrder
  Fresh.NativeSingleReturnRelay

noncomputable def OutsideFirstClosing (v : Fin 8 → ℝ) (k : Fin 8) (P : ℝ) (c a : Fin 8) : Prop :=
  a≠k ∧ reading v k a≠reading v k c ∧
    ∀ i : Fin 8, i≠k → reading v k i≠reading v k c → closing (reading v k a) P≤closing (reading v k i) P

theorem setter_outside {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (j c : Fin 8) (he : HandoffEntry v k Q P j)
    (hs : SingleReturn v k P (handoffOpening v k P j) c) : reading v k j≠reading v k c := by
  intro hh
  have hz := handoff_selected_zero hv k Q P he.2.1 j he.2.2.1
  rw [hh] at hz
  have ha := hs.2.1
  omega

theorem exists_outside_first {v : Fin 8 → ℝ} (k : Fin 8) (P : ℝ) (c j : Fin 8)
    (hj : j≠k) (hneq : reading v k j≠reading v k c) : ∃ a : Fin 8, OutsideFirstClosing v k P c a := by
  classical
  let S := Finset.univ.filter (fun i : Fin 8=>i≠k ∧ reading v k i≠reading v k c)
  have hne : S.Nonempty := ⟨j,by simp [S,hj,hneq]⟩
  obtain ⟨a,ha,hmin⟩ := Finset.exists_min_image S (fun i=>closing (reading v k i) P) hne
  have ham := (Finset.mem_filter.mp ha).2
  refine ⟨a,ham.1,ham.2,?_⟩
  intro i hi hd
  exact hmin i (by simp [S,hi,hd])

theorem fits_iff_anchor {v : Fin 8 → ℝ} (k : Fin 8) (P R : ℝ) (c a : Fin 8)
    (ha : OutsideFirstClosing v k P c a) :
    OriginalFits v k P R c ↔ handoffOpening v k R c≤closing (reading v k a) P := by
  constructor
  · intro hf
    exact hf a ha.1 ha.2.1
  · intro hh i hi hd
    exact le_trans hh (ha.2.2 i hi hd)

theorem relay_capture_iff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hs : SingleReturn v k P R c)
    (hc : InWay (reading v k c) R) (i : Fin 8) (hi : i≠k) :
    InWay (reading v k i) (handoffOpening v k R c) ↔
      reading v k i≠reading v k c ∧ closing (reading v k i) P<handoffOpening v k R c ∧
        reading v k i*handoffOpening v k R c<(label (reading v k i*handoffOpening v k R c) : ℝ)+1/8 := by
  have hm2 := (single_relay hv k P R hm c hs hc).2
  have hb : InWay (reading v k i) (handoffOpening v k R c) ↔
      0 < advance (reading v k i) R (handoffOpening v k R c) ∧
        reading v k i*handoffOpening v k R c<(label (reading v k i*handoffOpening v k R c) : ℝ)+1/8 :=
    capture_iff_returned_lower hv k R _ hm2 i hi
  rw [hb,relay_return_iff hv k P R hm c hs hc i hi]
  exact and_assoc

theorem outside_anchor_returns {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c a : Fin 8) (hs : SingleReturn v k P R c)
    (hc : InWay (reading v k c) R) (ha : OutsideFirstClosing v k P c a)
    (hcross : closing (reading v k a) P<handoffOpening v k R c) :
    0 < advance (reading v k a) R (handoffOpening v k R c) :=
  (relay_return_iff hv k P R hm c hs hc a ha.1).2 ⟨ha.2.1,hcross⟩

-- STANDING: DEFINITION
noncomputable def RelayClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (Q P : ℝ) (j c : Fin 8), HandoffEntry v k Q P j ∧
    SingleClosingEntry v k P (handoffOpening v k P j) c ∧
    InWay (reading v k c) (handoffOpening v k P j) ∧ OriginalFits v k P (handoffOpening v k P j) c

-- STANDING: DEFINITION
noncomputable def AnchorClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (Q P : ℝ) (j c a : Fin 8), HandoffEntry v k Q P j ∧
    SingleClosingEntry v k P (handoffOpening v k P j) c ∧
    InWay (reading v k c) (handoffOpening v k P j) ∧ OutsideFirstClosing v k P c a ∧
      handoffOpening v k (handoffOpening v k P j) c≤closing (reading v k a) P

-- STANDING: DEFINITION
noncomputable def RecoveryClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (Q P : ℝ) (j c : Fin 8), HandoffEntry v k Q P j ∧
    SingleClosingEntry v k P (handoffOpening v k P j) c ∧ ¬InWay (reading v k c) (handoffOpening v k P j)

theorem relay_into_noReturn {v : Fin 8 → ℝ} {k : Fin 8} (h : RelayClass v k) : HandoffNoReturnClass v k := by
  obtain ⟨hv,Q,P,j,c,he,hentry,hc,hfit⟩ := h
  have ht := forced_handoff hv k Q P he.2.1 j he.2.2.1 he.2.2.2
  have hs := (entry_iff_single hv k P _ ht.1.le c).1 hentry
  have hsur := (survivor_iff hv k P _ ht.2 c).2 ⟨hs.1,hc⟩
  have hP := lt_trans he.1 (predecessor_strict hv k Q P he.2.1 j he.2.2.1)
  exact ⟨hv,P,handoffOpening v k P j,c,
    ⟨hP,ht.2,hsur,equal_readings_order k P _ c (fun i hi=>hs.2.2 i hi.1 hi.2.1)⟩,
    (relay_zero_iff_fits hv k P _ ht.2 c hs hc).2 hfit⟩

theorem anchor_into_relay {v : Fin 8 → ℝ} {k : Fin 8} (h : AnchorClass v k) : RelayClass v k := by
  obtain ⟨hv,Q,P,j,c,a,he,hentry,hc,ha,hfit⟩ := h
  exact ⟨hv,Q,P,j,c,he,hentry,hc,(fits_iff_anchor k P _ c a ha).2 hfit⟩

theorem relay_into_anchor {v : Fin 8 → ℝ} {k : Fin 8} (h : RelayClass v k) : AnchorClass v k := by
  obtain ⟨hv,Q,P,j,c,he,hentry,hc,hfit⟩ := h
  have ht := forced_handoff hv k Q P he.2.1 j he.2.2.1 he.2.2.2
  have hs := (entry_iff_single hv k P _ ht.1.le c).1 hentry
  obtain ⟨a,ha⟩ := exists_outside_first k P c j he.2.2.1.1 (setter_outside hv k Q P j c he hs)
  exact ⟨hv,Q,P,j,c,a,he,hentry,hc,ha,(fits_iff_anchor k P _ c a ha).1 hfit⟩

theorem recovery_into_recovered {v : Fin 8 → ℝ} {k : Fin 8} (h : RecoveryClass v k) : HandoffRecoveredClass v k := by
  obtain ⟨hv,Q,P,j,c,he,hentry,hc⟩ := h
  have ht := forced_handoff hv k Q P he.2.1 j he.2.2.1 he.2.2.2
  have hs := (entry_iff_single hv k P _ ht.1.le c).1 hentry
  refine ⟨hv,Q,P,j,he,?_⟩
  intro i hi hret
  have heq := hs.2.2 i hi hret
  have hn : ¬InWay (reading v k i) (handoffOpening v k P j) := by simpa only [heq] using hc
  have hpass : (label (reading v k i*handoffOpening v k P j) : ℝ)+1/8≤reading v k i*handoffOpening v k P j :=
    le_of_not_gt (fun hh=>hn ((inWay_iff_lower_not_passed _ _).2 hh))
  have hmul := mul_le_mul_of_nonneg_left hpass (show 0≤reading v k j from abs_nonneg _)
  have hid := handoff_identity hv k j P he.2.2.1.1
  have hscaled := congrArg (fun x : ℝ=>reading v k i*x) hid
  nlinarith only [hmul,hscaled]

theorem relay_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : RelayClass v k) : Isolation v k :=
  handoff_noReturn_isolation (relay_into_noReturn h)

theorem anchor_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : AnchorClass v k) : Isolation v k :=
  relay_isolation (anchor_into_relay h)

theorem recovery_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : RecoveryClass v k) : Isolation v k :=
  handoff_recovered_isolation (recovery_into_recovered h)

theorem relay_three_moves {v : Fin 8 → ℝ} {k : Fin 8} (h : RelayClass v k) :
    ∃ Q P R T : ℝ, 0<Q ∧ Q<P ∧ P<R ∧ R<T ∧ IsMove (disparitySet v k) Q P ∧
      IsMove (disparitySet v k) P R ∧ IsMove (disparitySet v k) R T ∧ IsolatedAt v k T := by
  obtain ⟨hv,Q,P,j,c,he,hentry,hc,hfit⟩ := h
  have ht := forced_handoff hv k Q P he.2.1 j he.2.2.1 he.2.2.2
  have hs := (entry_iff_single hv k P _ ht.1.le c).1 hentry
  have ht2 := single_relay hv k P _ ht.2 c hs hc
  exact ⟨Q,P,handoffOpening v k P j,handoffOpening v k (handoffOpening v k P j) c,
    he.1,predecessor_strict hv k Q P he.2.1 j he.2.2.1,ht.1,ht2.1,he.2.1,ht.2,ht2.2,
    relay_fits_isolated hv k P _ ht.2 c hs hc hfit⟩

#print axioms setter_outside
#print axioms exists_outside_first
#print axioms fits_iff_anchor
#print axioms relay_capture_iff
#print axioms outside_anchor_returns
#print axioms relay_into_noReturn
#print axioms anchor_into_relay
#print axioms relay_into_anchor
#print axioms recovery_into_recovered
#print axioms relay_isolation
#print axioms anchor_isolation
#print axioms recovery_isolation
#print axioms relay_three_moves
end Fresh.NativeSingleReturnArrangement
