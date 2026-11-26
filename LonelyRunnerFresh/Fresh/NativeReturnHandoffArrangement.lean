import Fresh.NativeReturnHandoff

/-! Original returner handoffs rejoin the existing native no-return or
recovered-return families. The second actual move is DERIVED from survivor
opening order; its isolation uses explicit structural successor inputs. -/
namespace Fresh.NativeReturnHandoffArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff

noncomputable def HandoffEntry (v : Fin 8 → ℝ) (k : Fin 8) (Q P : ℝ) (j : Fin 8) : Prop :=
  0 < Q ∧ IsMove (disparitySet v k) Q P ∧ Survivor v k Q P j ∧ OpeningOrder v k Q P j

noncomputable def NoReturnSecond (v : Fin 8 → ℝ) (k : Fin 8) (P : ℝ) (j : Fin 8) : Prop :=
  ∀ i : Fin 8, i≠k → advance (reading v k i) P (handoffOpening v k P j)=0

noncomputable def RecoveredSecond (v : Fin 8 → ℝ) (k : Fin 8) (P : ℝ) (j : Fin 8) : Prop :=
  ∀ i : Fin 8, i≠k → 0 < advance (reading v k i) P (handoffOpening v k P j) →
    reading v k j*((label (reading v k i*handoffOpening v k P j) : ℝ)+1/8) ≤
      reading v k i*((label (reading v k j*P) : ℝ)+1/8)

-- STANDING: DEFINITION
noncomputable def HandoffNoReturnClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (Q P : ℝ) (j : Fin 8), HandoffEntry v k Q P j ∧ NoReturnSecond v k P j

-- STANDING: DEFINITION
noncomputable def HandoffRecoveredClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (Q P : ℝ) (j : Fin 8), HandoffEntry v k Q P j ∧ RecoveredSecond v k P j

-- STANDING: DEFINITION
noncomputable def SoleNoReturnClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (Q P : ℝ) (j : Fin 8), 0 < Q ∧ IsMove (disparitySet v k) Q P ∧
    Survivor v k Q P j ∧ (∀ i : Fin 8, Survivor v k Q P i → i=j) ∧ NoReturnSecond v k P j

-- STANDING: DEFINITION
noncomputable def SoleRecoveredClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (Q P : ℝ) (j : Fin 8), 0 < Q ∧ IsMove (disparitySet v k) Q P ∧
    Survivor v k Q P j ∧ (∀ i : Fin 8, Survivor v k Q P i → i=j) ∧ RecoveredSecond v k P j

theorem handoff_into_noReturn {v : Fin 8 → ℝ} {k : Fin 8} (h : HandoffNoReturnClass v k) :
    Fresh.NativeCanonicalReturn.NoReturnClass v k := by
  obtain ⟨hv,Q,P,j,⟨hQ,hm,hj,ho⟩,hzero⟩ := h
  have hc := (survivor_iff hv k Q P hm j).1 hj
  have hcap := capture_at_label (reading v k j) P hc.2
  have ht := forced_handoff hv k Q P hm j hj ho
  have hP := lt_trans hQ (predecessor_strict hv k Q P hm j hj)
  exact ⟨hv,j,P,label (reading v k j*P),hc.1,hP,hcap.1,hcap.2,ht.2,hzero⟩

theorem handoff_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : HandoffRecoveredClass v k) :
    Fresh.NativeCanonicalReturn.CanonicalReturnClass v k := by
  obtain ⟨hv,Q,P,j,⟨hQ,hm,hj,ho⟩,hpassed⟩ := h
  have hc := (survivor_iff hv k Q P hm j).1 hj
  have hcap := capture_at_label (reading v k j) P hc.2
  have ht := forced_handoff hv k Q P hm j hj ho
  have hP := lt_trans hQ (predecessor_strict hv k Q P hm j hj)
  exact ⟨hv,j,P,label (reading v k j*P),hc.1,hP,hcap.1,hcap.2,ht.2,hpassed⟩

theorem noReturn_into_recovered {v : Fin 8 → ℝ} {k : Fin 8} (h : HandoffNoReturnClass v k) :
    HandoffRecoveredClass v k := by
  obtain ⟨hv,Q,P,j,hentry,hzero⟩ := h
  refine ⟨hv,Q,P,j,hentry,?_⟩
  intro i hi ha
  have hz := hzero i hi
  omega

theorem sole_noReturn_into_handoff {v : Fin 8 → ℝ} {k : Fin 8} (h : SoleNoReturnClass v k) :
    HandoffNoReturnClass v k := by
  obtain ⟨hv,Q,P,j,hQ,hm,hj,hsole,hzero⟩ := h
  exact ⟨hv,Q,P,j,⟨hQ,hm,hj,sole_survivor_order k Q P j hsole⟩,hzero⟩

theorem sole_recovered_into_handoff {v : Fin 8 → ℝ} {k : Fin 8} (h : SoleRecoveredClass v k) :
    HandoffRecoveredClass v k := by
  obtain ⟨hv,Q,P,j,hQ,hm,hj,hsole,hpassed⟩ := h
  exact ⟨hv,Q,P,j,⟨hQ,hm,hj,sole_survivor_order k Q P j hsole⟩,hpassed⟩

theorem handoff_noReturn_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : HandoffNoReturnClass v k) : Isolation v k :=
  Fresh.NativeCanonicalReturn.noReturn_isolation (handoff_into_noReturn h)

theorem handoff_recovered_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : HandoffRecoveredClass v k) : Isolation v k :=
  Fresh.NativeCanonicalReturn.canonical_isolation (handoff_into_canonical h)

theorem two_moves_noReturn {v : Fin 8 → ℝ} {k : Fin 8} (h : HandoffNoReturnClass v k) :
    ∃ Q P R : ℝ, 0 < Q ∧ Q < P ∧ P < R ∧
      IsMove (disparitySet v k) Q P ∧ IsMove (disparitySet v k) P R ∧ IsolatedAt v k R := by
  obtain ⟨hv,Q,P,j,⟨hQ,hm,hj,ho⟩,hzero⟩ := h
  have ht := forced_handoff hv k Q P hm j hj ho
  exact ⟨Q,P,handoffOpening v k P j,hQ,predecessor_strict hv k Q P hm j hj,ht.1,hm,ht.2,
    Fresh.NativeReturnSurvivors.zero_returns_isolated hv k P _ ht.2 hzero⟩

theorem two_moves_recovered {v : Fin 8 → ℝ} {k : Fin 8} (h : HandoffRecoveredClass v k) :
    ∃ Q P R : ℝ, 0 < Q ∧ Q < P ∧ P < R ∧
      IsMove (disparitySet v k) Q P ∧ IsMove (disparitySet v k) P R ∧ IsolatedAt v k R := by
  obtain ⟨hv,Q,P,j,⟨hQ,hm,hj,ho⟩,hpassed⟩ := h
  have ht := forced_handoff hv k Q P hm j hj ho
  have hc := (survivor_iff hv k Q P hm j).1 hj
  exact ⟨Q,P,handoffOpening v k P j,hQ,predecessor_strict hv k Q P hm j hj,ht.1,hm,ht.2,
    Fresh.NativeCanonicalReturn.returned_isolated hv k j hc.1 P _ (label (reading v k j*P)) ht.2
      (handoff_identity hv k j P hc.1) hpassed⟩

noncomputable def RelativeEntrySecond (v : Fin 8 → ℝ) (k : Fin 8) (Q P : ℝ) (j : Fin 8) : Prop :=
  ∀ i : Fin 8, i≠k → i≠j →
    (Survivor v k Q P i → reading v k i ≤ 3*reading v k j) ∧
    (¬ Survivor v k Q P i → reading v k i/4 ≤ reading v k j*((label (reading v k i*P) : ℝ)+7/8-reading v k i*P))

-- STANDING: DEFINITION
noncomputable def HandoffRelativeClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (Q P : ℝ) (j : Fin 8), HandoffEntry v k Q P j ∧ RelativeEntrySecond v k Q P j

-- STANDING: DEFINITION
noncomputable def SoleRelativeClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (Q P : ℝ) (j : Fin 8), 0 < Q ∧ IsMove (disparitySet v k) Q P ∧
    Survivor v k Q P j ∧ (∀ i : Fin 8, Survivor v k Q P i → i=j) ∧ RelativeEntrySecond v k Q P j

theorem relative_entry_bands {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (hm : IsMove (disparitySet v k) Q P) (j : Fin 8) (hb : RelativeEntrySecond v k Q P j) :
    ∀ i : Fin 8, i≠k → i≠j →
      (((label (reading v k i*P) : ℝ)+1/8 ≤ reading v k i*P ∧
        reading v k i/4 ≤ reading v k j*((label (reading v k i*P) : ℝ)+7/8-reading v k i*P)) ∨
       ((label (reading v k i*P) : ℝ)-1/8 < reading v k i*P ∧
        reading v k i*P < (label (reading v k i*P) : ℝ)+1/8 ∧ reading v k i ≤ 3*reading v k j)) := by
  intro i hi hij
  by_cases hs : Survivor v k Q P i
  · have hc := capture_at_label (reading v k i) P ((survivor_iff hv k Q P hm i).1 hs).2
    exact Or.inr ⟨hc.1,hc.2,(hb i hi hij).1 hs⟩
  · have hn : ¬ InWay (reading v k i) P := fun hw=>hs ((survivor_iff hv k Q P hm i).2 ⟨hi,hw⟩)
    have hl : (label (reading v k i*P) : ℝ)+1/8 ≤ reading v k i*P := by
      by_contra hbad
      exact hn ((Fresh.NativeReturnSurvivors.inWay_iff_lower_not_passed _ _).2 (lt_of_not_ge hbad))
    exact Or.inl ⟨hl,(hb i hi hij).2 hs⟩

theorem relative_second_noReturns {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (hm : IsMove (disparitySet v k) Q P) (j : Fin 8) (hj : Survivor v k Q P j)
    (ho : OpeningOrder v k Q P j) (hb : RelativeEntrySecond v k Q P j) : NoReturnSecond v k P j := by
  have hc := (survivor_iff hv k Q P hm j).1 hj
  have hcap := capture_at_label (reading v k j) P hc.2
  have hd : 0 < reading v k j := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨j,hc.1,rfl⟩)
  have hmove := (forced_handoff hv k Q P hm j hj ho).2
  have hidentity := handoff_identity hv k j P hc.1
  have hbands := relative_entry_bands hv k Q P hm j hb
  intro i hi
  by_cases hij : i=j
  · subst i
    exact handoff_selected_zero hv k Q P hm j hj
  · have hwin : (label (reading v k i*P) : ℝ)+1/8 ≤ reading v k i*handoffOpening v k P j ∧
        reading v k i*handoffOpening v k P j ≤ (label (reading v k i*P) : ℝ)+7/8 := by
      rcases hbands i hi hij with hret|hother
      · exact Fresh.NativeRelativeCapture.retained_window _ _ P _ _ _ hd (abs_nonneg _) hidentity hcap.1 hcap.2 hret.1 hret.2
      · have hmem : reading v k i ∈ disparitySet v k := mem_disparitySet.mpr ⟨i,hi,rfl⟩
        have horder := Fresh.FastestCaptureRecovery.captured_order_of_move _ _ hmove hmem hd
          (disparitySet_pos hv k _ hmem) hidentity hother.1 hother.2.1
        have hh := Fresh.NativeRelativeCapture.captured_window _ _ P _ _ _ hd hother.2.2 hidentity hcap.1 hcap.2 hother.2.1 horder
        exact ⟨hh.1,hh.2.le⟩
    have hlabel := (Fresh.NativeEntryLabels.entry_iff_label _ _ _).1 (Or.inl hwin)
    simp only [advance,hlabel,sub_self,Int.toNat_zero]

theorem relative_into_noReturn_handoff {v : Fin 8 → ℝ} {k : Fin 8} (h : HandoffRelativeClass v k) :
    HandoffNoReturnClass v k := by
  obtain ⟨hv,Q,P,j,hentry,hb⟩ := h
  exact ⟨hv,Q,P,j,hentry,relative_second_noReturns hv k Q P hentry.2.1 j hentry.2.2.1 hentry.2.2.2 hb⟩

theorem sole_relative_into_handoff {v : Fin 8 → ℝ} {k : Fin 8} (h : SoleRelativeClass v k) :
    HandoffRelativeClass v k := by
  obtain ⟨hv,Q,P,j,hQ,hm,hj,hsole,hb⟩ := h
  exact ⟨hv,Q,P,j,⟨hQ,hm,hj,sole_survivor_order k Q P j hsole⟩,hb⟩

theorem handoff_relative_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : HandoffRelativeClass v k) : Isolation v k :=
  handoff_noReturn_isolation (relative_into_noReturn_handoff h)

noncomputable def QuarterEntrySecond (v : Fin 8 → ℝ) (k : Fin 8) (P : ℝ) (j c : Fin 8) : Prop :=
  c≠k ∧
    (∀ i : Fin 8, i≠k → reading v k i*((label (reading v k c*P) : ℝ)+7/8) ≤
      reading v k c*((label (reading v k i*P) : ℝ)+7/8)) ∧
    reading v k c/4 ≤ reading v k j*((label (reading v k c*P) : ℝ)+7/8-reading v k c*P)

-- STANDING: DEFINITION
noncomputable def HandoffQuarterClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (Q P : ℝ) (j c : Fin 8), HandoffEntry v k Q P j ∧ QuarterEntrySecond v k P j c

-- STANDING: DEFINITION
noncomputable def SoleQuarterClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (Q P : ℝ) (j c : Fin 8), 0 < Q ∧ IsMove (disparitySet v k) Q P ∧
    Survivor v k Q P j ∧ (∀ i : Fin 8, Survivor v k Q P i → i=j) ∧ QuarterEntrySecond v k P j c

theorem quarter_second_noReturns {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ) {j : Fin 8}
    (he : HandoffEntry v k Q P j) (c : Fin 8) (hb : QuarterEntrySecond v k P j c) : NoReturnSecond v k P j := by
  obtain ⟨hQ,hm,hj,ho⟩ := he
  have hc := (survivor_iff hv k Q P hm j).1 hj
  have hcap := capture_at_label (reading v k j) P hc.2
  have hnext := (forced_handoff hv k Q P hm j hj ho).2
  have hP := lt_trans hQ (predecessor_strict hv k Q P hm j hj)
  let L : Fin 8 → ℤ := fun i=>label (reading v k i*P)
  have hf : Fresh.NativeReturnCapture.ReturnFrame v k j c P (L j) L (fun _=>0) := by
    refine ⟨hc.1,hb.1,rfl,rfl,hP,hcap.1,hcap.2,hnext,?_,?_⟩
    · intro i hi hij
      exact ⟨label_entry (reading v k i) P,Or.inl rfl⟩
    · intro i hi
      simpa [Fresh.NativeReturnCapture.lifted,L,reading] using hb.2.1 i hi
  have hface : Fresh.NativeReturnCapture.SharpFace v k j c P (L j) L (fun _=>0) := by
    exact Fresh.NativeFirstClosing.quarter_implies_deficit (reading v k j) (reading v k c) P (L j) (Fresh.NativeReturnCapture.lifted L (fun _=>0) c)
      (abs_nonneg _) hcap.1 (by simpa [Fresh.NativeReturnCapture.lifted,L,reading] using hb.2.2)
  have hlabels := Fresh.NativeEntryLabels.sharp_labels hv k j c P (L j) L (fun _=>0) hf hface
  intro i hi
  exact (hlabels i hi).2.2

theorem quarter_into_noReturn_handoff {v : Fin 8 → ℝ} {k : Fin 8} (h : HandoffQuarterClass v k) :
    HandoffNoReturnClass v k := by
  obtain ⟨hv,Q,P,j,c,he,hb⟩ := h
  exact ⟨hv,Q,P,j,he,quarter_second_noReturns hv k Q P he c hb⟩

theorem sole_quarter_into_handoff {v : Fin 8 → ℝ} {k : Fin 8} (h : SoleQuarterClass v k) :
    HandoffQuarterClass v k := by
  obtain ⟨hv,Q,P,j,c,hQ,hm,hj,hsole,hb⟩ := h
  exact ⟨hv,Q,P,j,c,⟨hQ,hm,hj,sole_survivor_order k Q P j hsole⟩,hb⟩

theorem relative_into_quarter_handoff {v : Fin 8 → ℝ} {k : Fin 8} (h : HandoffRelativeClass v k) :
    HandoffQuarterClass v k := by
  obtain ⟨hv,Q,P,j,he,hb⟩ := h
  have hc := (survivor_iff hv k Q P he.2.1 j).1 he.2.2.1
  have hcap := capture_at_label (reading v k j) P hc.2
  have hd : 0 < reading v k j := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨j,hc.1,rfl⟩)
  let L : Fin 8 → ℤ := fun i=>label (reading v k i*P)
  obtain ⟨c,hck,hfirst⟩ := Fresh.NativeFirstClosing.exists_first_closing hv k L
  refine ⟨hv,Q,P,j,c,he,hck,?_,?_⟩
  · intro i hi
    exact hfirst i hi
  · by_cases hcj : c=j
    · subst c
      have hh := mul_nonneg hd.le (sub_nonneg.mpr hcap.2.le)
      nlinarith only [hh,hd]
    · by_cases hs : Survivor v k Q P c
      · have hc' := capture_at_label (reading v k c) P ((survivor_iff hv k Q P he.2.1 c).1 hs).2
        have hh := mul_nonneg hd.le (sub_nonneg.mpr hc'.2.le)
        have hratio := (hb c hck hcj).1 hs
        nlinarith only [hh,hratio]
      · exact (hb c hck hcj).2 hs

theorem handoff_quarter_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : HandoffQuarterClass v k) : Isolation v k :=
  handoff_noReturn_isolation (quarter_into_noReturn_handoff h)

#print axioms quarter_second_noReturns
#print axioms quarter_into_noReturn_handoff
#print axioms sole_quarter_into_handoff
#print axioms relative_into_quarter_handoff
#print axioms handoff_quarter_isolation
#print axioms relative_entry_bands
#print axioms relative_second_noReturns
#print axioms relative_into_noReturn_handoff
#print axioms sole_relative_into_handoff
#print axioms handoff_relative_isolation
#print axioms handoff_into_noReturn
#print axioms handoff_into_canonical
#print axioms noReturn_into_recovered
#print axioms sole_noReturn_into_handoff
#print axioms sole_recovered_into_handoff
#print axioms handoff_noReturn_isolation
#print axioms handoff_recovered_isolation
#print axioms two_moves_noReturn
#print axioms two_moves_recovered
end Fresh.NativeReturnHandoffArrangement
