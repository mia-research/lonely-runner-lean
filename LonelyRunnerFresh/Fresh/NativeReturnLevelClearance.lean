import Fresh.NativeSelectedLevelClearance

/-! Generic predecessor return levels, without a common-opening cohort.
A selected level clears automatically for advances at least two, or for an
earlier predecessor phase. Equal-level recapture forces the late-one branch. -/
namespace Fresh.NativeReturnLevelClearance
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement Fresh.NativeReturnClosingOrder
  Fresh.NativeCapturedPartnerJoin Fresh.NativeCohortReturns Fresh.NativeCohortOutsiderRelay

theorem displacement_bounds (s P U : ℝ) (hs : 0 ≤ s) (hPU : P ≤ U) (hw : InWay s U) :
    (advance s P U : ℝ)-1 < s*(U-P) ∧ s*(U-P) < (advance s P U : ℝ)+1/4 := by
  have hi := advance_identity s P U hs hPU
  have hiR : (label (s*U) : ℝ)=(label (s*P) : ℝ)+(advance s P U : ℝ) := by exact_mod_cast hi
  have hcap := capture_at_label s U hw
  have hbase := (entry_interval s P _).1 (label_entry s P)
  rw [hiR] at hcap
  constructor  <;> nlinarith only [hcap.1,hcap.2,hbase.1,hbase.2]

theorem early_displacement (s P U : ℝ) (hs : 0 ≤ s) (hPU : P ≤ U) (hw : InWay s U)
    (he : s*P  ≤  (label (s*P) : ℝ)+11/24) :
    (advance s P U : ℝ)-7/12 < s*(U-P) := by
  have hi := advance_identity s P U hs hPU
  have hiR : (label (s*U) : ℝ)=(label (s*P) : ℝ)+(advance s P U : ℝ) := by exact_mod_cast hi
  have hc := (capture_at_label s U hw).1
  rw [hiR] at hc
  linarith only [he,hc]

theorem two_level_compact (s d P U : ℝ) (hs : 0 ≤ s) (hd : 0 ≤ d) (hPU : P ≤ U)
    (hws : InWay s U) (hwd : InWay d U) (hm : advance s P U=advance d P U)
    (htwo : 2 ≤ advance d P U) : s < 3*d := by
  have hb := (displacement_bounds s P U hs hPU hws).2
  rw [hm] at hb
  have hdb := (displacement_bounds d P U hd hPU hwd).1
  have hmR : (2 : ℝ) ≤ (advance d P U : ℝ) := by exact_mod_cast htwo
  by_contra hn
  have hx := mul_le_mul_of_nonneg_right (le_of_not_gt hn) (sub_nonneg.mpr hPU)
  nlinarith only [hb,hdb,hmR,hx]

theorem early_level_compact (s d P U : ℝ) (hs : 0 ≤ s) (hd : 0 ≤ d) (hPU : P ≤ U)
    (hws : InWay s U) (hwd : InWay d U) (hm : advance s P U=advance d P U)
    (hpos : 0 < advance d P U) (he : d*P  ≤  (label (d*P) : ℝ)+11/24) : s < 3*d := by
  have hb := (displacement_bounds s P U hs hPU hws).2
  rw [hm] at hb
  have hdb := early_displacement d P U hd hPU hwd he
  have hmR : (1 : ℝ) ≤ (advance d P U : ℝ) := by exact_mod_cast hpos
  by_contra hn
  have hx := mul_le_mul_of_nonneg_right (le_of_not_gt hn) (sub_nonneg.mpr hPU)
  nlinarith only [hb,hdb,hmR,hx]

theorem paired_phase_compact (s d P U : ℝ) (hs : 0 ≤ s) (hd : 0 ≤ d) (hPU : P ≤ U)
    (hws : InWay s U) (hwd : InWay d U) (hm : advance s P U=advance d P U)
    (hface : 3*(d*P-(label (d*P) : ℝ))-(s*P-(label (s*P) : ℝ)) ≤ 2*(advance d P U : ℝ)-1/2) : s<3*d := by
  have hi := advance_identity s P U hs hPU
  have hj := advance_identity d P U hd hPU
  rw [hm] at hi
  have hiR : (label (s*U) : ℝ)=(label (s*P) : ℝ)+(advance d P U : ℝ) := by exact_mod_cast hi
  have hjR : (label (d*U) : ℝ)=(label (d*P) : ℝ)+(advance d P U : ℝ) := by exact_mod_cast hj
  have hsi := (capture_at_label s U hws).2
  have hdj := (capture_at_label d U hwd).1
  rw [hiR] at hsi
  rw [hjR] at hdj
  by_contra hn
  have hx := mul_le_mul_of_nonneg_right (le_of_not_gt hn) (sub_nonneg.mpr hPU)
  nlinarith only [hsi,hdj,hx,hface]

theorem captured_ratio_zero {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (U : ℝ) (i g : Fin 8)
    (hi : i≠k) (hg : g≠k) (hwi : InWay (reading v k i) U) (hwg : InWay (reading v k g) U)
    (hr : reading v k i ≤ 3*reading v k g)
    (hmove : IsMove (disparitySet v k) U (handoffOpening v k U g)) :
    advance (reading v k i) U (handoffOpening v k U g)=0 := by
  have hd : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have hcg := capture_at_label (reading v k g) U hwg
  have hci := capture_at_label (reading v k i) U hwi
  have hid := handoff_identity hv k g U hg
  have hmem : reading v k i∈disparitySet v k := mem_disparitySet.mpr ⟨i,hi,rfl⟩
  have ho := Fresh.FastestCaptureRecovery.captured_order_of_move _ _ hmove hmem hd
    (disparitySet_pos hv k _ hmem) hid hci.1 hci.2
  have hw := Fresh.NativeRelativeCapture.captured_window _ _ U _ _ _ hd hr hid hcg.1 hcg.2 hci.2 ho
  have hl := (entry_iff_label _ _ _).1 (Or.inl ⟨hw.1,hw.2.le⟩)
  simp only [advance,hl,sub_self,Int.toNat_zero]

theorem paired_phase_zero {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P U : ℝ) (i g : Fin 8)
    (hprior : IsMove (disparitySet v k) P U) (hi : i≠k) (hg : g≠k)
    (hwi : InWay (reading v k i) U) (hwg : InWay (reading v k g) U)
    (hm : advance (reading v k i) P U=advance (reading v k g) P U)
    (hface : 3*(reading v k g*P-(label (reading v k g*P) : ℝ))-
      (reading v k i*P-(label (reading v k i*P) : ℝ)) ≤ 2*(advance (reading v k g) P U : ℝ)-1/2)
    (hmove : IsMove (disparitySet v k) U (handoffOpening v k U g)) :
    advance (reading v k i) U (handoffOpening v k U g)=0 :=
  captured_ratio_zero hv k U i g hi hg hwi hwg
    (paired_phase_compact _ _ P U (abs_nonneg _) (abs_nonneg _)
      (le_of_isMove (disparitySet_pos hv k) hprior) hwi hwg hm hface).le hmove

theorem equal_recap_forces_pair_face {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P U : ℝ) (i g : Fin 8)
    (hprior : IsMove (disparitySet v k) P U) (hi : i≠k) (hg : g≠k)
    (hwi : InWay (reading v k i) U) (hwg : InWay (reading v k g) U)
    (hm : advance (reading v k i) P U=advance (reading v k g) P U)
    (hmove : IsMove (disparitySet v k) U (handoffOpening v k U g))
    (hafter : InWay (reading v k i) (handoffOpening v k U g)) :
    2*(advance (reading v k g) P U : ℝ)-1/2 <
      3*(reading v k g*P-(label (reading v k g*P) : ℝ))-(reading v k i*P-(label (reading v k i*P) : ℝ)) := by
  apply lt_of_not_ge
  intro hface
  exact (not_lt.mpr (nonreturning_clear hv k U _ hmove i hi
    (paired_phase_zero hv k P U i g hprior hi hg hwi hwg hm hface hmove))) hafter

noncomputable def LevelGuard (v : Fin 8 → ℝ) (k : Fin 8) (P U : ℝ) (g : Fin 8) : Prop :=
  2 ≤ advance (reading v k g) P U ∨ reading v k g*P  ≤  (label (reading v k g*P) : ℝ)+11/24

theorem guarded_compact {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P U : ℝ) (i g : Fin 8)
    (hprior : IsMove (disparitySet v k) P U) (hi : i≠k) (hg : g≠k)
    (hwi : InWay (reading v k i) U) (hwg : InWay (reading v k g) U)
    (hm : advance (reading v k i) P U=advance (reading v k g) P U) (hguard : LevelGuard v k P U g) :
    reading v k i < 3*reading v k g := by
  have hPU := le_of_isMove (disparitySet_pos hv k) hprior
  rcases hguard with htwo|he
  · exact two_level_compact _ _ P U (abs_nonneg _) (abs_nonneg _) hPU hwi hwg hm htwo
  · exact early_level_compact _ _ P U (abs_nonneg _) (abs_nonneg _) hPU hwi hwg hm
      (captured_implies_return hv k P U hprior g hg hwg) he

theorem guarded_level_zero {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P U : ℝ) (i g : Fin 8)
    (hprior : IsMove (disparitySet v k) P U) (hi : i≠k) (hg : g≠k)
    (hwi : InWay (reading v k i) U) (hwg : InWay (reading v k g) U)
    (hm : advance (reading v k i) P U=advance (reading v k g) P U) (hguard : LevelGuard v k P U g)
    (hmove : IsMove (disparitySet v k) U (handoffOpening v k U g)) :
    advance (reading v k i) U (handoffOpening v k U g)=0 := by
  have hd : 0 < reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have hr := (guarded_compact hv k P U i g hprior hi hg hwi hwg hm hguard).le
  have hcg := capture_at_label (reading v k g) U hwg
  have hci := capture_at_label (reading v k i) U hwi
  have hid := handoff_identity hv k g U hg
  have hmem : reading v k i∈disparitySet v k := mem_disparitySet.mpr ⟨i,hi,rfl⟩
  have ho := Fresh.FastestCaptureRecovery.captured_order_of_move _ _ hmove hmem hd
    (disparitySet_pos hv k _ hmem) hid hci.1 hci.2
  have hw := Fresh.NativeRelativeCapture.captured_window _ _ U _ _ _ hd hr hid hcg.1 hcg.2 hci.2 ho
  have hl := (entry_iff_label _ _ _).1 (Or.inl ⟨hw.1,hw.2.le⟩)
  simp only [advance,hl,sub_self,Int.toNat_zero]

theorem equal_level_recap_forces_late_one {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P U : ℝ) (i g : Fin 8)
    (hprior : IsMove (disparitySet v k) P U) (hi : i≠k) (hg : g≠k)
    (hwi : InWay (reading v k i) U) (hwg : InWay (reading v k g) U)
    (hm : advance (reading v k i) P U=advance (reading v k g) P U)
    (hmove : IsMove (disparitySet v k) U (handoffOpening v k U g))
    (hafter : InWay (reading v k i) (handoffOpening v k U g)) :
    advance (reading v k g) P U=1 ∧ (label (reading v k g*P) : ℝ)+11/24 < reading v k g*P ∧
      ¬InWay (reading v k g) P := by
  have hnot : ¬LevelGuard v k P U g := by
    intro hh
    exact (not_lt.mpr (nonreturning_clear hv k U _ hmove i hi
      (guarded_level_zero hv k P U i g hprior hi hg hwi hwg hm hh hmove))) hafter
  have hn2 : ¬2 ≤ advance (reading v k g) P U := fun htwo=>hnot (Or.inl htwo)
  have hpos := captured_implies_return hv k P U hprior g hg hwg
  change 0 < advance (reading v k g) P U at hpos
  have hone : advance (reading v k g) P U=1 := by omega
  have hlate : (label (reading v k g*P) : ℝ)+11/24 < reading v k g*P :=
    lt_of_not_ge (fun he=>hnot (Or.inr he))
  refine ⟨hone,hlate,?_⟩
  intro hw
  have hh := (inWay_iff_lower_not_passed _ _).1 hw
  linarith only [hlate,hh]

-- STANDING: DEFINITION
noncomputable def LevelRecoveryClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (P U : ℝ) (g : Fin 8), 0 < P ∧ IsMove (disparitySet v k) P U ∧
    g≠k ∧ InWay (reading v k g) U ∧ IsMove (disparitySet v k) U (handoffOpening v k U g) ∧ LevelGuard v k P U g ∧
    (∀ i : Fin 8, i≠k → 0 < advance (reading v k i) U (handoffOpening v k U g) →
      (¬InWay (reading v k i) U ∨ advance (reading v k i) P U≠advance (reading v k g) P U) →
      reading v k g*((label (reading v k i*handoffOpening v k U g) : ℝ)+1/8)  ≤ 
        reading v k i*((label (reading v k g*U) : ℝ)+1/8))

theorem levelRecovery_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : LevelRecoveryClass v k) :
    Fresh.NativeCanonicalReturn.CanonicalReturnClass v k := by
  obtain ⟨hv,P,U,g,hP,hprior,hg,hw,hmove,hguard,hpassed⟩ := h
  have hPU := le_of_isMove (disparitySet_pos hv k) hprior
  have hcap := capture_at_label (reading v k g) U hw
  refine ⟨hv,g,U,label (reading v k g*U),hg,lt_of_lt_of_le hP hPU,hcap.1,hcap.2,hmove,?_⟩
  intro i hi ha
  change 0 < advance (reading v k i) U (handoffOpening v k U g) at ha
  apply hpassed i hi ha
  by_cases hwi : InWay (reading v k i) U
  · apply Or.inr
    intro heq
    have hz := guarded_level_zero hv k P U i g hprior hi hg hwi hw heq hguard hmove
    omega
  · exact Or.inl hwi

theorem levelRecovery_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : LevelRecoveryClass v k) : Isolation v k :=
  Fresh.NativeCanonicalReturn.canonical_isolation (levelRecovery_into_canonical h)

-- STANDING: DEFINITION
noncomputable def PhaseRecoveryClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (P U : ℝ) (g : Fin 8), 0<P ∧ IsMove (disparitySet v k) P U ∧
    g≠k ∧ InWay (reading v k g) U ∧ IsMove (disparitySet v k) U (handoffOpening v k U g) ∧
    (∀ i : Fin 8, i≠k → 0<advance (reading v k i) U (handoffOpening v k U g) →
      (¬InWay (reading v k i) U ∨ advance (reading v k i) P U≠advance (reading v k g) P U ∨
        2*(advance (reading v k g) P U : ℝ)-1/2 <
          3*(reading v k g*P-(label (reading v k g*P) : ℝ))-(reading v k i*P-(label (reading v k i*P) : ℝ))) →
      reading v k g*((label (reading v k i*handoffOpening v k U g) : ℝ)+1/8) ≤
        reading v k i*((label (reading v k g*U) : ℝ)+1/8))

theorem phaseRecovery_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : PhaseRecoveryClass v k) :
    Fresh.NativeCanonicalReturn.CanonicalReturnClass v k := by
  obtain ⟨hv,P,U,g,hP,hprior,hg,hw,hmove,hpassed⟩ := h
  have hPU := le_of_isMove (disparitySet_pos hv k) hprior
  have hcap := capture_at_label (reading v k g) U hw
  refine ⟨hv,g,U,label (reading v k g*U),hg,lt_of_lt_of_le hP hPU,hcap.1,hcap.2,hmove,?_⟩
  intro i hi ha
  change 0<advance (reading v k i) U (handoffOpening v k U g) at ha
  apply hpassed i hi ha
  by_cases hwi : InWay (reading v k i) U
  · apply Or.inr
    by_cases hlevel : advance (reading v k i) P U=advance (reading v k g) P U
    · apply Or.inr
      apply lt_of_not_ge
      intro hface
      have hz := paired_phase_zero hv k P U i g hprior hi hg hwi hw hlevel hface hmove
      omega
    · exact Or.inl hlevel
  · exact Or.inl hwi

theorem phaseRecovery_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : PhaseRecoveryClass v k) : Isolation v k :=
  Fresh.NativeCanonicalReturn.canonical_isolation (phaseRecovery_into_canonical h)

theorem next_capture_trichotomy {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P U : ℝ) (i g : Fin 8)
    (hprior : IsMove (disparitySet v k) P U) (hi : i≠k) (hg : g≠k)
    (hwg : InWay (reading v k g) U) (hmove : IsMove (disparitySet v k) U (handoffOpening v k U g))
    (hafter : InWay (reading v k i) (handoffOpening v k U g)) :
    ¬InWay (reading v k i) U ∨
      (InWay (reading v k i) U ∧ advance (reading v k i) P U≠advance (reading v k g) P U) ∨
      (InWay (reading v k i) U ∧ advance (reading v k i) P U=advance (reading v k g) P U ∧
        advance (reading v k g) P U=1 ∧ ¬InWay (reading v k g) P ∧
        (label (reading v k g*P) : ℝ)+11/24<reading v k g*P ∧
        (3/2 : ℝ)<3*(reading v k g*P-(label (reading v k g*P) : ℝ))-
          (reading v k i*P-(label (reading v k i*P) : ℝ))) := by
  by_cases hwi : InWay (reading v k i) U
  · by_cases hlevel : advance (reading v k i) P U=advance (reading v k g) P U
    · have hl := equal_level_recap_forces_late_one hv k P U i g hprior hi hg hwi hwg hlevel hmove hafter
      have hf := equal_recap_forces_pair_face hv k P U i g hprior hi hg hwi hwg hlevel hmove hafter
      rw [hl.1] at hf
      norm_num only [Nat.cast_one] at hf
      exact Or.inr (Or.inr ⟨hwi,hlevel,hl.1,hl.2.2,hl.2.1,by linarith only [hf]⟩)
    · exact Or.inr (Or.inl ⟨hwi,hlevel⟩)
  · exact Or.inl hwi

#print axioms next_capture_trichotomy

#print axioms phaseRecovery_into_canonical
#print axioms phaseRecovery_isolation

#print axioms paired_phase_compact
#print axioms captured_ratio_zero
#print axioms paired_phase_zero
#print axioms equal_recap_forces_pair_face
#print axioms displacement_bounds
#print axioms early_displacement
#print axioms two_level_compact
#print axioms early_level_compact
#print axioms guarded_compact
#print axioms guarded_level_zero
#print axioms equal_level_recap_forces_late_one
#print axioms levelRecovery_into_canonical
#print axioms levelRecovery_isolation
end Fresh.NativeReturnLevelClearance
