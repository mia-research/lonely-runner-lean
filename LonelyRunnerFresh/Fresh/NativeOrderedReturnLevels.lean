import Fresh.NativeReturnLevelClearance

/-! Actual recaptured readers cannot have a smaller predecessor return level
than the setter. Higher-level returns obey an exact local advance comparison;
no claim of global label growth or a decreasing capture set is made. -/
namespace Fresh.NativeOrderedReturnLevels
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement Fresh.NativeReturnClosingOrder
  Fresh.NativeCapturedPartnerJoin Fresh.NativeCohortReturns Fresh.NativeCohortOutsiderRelay
  Fresh.NativeReturnLevelClearance

theorem general_phase_compact (s d P U : ℝ) (hs : 0 ≤ s) (hd : 0 ≤ d) (hPU : P ≤ U)
    (hws : InWay s U) (hwd : InWay d U)
    (hface : 3*(d*P-(label (d*P) : ℝ))-(s*P-(label (s*P) : ℝ)) ≤
      3*(advance d P U : ℝ)-(advance s P U : ℝ)-1/2) : s<3*d := by
  have hi := advance_identity s P U hs hPU
  have hj := advance_identity d P U hd hPU
  have hiR : (label (s*U) : ℝ)=(label (s*P) : ℝ)+(advance s P U : ℝ) := by exact_mod_cast hi
  have hjR : (label (d*U) : ℝ)=(label (d*P) : ℝ)+(advance d P U : ℝ) := by exact_mod_cast hj
  have hsi := (capture_at_label s U hws).2
  have hdj := (capture_at_label d U hwd).1
  rw [hiR] at hsi
  rw [hjR] at hdj
  by_contra hn
  have hx := mul_le_mul_of_nonneg_right (le_of_not_gt hn) (sub_nonneg.mpr hPU)
  nlinarith only [hsi,hdj,hx,hface]

theorem ordered_guard_face {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P U : ℝ) (i g : Fin 8)
    (hprior : IsMove (disparitySet v k) P U) (hg : g≠k) (hwg : InWay (reading v k g) U)
    (hle : advance (reading v k i) P U ≤ advance (reading v k g) P U)
    (hguard : LevelGuard v k P U g) :
    3*(reading v k g*P-(label (reading v k g*P) : ℝ))-
      (reading v k i*P-(label (reading v k i*P) : ℝ)) ≤
      3*(advance (reading v k g) P U : ℝ)-(advance (reading v k i) P U : ℝ)-1/2 := by
  have hi := (entry_interval (reading v k i) P _).1 (label_entry (reading v k i) P)
  have hgentry := (entry_interval (reading v k g) P _).1 (label_entry (reading v k g) P)
  have hleR : (advance (reading v k i) P U : ℝ) ≤ (advance (reading v k g) P U : ℝ) := by exact_mod_cast hle
  rcases hguard with htwo|hearly
  · have htwoR : (2 : ℝ) ≤ (advance (reading v k g) P U : ℝ) := by exact_mod_cast htwo
    nlinarith only [hi.1,hgentry.2,hleR,htwoR]
  · have hpos := captured_implies_return hv k P U hprior g hg hwg
    change 0<advance (reading v k g) P U at hpos
    have honeR : (1 : ℝ) ≤ (advance (reading v k g) P U : ℝ) := by exact_mod_cast hpos
    nlinarith only [hi.1,hearly,hleR,honeR]

theorem general_phase_zero {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P U : ℝ) (i g : Fin 8)
    (hprior : IsMove (disparitySet v k) P U) (hi : i≠k) (hg : g≠k)
    (hwi : InWay (reading v k i) U) (hwg : InWay (reading v k g) U)
    (hface : 3*(reading v k g*P-(label (reading v k g*P) : ℝ))-
      (reading v k i*P-(label (reading v k i*P) : ℝ)) ≤
      3*(advance (reading v k g) P U : ℝ)-(advance (reading v k i) P U : ℝ)-1/2)
    (hmove : IsMove (disparitySet v k) U (handoffOpening v k U g)) :
    advance (reading v k i) U (handoffOpening v k U g)=0 :=
  captured_ratio_zero hv k U i g hi hg hwi hwg
    (general_phase_compact _ _ P U (abs_nonneg _) (abs_nonneg _)
      (le_of_isMove (disparitySet_pos hv k) hprior) hwi hwg hface).le hmove

theorem ordered_guard_zero {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P U : ℝ) (i g : Fin 8)
    (hprior : IsMove (disparitySet v k) P U) (hi : i≠k) (hg : g≠k)
    (hwi : InWay (reading v k i) U) (hwg : InWay (reading v k g) U)
    (hle : advance (reading v k i) P U ≤ advance (reading v k g) P U) (hguard : LevelGuard v k P U g)
    (hmove : IsMove (disparitySet v k) U (handoffOpening v k U g)) :
    advance (reading v k i) U (handoffOpening v k U g)=0 :=
  general_phase_zero hv k P U i g hprior hi hg hwi hwg
    (ordered_guard_face hv k P U i g hprior hg hwg hle hguard) hmove

theorem recapture_pair_face {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P U : ℝ) (i g : Fin 8)
    (hprior : IsMove (disparitySet v k) P U) (hi : i≠k) (hg : g≠k)
    (hwi : InWay (reading v k i) U) (hwg : InWay (reading v k g) U)
    (hmove : IsMove (disparitySet v k) U (handoffOpening v k U g))
    (hafter : InWay (reading v k i) (handoffOpening v k U g)) :
    3*(advance (reading v k g) P U : ℝ)-(advance (reading v k i) P U : ℝ)-1/2 <
      3*(reading v k g*P-(label (reading v k g*P) : ℝ))-(reading v k i*P-(label (reading v k i*P) : ℝ)) := by
  apply lt_of_not_ge
  intro hf
  exact (not_lt.mpr (nonreturning_clear hv k U _ hmove i hi
    (general_phase_zero hv k P U i g hprior hi hg hwi hwg hf hmove))) hafter

theorem recapture_level_order {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P U : ℝ) (i g : Fin 8)
    (hprior : IsMove (disparitySet v k) P U) (hi : i≠k) (hg : g≠k)
    (hwi : InWay (reading v k i) U) (hwg : InWay (reading v k g) U)
    (hmove : IsMove (disparitySet v k) U (handoffOpening v k U g))
    (hafter : InWay (reading v k i) (handoffOpening v k U g)) :
    3*advance (reading v k g) P U ≤ advance (reading v k i) P U+3 ∧
      advance (reading v k g) P U ≤ advance (reading v k i) P U ∧
      (advance (reading v k i) P U=advance (reading v k g) P U → advance (reading v k g) P U=1) := by
  have hf := recapture_pair_face hv k P U i g hprior hi hg hwi hwg hmove hafter
  have hiEntry := (entry_interval (reading v k i) P _).1 (label_entry (reading v k i) P)
  have hgEntry := (entry_interval (reading v k g) P _).1 (label_entry (reading v k g) P)
  have hreal : 3*(advance (reading v k g) P U : ℝ)<(advance (reading v k i) P U : ℝ)+13/4 := by
    nlinarith only [hf,hiEntry.1,hgEntry.2]
  have hbound : 3*advance (reading v k g) P U ≤ advance (reading v k i) P U+3 := by
    by_contra hn
    have hN : advance (reading v k i) P U+4 ≤ 3*advance (reading v k g) P U := by omega
    have hR : (advance (reading v k i) P U : ℝ)+4 ≤ 3*(advance (reading v k g) P U : ℝ) := by exact_mod_cast hN
    linarith only [hreal,hR]
  have hip := captured_implies_return hv k P U hprior i hi hwi
  have hgp := captured_implies_return hv k P U hprior g hg hwg
  change 0<advance (reading v k i) P U at hip
  change 0<advance (reading v k g) P U at hgp
  exact ⟨hbound,by omega,by intro heq; omega⟩

theorem next_capture_ordered_trichotomy {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P U : ℝ) (i g : Fin 8)
    (hprior : IsMove (disparitySet v k) P U) (hi : i≠k) (hg : g≠k)
    (hwg : InWay (reading v k g) U) (hmove : IsMove (disparitySet v k) U (handoffOpening v k U g))
    (hafter : InWay (reading v k i) (handoffOpening v k U g)) :
    ¬InWay (reading v k i) U ∨
      (InWay (reading v k i) U ∧ advance (reading v k g) P U<advance (reading v k i) P U ∧
        3*advance (reading v k g) P U ≤ advance (reading v k i) P U+3) ∨
      (InWay (reading v k i) U ∧ advance (reading v k i) P U=1 ∧ advance (reading v k g) P U=1 ∧
        ¬InWay (reading v k g) P ∧ (label (reading v k g*P) : ℝ)+11/24<reading v k g*P) := by
  by_cases hwi : InWay (reading v k i) U
  · have ho := recapture_level_order hv k P U i g hprior hi hg hwi hwg hmove hafter
    by_cases heq : advance (reading v k i) P U=advance (reading v k g) P U
    · have hl := equal_level_recap_forces_late_one hv k P U i g hprior hi hg hwi hwg heq hmove hafter
      exact Or.inr (Or.inr ⟨hwi,heq.trans hl.1,hl.1,hl.2.2,hl.2.1⟩)
    · exact Or.inr (Or.inl ⟨hwi,by omega,ho.1⟩)
  · exact Or.inl hwi

-- STANDING: DEFINITION
noncomputable def MaxLevelRetainedClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (P U : ℝ) (g : Fin 8), 0<P ∧ IsMove (disparitySet v k) P U ∧
    g≠k ∧ InWay (reading v k g) U ∧ IsMove (disparitySet v k) U (handoffOpening v k U g) ∧ LevelGuard v k P U g ∧
    (∀ i : Fin 8, i≠k → InWay (reading v k i) U → advance (reading v k i) P U≤advance (reading v k g) P U) ∧
    (∀ i : Fin 8, i≠k → ¬InWay (reading v k i) U → handoffOpening v k U g≤closing (reading v k i) U)

theorem maxLevel_into_noReturn {v : Fin 8 → ℝ} {k : Fin 8} (h : MaxLevelRetainedClass v k) :
    Fresh.NativeCanonicalReturn.NoReturnClass v k := by
  obtain ⟨hv,P,U,g,hP,hprior,hg,hw,hmove,hguard,hmax,hclose⟩ := h
  have hPU := le_of_isMove (disparitySet_pos hv k) hprior
  have hcap := capture_at_label (reading v k g) U hw
  have hUV := le_of_isMove (disparitySet_pos hv k) hmove
  refine ⟨hv,g,U,label (reading v k g*U),hg,lt_of_lt_of_le hP hPU,hcap.1,hcap.2,hmove,?_⟩
  intro i hi
  by_cases hwi : InWay (reading v k i) U
  · exact ordered_guard_zero hv k P U i g hprior hi hg hwi hw (hmax i hi hwi) hguard hmove
  · have hp : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
    apply (zero_iff_original_upper _ _ _ hp.le hUV).2
    have hh := (le_div_iff₀ hp).1 (hclose i hi hwi)
    simpa only [closing,mul_comm] using hh

theorem maxLevel_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : MaxLevelRetainedClass v k) : Isolation v k :=
  Fresh.NativeCanonicalReturn.noReturn_isolation (maxLevel_into_noReturn h)

-- STANDING: DEFINITION
noncomputable def OrderedRecoveryClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (P U : ℝ) (g : Fin 8), 0<P ∧ IsMove (disparitySet v k) P U ∧
    g≠k ∧ InWay (reading v k g) U ∧ IsMove (disparitySet v k) U (handoffOpening v k U g) ∧ LevelGuard v k P U g ∧
    (∀ i : Fin 8, i≠k → 0<advance (reading v k i) U (handoffOpening v k U g) →
      (¬InWay (reading v k i) U ∨ advance (reading v k g) P U<advance (reading v k i) P U) →
      reading v k g*((label (reading v k i*handoffOpening v k U g) : ℝ)+1/8) ≤ reading v k i*((label (reading v k g*U) : ℝ)+1/8))

theorem orderedRecovery_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : OrderedRecoveryClass v k) :
    Fresh.NativeCanonicalReturn.CanonicalReturnClass v k := by
  obtain ⟨hv,P,U,g,hP,hprior,hg,hw,hmove,hguard,hpassed⟩ := h
  have hPU := le_of_isMove (disparitySet_pos hv k) hprior
  have hcap := capture_at_label (reading v k g) U hw
  refine ⟨hv,g,U,label (reading v k g*U),hg,lt_of_lt_of_le hP hPU,hcap.1,hcap.2,hmove,?_⟩
  intro i hi ha
  change 0<advance (reading v k i) U (handoffOpening v k U g) at ha
  apply hpassed i hi ha
  by_cases hwi : InWay (reading v k i) U
  · apply Or.inr
    apply lt_of_not_ge
    intro hle
    have hz := ordered_guard_zero hv k P U i g hprior hi hg hwi hw hle hguard hmove
    omega
  · exact Or.inl hwi

theorem orderedRecovery_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : OrderedRecoveryClass v k) : Isolation v k :=
  Fresh.NativeCanonicalReturn.canonical_isolation (orderedRecovery_into_canonical h)

-- STANDING: DEFINITION
noncomputable def GeneralPhaseRecoveryClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (P U : ℝ) (g : Fin 8), 0<P ∧ IsMove (disparitySet v k) P U ∧
    g≠k ∧ InWay (reading v k g) U ∧ IsMove (disparitySet v k) U (handoffOpening v k U g) ∧
    (∀ i : Fin 8, i≠k → 0<advance (reading v k i) U (handoffOpening v k U g) →
      (¬InWay (reading v k i) U ∨ 3*(advance (reading v k g) P U : ℝ)-(advance (reading v k i) P U : ℝ)-1/2 <
        3*(reading v k g*P-(label (reading v k g*P) : ℝ))-(reading v k i*P-(label (reading v k i*P) : ℝ))) →
      reading v k g*((label (reading v k i*handoffOpening v k U g) : ℝ)+1/8) ≤ reading v k i*((label (reading v k g*U) : ℝ)+1/8))

theorem generalPhase_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : GeneralPhaseRecoveryClass v k) :
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
    apply lt_of_not_ge
    intro hf
    have hz := general_phase_zero hv k P U i g hprior hi hg hwi hw hf hmove
    omega
  · exact Or.inl hwi

theorem generalPhase_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : GeneralPhaseRecoveryClass v k) : Isolation v k :=
  Fresh.NativeCanonicalReturn.canonical_isolation (generalPhase_into_canonical h)

noncomputable def returnWeight (s U V : ℝ) : ℕ := 4*advance s U V-1

theorem coupled_return_levels {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P U : ℝ) (i g : Fin 8)
    (hprior : IsMove (disparitySet v k) P U) (hi : i≠k) (hg : g≠k)
    (hwi : InWay (reading v k i) U) (hwg : InWay (reading v k g) U)
    (hmove : IsMove (disparitySet v k) U (handoffOpening v k U g))
    (ha : 0<advance (reading v k i) U (handoffOpening v k U g)) :
    returnWeight (reading v k i) U (handoffOpening v k U g)*advance (reading v k g) P U ≤
      advance (reading v k i) P U+returnWeight (reading v k i) U (handoffOpening v k U g) := by
  let a := advance (reading v k i) U (handoffOpening v k U g)
  let p := returnWeight (reading v k i) U (handoffOpening v k U g)
  have hap : 1≤a := by dsimp [a]; omega
  have hpp : 0<p := by dsimp [p,returnWeight]; omega
  have hpCast : (p : ℝ)=4*(a : ℝ)-1 := by
    dsimp [p,returnWeight,a]
    rw [Nat.cast_sub (by omega : 1≤4*advance (reading v k i) U (handoffOpening v k U g))]
    push_cast
    ring
  have hsur := (survivor_iff hv k P U hprior g).2 ⟨hg,hwg⟩
  have horder := order_of_move hv k P U hprior g hsur hmove
  have hfast := Fresh.NativeRepeatedReturn.captured_return_ratio hv k P U hprior g hsur horder i hi hwi a hap (by rfl)
  have hratio : (p : ℝ)*reading v k g<reading v k i := by rw [hpCast]; exact hfast
  have hPU := le_of_isMove (disparitySet_pos hv k) hprior
  have hb := (displacement_bounds (reading v k i) P U (abs_nonneg _) hPU hwi).2
  have hd := (displacement_bounds (reading v k g) P U (abs_nonneg _) hPU hwg).1
  have hpR : (0 : ℝ)<(p : ℝ) := by exact_mod_cast hpp
  have hdscale := mul_lt_mul_of_pos_left hd hpR
  have hstep := mul_le_mul_of_nonneg_right hratio.le (sub_nonneg.mpr hPU)
  have hreal : (p : ℝ)*(advance (reading v k g) P U : ℝ)<(advance (reading v k i) P U : ℝ)+(p : ℝ)+1/4 := by
    nlinarith only [hb,hdscale,hstep]
  change p*advance (reading v k g) P U ≤ advance (reading v k i) P U+p
  by_contra hn
  have hNat : advance (reading v k i) P U+p+1≤p*advance (reading v k g) P U := by omega
  have hReal : (advance (reading v k i) P U : ℝ)+(p : ℝ)+1≤(p : ℝ)*(advance (reading v k g) P U : ℝ) := by exact_mod_cast hNat
  linarith only [hreal,hReal]

theorem levelRecovery_into_ordered {v : Fin 8 → ℝ} {k : Fin 8} (h : LevelRecoveryClass v k) : OrderedRecoveryClass v k := by
  obtain ⟨hv,P,U,g,hP,hprior,hg,hw,hmove,hguard,hpassed⟩ := h
  refine ⟨hv,P,U,g,hP,hprior,hg,hw,hmove,hguard,?_⟩
  intro i hi ha hmask
  apply hpassed i hi ha
  rcases hmask with hclear|hgreater
  · exact Or.inl hclear
  · exact Or.inr (by omega)

theorem orderedRecovery_into_level {v : Fin 8 → ℝ} {k : Fin 8} (h : OrderedRecoveryClass v k) : LevelRecoveryClass v k := by
  obtain ⟨hv,P,U,g,hP,hprior,hg,hw,hmove,hguard,hpassed⟩ := h
  refine ⟨hv,P,U,g,hP,hprior,hg,hw,hmove,hguard,?_⟩
  intro i hi ha _
  apply hpassed i hi ha
  by_cases hwi : InWay (reading v k i) U
  · apply Or.inr
    apply lt_of_not_ge
    intro hle
    have hz := ordered_guard_zero hv k P U i g hprior hi hg hwi hw hle hguard hmove
    omega
  · exact Or.inl hwi

#print axioms coupled_return_levels
#print axioms levelRecovery_into_ordered
#print axioms orderedRecovery_into_level

#print axioms general_phase_compact
#print axioms ordered_guard_face
#print axioms general_phase_zero
#print axioms ordered_guard_zero
#print axioms recapture_pair_face
#print axioms recapture_level_order
#print axioms next_capture_ordered_trichotomy
#print axioms maxLevel_into_noReturn
#print axioms maxLevel_isolation
#print axioms orderedRecovery_into_canonical
#print axioms orderedRecovery_isolation
#print axioms generalPhase_into_canonical
#print axioms generalPhase_isolation
end Fresh.NativeOrderedReturnLevels
