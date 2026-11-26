import Fresh.NativeCurrentLabelPacket
import Fresh.NativeOneReaderDeformation

/-! A same-label captured packet cannot split into different capture labels
at the next positive-label opening. Continuing members keep this property
through any supplied history, even when outsiders set the openings. When a
member sets the next move, its continuing packet clears. Fresh captures and
members that became clear and returned remain explicit separate duties. -/
namespace Fresh.NativeRecapturedLabelReset
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels
  Fresh.NativeReturnHandoff Fresh.NativeReturnSurvivors Fresh.NativeOneReaderDeformation
  Fresh.NativeReturnLevelClearance Fresh.NativeReturnClosingOrder
  Fresh.NativeCurrentLabelPacket Fresh.NativeCanonicalReturn
  Fresh.FastestCaptureRetention

theorem capture_label_positive (s R : ℝ) (hfirst : (1/8 : ℝ) ≤ s*R)
    (hw : InWay s R) : 0 < label (s*R) := by
  have hh := (capture_at_label s R hw).2
  by_contra hn
  have hi : label (s*R) ≤ 0 := by omega
  have hr : (label (s*R) : ℝ) ≤ 0 := by exact_mod_cast hi
  linarith only [hh,hr,hfirst]

theorem capture_positive_after_start (m s R : ℝ) (hm : 0 < m) (hms : m ≤ s)
    (hstart : 1/(8*m) ≤ R) (hw : InWay s R) : 0 < label (s*R) := by
  have hRp : 0 < R := lt_of_lt_of_le (by positivity : (0 : ℝ) < 1/(8*m)) hstart
  have hface := (div_le_iff₀ (by positivity : (0 : ℝ) < 8*m)).1 hstart
  have hmin : (1/8 : ℝ) ≤ m*R := by nlinarith only [hface]
  exact capture_label_positive s R (hmin.trans (mul_le_mul_of_nonneg_right hms hRp.le)) hw

-- This is a local consequence of the supplied opening, never a time budget.
theorem opening_relative_face (d R S : ℝ) (hd : 0 < d)
    (hw : InWay d R) (hn : 0 < label (d*R))
    (ho : d*S=(label (d*R) : ℝ)+1/8) : 7*S < 9*R := by
  have hl := (capture_at_label d R hw).1
  have hN : (1 : ℝ) ≤ (label (d*R) : ℝ) := by exact_mod_cast hn
  have hh : 7*(d*S) < 9*(d*R) := by linarith only [hl,hN,ho]
  nlinarith only [hh,hd]

theorem capture_labels_equal_of_close (s d S : ℝ)
    (hs : InWay s S) (hd : InWay d S) (hclose : |(s-d)*S| ≤ 3/4) :
    label (s*S)=label (d*S) := by
  have hc := abs_le.mp hclose
  have hcs := capture_at_label s S hs
  have hcd := capture_at_label d S hd
  by_contra hn
  rcases lt_or_gt_of_ne hn with hlt|hgt
  · have hi : label (s*S)+1 ≤ label (d*S) := by omega
    have hr : (label (s*S) : ℝ)+1 ≤ (label (d*S) : ℝ) := by exact_mod_cast hi
    nlinarith only [hcs.2,hcd.1,hr,hc.1]
  · have hi : label (d*S)+1 ≤ label (s*S) := by omega
    have hr : (label (d*S) : ℝ)+1 ≤ (label (s*S) : ℝ) := by exact_mod_cast hi
    nlinarith only [hcd.2,hcs.1,hr,hc.2]

theorem same_label_capture_spread (s d R : ℝ)
    (hs : InWay s R) (hd : InWay d R) (hl : label (s*R)=label (d*R)) :
    |(s-d)*R| < 1/4 := by
  have hcs := capture_at_label s R hs
  have hcd := capture_at_label d R hd
  rw [hl] at hcs
  rw [abs_lt]
  constructor <;> nlinarith only [hcs.1,hcs.2,hcd.1,hcd.2]

theorem recaptured_labels_equal (s d R S : ℝ) (hR : 0 < R) (hS : 0 ≤ S)
    (hSR : S ≤ 3*R) (hs : InWay s R) (hd : InWay d R)
    (hl : label (s*R)=label (d*R)) (hsnow : InWay s S) (hdnow : InWay d S) :
    label (s*S)=label (d*S) := by
  have hspread := same_label_capture_spread s d R hs hd hl
  rw [abs_mul,abs_of_pos hR] at hspread
  have hscale := mul_le_mul_of_nonneg_left hSR (abs_nonneg (s-d))
  apply capture_labels_equal_of_close s d S hsnow hdnow
  rw [abs_mul,abs_of_nonneg hS]
  nlinarith only [hspread,hscale]

theorem handoff_recaptured_labels_equal {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k a i g : Fin 8) (R : ℝ) (hR : 0 < R) (ha : a≠k)
    (hwa : InWay (reading v k a) R) (hN : 0 < label (reading v k a*R))
    (hwi : InWay (reading v k i) R) (hwg : InWay (reading v k g) R)
    (hl : label (reading v k i*R)=label (reading v k g*R))
    (hiS : InWay (reading v k i) (handoffOpening v k R a))
    (hgS : InWay (reading v k g) (handoffOpening v k R a)) :
    label (reading v k i*handoffOpening v k R a)=
      label (reading v k g*handoffOpening v k R a) := by
  have hap : 0 < reading v k a := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hrel := opening_relative_face _ R _ hap hwa hN (handoff_identity hv k a R ha)
  have hRS : R < handoffOpening v k R a := by
    change R < opening (reading v k a) (label (reading v k a*R))
    rw [←next_at_label _ R hwa]
    exact lt_nextOpening hap hwa
  exact recaptured_labels_equal _ _ R _ hR (hR.le.trans hRS.le)
    (by linarith only [hrel,hR]) hwi hwg hl hiS hgS

theorem same_label_minimum_move {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k g : Fin 8) (S : ℝ) (hg : g≠k) (hwg : InWay (reading v k g) S)
    (hN : 0 < label (reading v k g*S))
    (hl : ∀ i : Fin 8, i≠k → InWay (reading v k i) S →
      label (reading v k i*S)=label (reading v k g*S))
    (hmin : ∀ i : Fin 8, i≠k → InWay (reading v k i) S → reading v k g ≤ reading v k i) :
    IsMove (disparitySet v k) S (handoffOpening v k S g) := by
  have hgp : 0 < reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have hnum : 0 ≤ (label (reading v k g*S) : ℝ)+1/8 := by
    have hh : (0 : ℝ) < (label (reading v k g*S) : ℝ) := by exact_mod_cast hN
    linarith only [hh]
  refine Or.inr ⟨reading v k g,mem_disparitySet.mpr ⟨g,hg,rfl⟩,hwg,(next_at_label _ S hwg).symm,?_⟩
  intro d hd hwd
  obtain ⟨i,hik,rfl⟩ := mem_disparitySet.mp hd
  change InWay (reading v k i) S at hwd
  change nextOpening (reading v k i) S ≤ handoffOpening v k S g
  rw [next_at_label _ S hwd]
  dsimp [handoffOpening,opening]
  rw [hl i hik hwd]
  exact div_le_div_of_nonneg_left hnum hgp (hmin i hik hwd)

theorem recaptured_labels_reflect (s d R S : ℝ) (hR : 0 < R) (hRS : R ≤ S)
    (hs : InWay s R) (hd : InWay d R) (hsnow : InWay s S) (hdnow : InWay d S)
    (hl : label (s*S)=label (d*S)) : label (s*R)=label (d*R) := by
  have hS : 0 < S := hR.trans_le hRS
  have hspread := same_label_capture_spread s d S hsnow hdnow hl
  rw [abs_mul,abs_of_pos hS] at hspread
  have hscale := mul_le_mul_of_nonneg_left hRS (abs_nonneg (s-d))
  apply capture_labels_equal_of_close s d R hs hd
  rw [abs_mul,abs_of_pos hR]
  linarith only [hspread,hscale]

theorem handoff_recaptured_partition {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k a i g : Fin 8) (R : ℝ) (hR : 0 < R) (ha : a≠k)
    (hwa : InWay (reading v k a) R) (hN : 0 < label (reading v k a*R))
    (hwi : InWay (reading v k i) R) (hwg : InWay (reading v k g) R)
    (hiS : InWay (reading v k i) (handoffOpening v k R a))
    (hgS : InWay (reading v k g) (handoffOpening v k R a)) :
    label (reading v k i*handoffOpening v k R a)=label (reading v k g*handoffOpening v k R a) ↔
      label (reading v k i*R)=label (reading v k g*R) := by
  have hap : 0 < reading v k a := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hRS : R ≤ handoffOpening v k R a := by
    change R ≤ opening (reading v k a) (label (reading v k a*R))
    rw [←next_at_label _ R hwa]
    exact (lt_nextOpening hap hwa).le
  exact ⟨recaptured_labels_reflect _ _ R _ hR hRS hwi hwg hiS hgS,
    fun hl=>handoff_recaptured_labels_equal hv k a i g R hR ha hwa hN hwi hwg hl hiS hgS⟩

theorem recaptured_pair_zero {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k a i g : Fin 8) (R : ℝ) (hR : 0 < R) (ha : a≠k) (hi : i≠k) (hg : g≠k)
    (hwa : InWay (reading v k a) R) (hN : 0 < label (reading v k a*R))
    (hm : IsMove (disparitySet v k) R (handoffOpening v k R a))
    (hwi : InWay (reading v k i) R) (hwg : InWay (reading v k g) R)
    (hl : label (reading v k i*R)=label (reading v k g*R))
    (hiS : InWay (reading v k i) (handoffOpening v k R a))
    (hgS : InWay (reading v k g) (handoffOpening v k R a))
    (hm2 : IsMove (disparitySet v k) (handoffOpening v k R a)
      (handoffOpening v k (handoffOpening v k R a) g)) :
    advance (reading v k i) (handoffOpening v k R a)
      (handoffOpening v k (handoffOpening v k R a) g)=0 := by
  have he := handoff_recaptured_labels_equal hv k a i g R hR ha hwa hN hwi hwg hl hiS hgS
  have hf := recaptured_label_floor hv k a R hR ha hwa hm g hg hwg hgS
  have hRS := le_of_isMove (disparitySet_pos hv k) hm
  have hmono := label_monotone (mul_le_mul_of_nonneg_left hRS (abs_nonneg (v g-v k)))
  have hcone : label (reading v k i*handoffOpening v k R a) <
      3*label (reading v k g*handoffOpening v k R a) := by
    change label (reading v k g*R) ≤ label (reading v k g*handoffOpening v k R a) at hmono
    rw [he]
    omega
  exact captured_ratio_zero hv k _ i g hi hg hiS hgS
    (captured_label_compact _ _ _ (hR.trans_le hRS) hiS hgS hcone).le hm2

-- The selected second reader belongs to the recaptured packet. Other current
-- captures may join when their current labels lie in its proved reset cone.
-- STANDING: DEFINITION
noncomputable def Frame (v : Fin 8 → ℝ) (k : Fin 8) (R : ℝ) (a g : Fin 8) : Prop :=
  a≠k ∧ g≠k ∧ 0 < R ∧ InWay (reading v k a) R ∧ 0 < label (reading v k a*R) ∧
    IsMove (disparitySet v k) R (handoffOpening v k R a) ∧
    InWay (reading v k g) R ∧ InWay (reading v k g) (handoffOpening v k R a) ∧
    IsMove (disparitySet v k) (handoffOpening v k R a)
      (handoffOpening v k (handoffOpening v k R a) g) ∧
    ∀ i : Fin 8, i≠k → InWay (reading v k i) (handoffOpening v k R a) →
      (InWay (reading v k i) R ∧ label (reading v k i*R)=label (reading v k g*R)) ∨
      label (reading v k i*handoffOpening v k R a) <
        3*label (reading v k g*handoffOpening v k R a)

theorem frame_packet {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (R : ℝ) (a g : Fin 8) (h : Frame v k R a g) :
    Packet v k (handoffOpening v k R a) g := by
  obtain ⟨ha,hg,hR,hwa,hN,hm,hwg,hgS,hm2,hmask⟩ := h
  have hfloor := recaptured_label_floor hv k a R hR ha hwa hm g hg hwg hgS
  have hRS := le_of_isMove (disparitySet_pos hv k) hm
  have hmono := label_monotone (mul_le_mul_of_nonneg_left hRS (abs_nonneg (v g-v k)))
  have hpositive : 0 < label (reading v k g*handoffOpening v k R a) := by
    change label (reading v k g*R) ≤ label (reading v k g*handoffOpening v k R a) at hmono
    omega
  refine ⟨hg,hgS,?_⟩
  intro i hi hwi
  rcases hmask i hi hwi with hold|hcone
  · have he := handoff_recaptured_labels_equal hv k a i g R hR ha hwa hN hold.1 hwg hold.2 hwi hgS
    rw [he]
    omega
  · exact hcone

theorem frame_next_zero {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (R : ℝ) (a g : Fin 8) (h : Frame v k R a g)
    (i : Fin 8) (hi : i≠k) (hw : InWay (reading v k i) (handoffOpening v k R a)) :
    advance (reading v k i) (handoffOpening v k R a)
      (handoffOpening v k (handoffOpening v k R a) g)=0 := by
  have hp := frame_packet hv k R a g h
  obtain ⟨ha,hg,hR,hwa,hN,hm,hwg,hgS,hm2,hmask⟩ := h
  have hRS := le_of_isMove (disparitySet_pos hv k) hm
  exact packet_member_zero hv k g _ (hR.trans_le hRS) hp hm2 i hi hw

-- Arbitrary supplied history, not a bound on how many exchanges can occur.
theorem continuing_history_labels {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k i g : Fin 8) (state : ℕ → ℝ) (setter : ℕ → Fin 8) (N : ℕ)
    (hR : ∀ j, j ≤ N → 0 < state j)
    (hw : ∀ j, j < N → setter j≠k ∧ InWay (reading v k (setter j)) (state j) ∧
      0 < label (reading v k (setter j)*state j) ∧ state (j+1)=handoffOpening v k (state j) (setter j))
    (hi : ∀ j, j ≤ N → InWay (reading v k i) (state j))
    (hg : ∀ j, j ≤ N → InWay (reading v k g) (state j))
    (hl : label (reading v k i*state 0)=label (reading v k g*state 0)) :
    ∀ j, j ≤ N → label (reading v k i*state j)=label (reading v k g*state j) := by
  intro j
  induction j with
  | zero => intro _; exact hl
  | succ j ih =>
    intro hj
    obtain ⟨ha,hwa,hN,he⟩ := hw j (by omega)
    rw [he]
    exact handoff_recaptured_labels_equal hv k (setter j) i g (state j) (hR j (by omega)) ha hwa hN
      (hi j (by omega)) (hg j (by omega)) (ih (by omega))
      (he ▸ hi (j+1) hj) (he ▸ hg (j+1) hj)

theorem continuing_history_partition {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k i g : Fin 8) (state : ℕ → ℝ) (setter : ℕ → Fin 8) (N : ℕ)
    (hR : ∀ j, j ≤ N → 0 < state j)
    (hw : ∀ j, j < N → setter j≠k ∧ InWay (reading v k (setter j)) (state j) ∧
      0 < label (reading v k (setter j)*state j) ∧ state (j+1)=handoffOpening v k (state j) (setter j))
    (hi : ∀ j, j ≤ N → InWay (reading v k i) (state j))
    (hg : ∀ j, j ≤ N → InWay (reading v k g) (state j)) :
    ∀ j, j ≤ N → (label (reading v k i*state j)=label (reading v k g*state j) ↔
      label (reading v k i*state 0)=label (reading v k g*state 0)) := by
  have hmono : ∀ j, j ≤ N → state 0 ≤ state j := by
    intro j
    induction j with
    | zero => intro _; exact le_rfl
    | succ j ih =>
      intro hj
      obtain ⟨ha,hwa,hN,he⟩ := hw j (by omega)
      have hp : 0 < reading v k (setter j) := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨setter j,ha,rfl⟩)
      have hstep : state j ≤ state (j+1) := by
        rw [he]
        change state j ≤ opening (reading v k (setter j)) (label (reading v k (setter j)*state j))
        rw [←next_at_label _ _ hwa]
        exact (lt_nextOpening hp hwa).le
      exact (ih (by omega)).trans hstep
  intro j hj
  constructor
  · exact recaptured_labels_reflect _ _ (state 0) (state j) (hR 0 (by omega))
      (hmono j hj) (hi 0 (by omega)) (hg 0 (by omega)) (hi j hj) (hg j hj)
  · intro hl
    exact continuing_history_labels hv k i g state setter N hR hw hi hg hl j hj

theorem pure_recapture_frame {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k a g : Fin 8) (R : ℝ) (ha : a≠k) (hg : g≠k) (hR : 0 < R)
    (hwa : InWay (reading v k a) R) (hN : 0 < label (reading v k a*R))
    (hm : IsMove (disparitySet v k) R (handoffOpening v k R a))
    (hwg : InWay (reading v k g) R)
    (hgS : InWay (reading v k g) (handoffOpening v k R a))
    (hold : ∀ i : Fin 8, i≠k → InWay (reading v k i) (handoffOpening v k R a) →
      InWay (reading v k i) R ∧ label (reading v k i*R)=label (reading v k g*R))
    (hmin : ∀ i : Fin 8, i≠k → InWay (reading v k i) (handoffOpening v k R a) →
      reading v k g ≤ reading v k i) : Frame v k R a g := by
  have hfloor := recaptured_label_floor hv k a R hR ha hwa hm g hg hwg hgS
  have hRS := le_of_isMove (disparitySet_pos hv k) hm
  have hmono := label_monotone (mul_le_mul_of_nonneg_left hRS (abs_nonneg (v g-v k)))
  have hp : 0 < label (reading v k g*handoffOpening v k R a) := by
    change label (reading v k g*R) ≤ label (reading v k g*handoffOpening v k R a) at hmono
    omega
  have hlabels : ∀ i : Fin 8, i≠k → InWay (reading v k i) (handoffOpening v k R a) →
      label (reading v k i*handoffOpening v k R a)=label (reading v k g*handoffOpening v k R a) := by
    intro i hi hwi
    have hh := hold i hi hwi
    exact handoff_recaptured_labels_equal hv k a i g R hR ha hwa hN hh.1 hwg hh.2 hwi hgS
  exact ⟨ha,hg,hR,hwa,hN,hm,hwg,hgS,
    same_label_minimum_move hv k g _ hg hgS hp hlabels hmin,
    fun i hi hw=>Or.inl (hold i hi hw)⟩

-- STANDING: DEFINITION
noncomputable def RetainedResetClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (R : ℝ) (a g : Fin 8), Frame v k R a g ∧
    ∀ i : Fin 8, i≠k → ¬InWay (reading v k i) (handoffOpening v k R a) →
      handoffOpening v k (handoffOpening v k R a) g ≤ closing (reading v k i) (handoffOpening v k R a)

-- STANDING: DEFINITION
noncomputable def RecoveredResetClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (R : ℝ) (a g : Fin 8), Frame v k R a g ∧
    ∀ i : Fin 8, i≠k → ¬InWay (reading v k i) (handoffOpening v k R a) →
      0 < advance (reading v k i) (handoffOpening v k R a)
        (handoffOpening v k (handoffOpening v k R a) g) →
      reading v k g*((label (reading v k i*handoffOpening v k (handoffOpening v k R a) g) : ℝ)+1/8) ≤
        reading v k i*((label (reading v k g*handoffOpening v k R a) : ℝ)+1/8)

theorem retainedReset_into_current {v : Fin 8 → ℝ} {k : Fin 8}
    (h : RetainedResetClass v k) : Fresh.NativeCurrentLabelPacket.RetainedClass v k := by
  obtain ⟨hv,R,a,g,hf,hclose⟩ := h
  have hp := frame_packet hv k R a g hf
  obtain ⟨ha,hg,hR,hwa,hN,hm,hwg,hgS,hm2,hmask⟩ := hf
  exact ⟨hv,_,g,hR.trans_le (le_of_isMove (disparitySet_pos hv k) hm),hp,hm2,hclose⟩

theorem recoveredReset_into_current {v : Fin 8 → ℝ} {k : Fin 8}
    (h : RecoveredResetClass v k) : Fresh.NativeCurrentLabelPacket.RecoveredClass v k := by
  obtain ⟨hv,R,a,g,hf,hpassed⟩ := h
  have hp := frame_packet hv k R a g hf
  obtain ⟨ha,hg,hR,hwa,hN,hm,hwg,hgS,hm2,hmask⟩ := hf
  exact ⟨hv,_,g,hR.trans_le (le_of_isMove (disparitySet_pos hv k) hm),hp,hm2,hpassed⟩

theorem retainedReset_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : RetainedResetClass v k) : Isolation v k :=
  Fresh.NativeCurrentLabelPacket.retained_isolation (retainedReset_into_current h)

theorem recoveredReset_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : RecoveredResetClass v k) : Isolation v k :=
  Fresh.NativeCurrentLabelPacket.recovered_isolation (recoveredReset_into_current h)

#print axioms recaptured_labels_reflect
#print axioms handoff_recaptured_partition
#print axioms recaptured_pair_zero
#print axioms continuing_history_partition
#print axioms pure_recapture_frame
#print axioms retainedReset_into_current
#print axioms recoveredReset_into_current
#print axioms retainedReset_isolation
#print axioms recoveredReset_isolation

#print axioms capture_positive_after_start
#print axioms capture_label_positive
#print axioms opening_relative_face
#print axioms capture_labels_equal_of_close
#print axioms same_label_capture_spread
#print axioms recaptured_labels_equal
#print axioms handoff_recaptured_labels_equal
#print axioms same_label_minimum_move
#print axioms frame_packet
#print axioms frame_next_zero
#print axioms continuing_history_labels
end Fresh.NativeRecapturedLabelReset
