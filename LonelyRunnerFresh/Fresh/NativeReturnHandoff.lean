import Fresh.NativeCanonicalReturn

/-! Original surviving returners force the next native opening. Only their
current lower-opening comparisons enter the maximum; no target clearance
is assumed, and closed comparisons preserve simultaneous setters. -/
namespace Fresh.NativeReturnHandoff
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.FastestCaptureRetention

noncomputable def reading (v : Fin 8 → ℝ) (k i : Fin 8) : ℝ := |v i-v k|

noncomputable def Survivor (v : Fin 8 → ℝ) (k : Fin 8) (Q P : ℝ) (i : Fin 8) : Prop :=
  i≠k ∧ 0 < advance (reading v k i) Q P ∧ reading v k i*P < (label (reading v k i*P) : ℝ)+1/8

noncomputable def handoffOpening (v : Fin 8 → ℝ) (k : Fin 8) (P : ℝ) (j : Fin 8) : ℝ :=
  opening (reading v k j) (label (reading v k j*P))

noncomputable def OpeningOrder (v : Fin 8 → ℝ) (k : Fin 8) (Q P : ℝ) (j : Fin 8) : Prop :=
  ∀ i : Fin 8, Survivor v k Q P i →
    reading v k j*((label (reading v k i*P) : ℝ)+1/8) ≤
      reading v k i*((label (reading v k j*P) : ℝ)+1/8)

theorem survivor_iff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (hm : IsMove (disparitySet v k) Q P) (i : Fin 8) :
    Survivor v k Q P i ↔ i≠k ∧ InWay (reading v k i) P := by
  constructor
  · intro h
    exact ⟨h.1,(capture_iff_returned_lower hv k Q P hm i h.1).2 h.2⟩
  · intro h
    exact ⟨h.1,(capture_iff_returned_lower hv k Q P hm i h.1).1 h.2⟩

theorem capture_at_label (s P : ℝ) (hw : InWay s P) :
    (label (s*P) : ℝ)-1/8 < s*P ∧ s*P < (label (s*P) : ℝ)+1/8 := by
  exact ⟨((Fresh.NativeEntryLabels.entry_interval _ _ _).1 (label_entry s P)).1,
    (inWay_iff_lower_not_passed s P).1 hw⟩

theorem next_at_label (s P : ℝ) (hw : InWay s P) :
    nextOpening s P=opening s (label (s*P)) := by
  have hc := capture_at_label s P hw
  have hn : |s*P-(label (s*P) : ℝ)| < 1/8 := by rw [abs_lt]; constructor <;> linarith only [hc.1,hc.2]
  rw [nextOpening_eq hn]
  rfl

theorem forced_handoff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (hm : IsMove (disparitySet v k) Q P) (j : Fin 8)
    (hj : Survivor v k Q P j) (ho : OpeningOrder v k Q P j) :
    P < handoffOpening v k P j ∧ IsMove (disparitySet v k) P (handoffOpening v k P j) := by
  have hc := (survivor_iff hv k Q P hm j).1 hj
  have hmem : reading v k j ∈ disparitySet v k := mem_disparitySet.mpr ⟨j,hc.1,rfl⟩
  have hp := disparitySet_pos hv k _ hmem
  have hn := next_at_label (reading v k j) P hc.2
  refine ⟨?_,Or.inr ⟨reading v k j,hmem,hc.2,hn.symm,?_⟩⟩
  · exact (lt_nextOpening hp hc.2).trans_eq hn
  · intro s hs hws
    obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hs
    have hsi : 0 < reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
    have hsur := (survivor_iff hv k Q P hm i).2 ⟨hi,hws⟩
    rw [next_at_label _ P hws]
    dsimp [handoffOpening,opening]
    apply (div_le_div_iff₀ hsi hp).2
    have hh := ho i hsur
    dsimp [reading] at hh ⊢
    nlinarith only [hh]

theorem order_of_move {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (hm : IsMove (disparitySet v k) Q P) (j : Fin 8) (hj : Survivor v k Q P j)
    (hn : IsMove (disparitySet v k) P (handoffOpening v k P j)) : OpeningOrder v k Q P j := by
  have hc := (survivor_iff hv k Q P hm j).1 hj
  have hp : 0 < reading v k j := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨j,hc.1,rfl⟩)
  intro i hi
  have hci := (survivor_iff hv k Q P hm i).1 hi
  have hmem : reading v k i ∈ disparitySet v k := mem_disparitySet.mpr ⟨i,hci.1,rfl⟩
  have hsi := disparitySet_pos hv k _ hmem
  have hle : nextOpening (reading v k i) P ≤ handoffOpening v k P j := by
    rcases hn with hfixed|⟨s,hs,hws,hR,hmax⟩
    · exact (hfixed.1 _ hmem hci.2).elim
    · exact hmax _ hmem hci.2
  rw [next_at_label _ P hci.2] at hle
  dsimp [handoffOpening,opening] at hle
  have hh := (div_le_div_iff₀ hsi hp).1 hle
  nlinarith only [hh]

theorem handoff_iff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (hm : IsMove (disparitySet v k) Q P) (j : Fin 8) (hj : Survivor v k Q P j) :
    IsMove (disparitySet v k) P (handoffOpening v k P j) ↔ OpeningOrder v k Q P j :=
  ⟨order_of_move hv k Q P hm j hj,fun ho=>(forced_handoff hv k Q P hm j hj ho).2⟩

theorem sole_survivor_order {v : Fin 8 → ℝ} (k : Fin 8) (Q P : ℝ) (j : Fin 8)
    (hsole : ∀ i : Fin 8, Survivor v k Q P i → i=j) : OpeningOrder v k Q P j := by
  intro i hi
  rw [hsole i hi]

theorem sole_survivor_handoff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (hm : IsMove (disparitySet v k) Q P) (j : Fin 8) (hj : Survivor v k Q P j)
    (hsole : ∀ i : Fin 8, Survivor v k Q P i → i=j) :
    P < handoffOpening v k P j ∧ IsMove (disparitySet v k) P (handoffOpening v k P j) :=
  forced_handoff hv k Q P hm j hj (sole_survivor_order k Q P j hsole)

theorem tied_openings {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (hm : IsMove (disparitySet v k) Q P) (j l : Fin 8)
    (hj : Survivor v k Q P j) (hl : Survivor v k Q P l)
    (hoj : OpeningOrder v k Q P j) (hol : OpeningOrder v k Q P l) :
    handoffOpening v k P j=handoffOpening v k P l :=
  isMove_unique (forced_handoff hv k Q P hm j hj hoj).2 (forced_handoff hv k Q P hm l hl hol).2

theorem exists_handoff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (hm : IsMove (disparitySet v k) Q P) (hne : ∃ i : Fin 8, Survivor v k Q P i) :
    ∃ j : Fin 8, Survivor v k Q P j ∧ OpeningOrder v k Q P j ∧
      P < handoffOpening v k P j ∧ IsMove (disparitySet v k) P (handoffOpening v k P j) := by
  classical
  let S := Finset.univ.filter (Survivor v k Q P)
  have hS : S.Nonempty := by obtain ⟨i,hi⟩ := hne; exact ⟨i,by simp [S,hi]⟩
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image S (handoffOpening v k P) hS
  have hjs : Survivor v k Q P j := (Finset.mem_filter.mp hj).2
  have hjc := (survivor_iff hv k Q P hm j).1 hjs
  have hjp : 0 < reading v k j := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨j,hjc.1,rfl⟩)
  have ho : OpeningOrder v k Q P j := by
    intro i hi
    have hic := (survivor_iff hv k Q P hm i).1 hi
    have hip : 0 < reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hic.1,rfl⟩)
    have hh := hmax i (by simp [S,hi])
    dsimp [handoffOpening,opening] at hh
    have hx := (div_le_div_iff₀ hip hjp).1 hh
    nlinarith only [hx]
  exact ⟨j,hjs,ho,forced_handoff hv k Q P hm j hjs ho⟩

theorem selected_not_survivor {v : Fin 8 → ℝ} (k u : Fin 8) (Q P : ℝ) (N : ℤ)
    (hlo : (N : ℝ)-1/8 < reading v k u*Q) (hhi : reading v k u*Q < (N : ℝ)+1/8)
    (hopen : reading v k u*P=(N : ℝ)+1/8) : ¬ Survivor v k Q P u := by
  intro hs
  have hz := selected_advance_zero (reading v k u) Q P N hlo hhi hopen
  have ha := hs.2.1
  omega

theorem predecessor_strict {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (hm : IsMove (disparitySet v k) Q P) (j : Fin 8) (hj : Survivor v k Q P j) : Q < P := by
  have hle := le_of_isMove (disparitySet_pos hv k) hm
  by_contra hn
  have he : P=Q := by linarith
  subst P
  have ha := hj.2.1
  simp [advance] at ha

theorem handoff_identity {v : Fin 8 → ℝ} (hv : IsArrangement v) (k j : Fin 8) (P : ℝ) (hj : j≠k) :
    reading v k j*handoffOpening v k P j=(label (reading v k j*P) : ℝ)+1/8 := by
  have hp : 0 < reading v k j := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨j,hj,rfl⟩)
  dsimp [handoffOpening,opening]
  field_simp

theorem handoff_selected_zero {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (hm : IsMove (disparitySet v k) Q P) (j : Fin 8) (hj : Survivor v k Q P j) :
    advance (reading v k j) P (handoffOpening v k P j)=0 := by
  have hc := (survivor_iff hv k Q P hm j).1 hj
  have hb := capture_at_label (reading v k j) P hc.2
  exact selected_advance_zero _ P _ _ hb.1 hb.2 (handoff_identity hv k j P hc.1)

theorem sole_return_replacement {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (hm : IsMove (disparitySet v k) Q P) (j : Fin 8) (hj : Survivor v k Q P j)
    (hsole : ∀ i : Fin 8, Survivor v k Q P i → i=j) :
    IsMove (disparitySet v k) P (handoffOpening v k P j) ∧
      ∀ i : Fin 8, Survivor v k P (handoffOpening v k P j) i → ¬ Survivor v k Q P i := by
  refine ⟨(sole_survivor_handoff hv k Q P hm j hj hsole).2,?_⟩
  intro i hi hold
  have he := hsole i hold
  subst i
  have hz := handoff_selected_zero hv k Q P hm j hj
  have ha := hi.2.1
  omega

theorem equal_readings_order {v : Fin 8 → ℝ} (k : Fin 8) (Q P : ℝ) (j : Fin 8)
    (hsame : ∀ i : Fin 8, Survivor v k Q P i → reading v k i=reading v k j) : OpeningOrder v k Q P j := by
  intro i hi
  rw [hsame i hi]

theorem equal_readings_handoff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (hm : IsMove (disparitySet v k) Q P) (j : Fin 8) (hj : Survivor v k Q P j)
    (hsame : ∀ i : Fin 8, Survivor v k Q P i → reading v k i=reading v k j) :
    P < handoffOpening v k P j ∧ IsMove (disparitySet v k) P (handoffOpening v k P j) :=
  forced_handoff hv k Q P hm j hj (equal_readings_order k Q P j hsame)

-- A symmetric pair may have one disparity while retaining two physical identities.
-- The entire previous surviving group clears at its common selected opening.
theorem equal_readings_replacement {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (hm : IsMove (disparitySet v k) Q P) (j : Fin 8) (hj : Survivor v k Q P j)
    (hsame : ∀ i : Fin 8, Survivor v k Q P i → reading v k i=reading v k j) :
    IsMove (disparitySet v k) P (handoffOpening v k P j) ∧
      ∀ i : Fin 8, Survivor v k P (handoffOpening v k P j) i → ¬ Survivor v k Q P i := by
  refine ⟨(equal_readings_handoff hv k Q P hm j hj hsame).2,?_⟩
  intro i hi hold
  have hz := handoff_selected_zero hv k Q P hm j hj
  have ha := hi.2.1
  rw [hsame i hold] at ha
  omega

#print axioms equal_readings_replacement
#print axioms equal_readings_order
#print axioms equal_readings_handoff
#print axioms predecessor_strict
#print axioms handoff_identity
#print axioms handoff_selected_zero
#print axioms sole_return_replacement
#print axioms survivor_iff
#print axioms capture_at_label
#print axioms next_at_label
#print axioms forced_handoff
#print axioms order_of_move
#print axioms handoff_iff
#print axioms sole_survivor_order
#print axioms sole_survivor_handoff
#print axioms tied_openings
#print axioms exists_handoff
#print axioms selected_not_survivor
end Fresh.NativeReturnHandoff
