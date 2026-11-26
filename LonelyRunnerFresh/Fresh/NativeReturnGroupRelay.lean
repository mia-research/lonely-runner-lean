import Fresh.NativeSingleReturnArrangement

/-! A native captured group can reset as a whole at its forced handoff.
Only original nonreturners may then advance, in their original closing
order. Compact capture and common-opening inputs derive this reset;
the reset is local and supplies no descending chain across later moves. -/
namespace Fresh.NativeReturnGroupRelay
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement Fresh.NativeReturnClosingOrder

noncomputable def Reset (v : Fin 8 → ℝ) (k : Fin 8) (P R : ℝ) (c : Fin 8) : Prop :=
  Survivor v k P R c ∧ OpeningOrder v k P R c ∧
    ∀ i : Fin 8, i≠k → 0 < advance (reading v k i) P R → advance (reading v k i) R (handoffOpening v k R c)=0

noncomputable def CompactEntry (v : Fin 8 → ℝ) (k : Fin 8) (P R : ℝ) (c : Fin 8) : Prop :=
  Survivor v k P R c ∧ OpeningOrder v k P R c ∧
    ∀ i : Fin 8, i≠k → 0 < advance (reading v k i) P R →
      InWay (reading v k i) R ∧ reading v k i≤3*reading v k c

noncomputable def CommonEntry (v : Fin 8 → ℝ) (k : Fin 8) (P R : ℝ) (c : Fin 8) : Prop :=
  Survivor v k P R c ∧ ∀ i : Fin 8, i≠k → 0 < advance (reading v k i) P R →
    handoffOpening v k R i=handoffOpening v k R c

noncomputable def GroupFits (v : Fin 8 → ℝ) (k : Fin 8) (P R : ℝ) (c : Fin 8) : Prop :=
  ∀ i : Fin 8, i≠k → advance (reading v k i) P R=0 → handoffOpening v k R c≤closing (reading v k i) P

theorem reset_move {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hr : Reset v k P R c) :
    R<handoffOpening v k R c ∧ IsMove (disparitySet v k) R (handoffOpening v k R c) :=
  forced_handoff hv k P R hm c hr.1 hr.2.1

theorem compact_into_reset {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hb : CompactEntry v k P R c) : Reset v k P R c := by
  have ht := forced_handoff hv k P R hm c hb.1 hb.2.1
  have hcap := capture_at_label (reading v k c) R ((survivor_iff hv k P R hm c).1 hb.1).2
  have hd : 0 < reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hb.1.1,rfl⟩)
  have hid := handoff_identity hv k c R hb.1.1
  refine ⟨hb.1,hb.2.1,?_⟩
  intro i hi ha
  have hbi := hb.2.2 i hi ha
  have hnear := capture_at_label (reading v k i) R hbi.1
  have hmem : reading v k i∈disparitySet v k := mem_disparitySet.mpr ⟨i,hi,rfl⟩
  have horder := Fresh.FastestCaptureRecovery.captured_order_of_move _ _ ht.2 hmem hd
    (disparitySet_pos hv k _ hmem) hid hnear.1 hnear.2
  have hw := Fresh.NativeRelativeCapture.captured_window _ _ R _ _ _ hd hbi.2 hid hcap.1 hcap.2 hnear.2 horder
  have hl := (entry_iff_label _ _ _).1 (Or.inl ⟨hw.1,hw.2.le⟩)
  simp only [advance,hl,sub_self,Int.toNat_zero]

theorem common_returner_captured {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hb : CommonEntry v k P R c)
    (i : Fin 8) (hi : i≠k) (ha : 0 < advance (reading v k i) P R) : InWay (reading v k i) R := by
  have hc := (survivor_iff hv k P R hm c).1 hb.1
  have hd : 0 < reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc.1,rfl⟩)
  have hRc : R<handoffOpening v k R c := by
    have hn := next_at_label (reading v k c) R hc.2
    exact (lt_nextOpening hd hc.2).trans_eq hn
  have hipos : 0 < reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  have hid := handoff_identity hv k i R hi
  rw [hb.2 i hi ha] at hid
  have hmuli := mul_lt_mul_of_pos_left hRc hipos
  apply (inWay_iff_lower_not_passed _ _).2
  linarith only [hmuli,hid]

theorem common_move {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hb : CommonEntry v k P R c) :
    R<handoffOpening v k R c ∧ IsMove (disparitySet v k) R (handoffOpening v k R c) := by
  have hc := (survivor_iff hv k P R hm c).1 hb.1
  have hmem : reading v k c∈disparitySet v k := mem_disparitySet.mpr ⟨c,hc.1,rfl⟩
  have hd := disparitySet_pos hv k _ hmem
  have hn := next_at_label (reading v k c) R hc.2
  refine ⟨(lt_nextOpening hd hc.2).trans_eq hn,Or.inr ⟨reading v k c,hmem,hc.2,hn.symm,?_⟩⟩
  intro s hs hws
  obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hs
  have hsur := (survivor_iff hv k P R hm i).2 ⟨hi,hws⟩
  have hh := hb.2 i hi hsur.2.1
  have hn' := next_at_label (reading v k i) R hws
  exact le_of_eq (hn'.trans hh)

theorem common_into_reset {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hb : CommonEntry v k P R c) : Reset v k P R c := by
  have ht := common_move hv k P R hm c hb
  refine ⟨hb.1,order_of_move hv k P R hm c hb.1 ht.2,?_⟩
  intro i hi ha
  have hcap := capture_at_label (reading v k i) R (common_returner_captured hv k P R hm c hb i hi ha)
  have hid := handoff_identity hv k i R hi
  rw [hb.2 i hi ha] at hid
  exact selected_advance_zero _ R _ _ hcap.1 hcap.2 hid

theorem common_compact_representative {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hb : CommonEntry v k P R c) :
    ∃ d : Fin 8, CompactEntry v k P R d ∧ handoffOpening v k R d=handoffOpening v k R c := by
  classical
  let S := Finset.univ.filter (fun i : Fin 8=>i≠k ∧ 0 < advance (reading v k i) P R)
  have hne : S.Nonempty := ⟨c,by simp [S,hb.1.1,hb.1.2.1]⟩
  obtain ⟨d,hd,hmax⟩ := Finset.exists_max_image S (reading v k) hne
  have hdm := (Finset.mem_filter.mp hd).2
  have hdcap := common_returner_captured hv k P R hm c hb d hdm.1 hdm.2
  have hsur := (survivor_iff hv k P R hm d).2 ⟨hdm.1,hdcap⟩
  have heq := hb.2 d hdm.1 hdm.2
  have ht := common_move hv k P R hm c hb
  have hmove : IsMove (disparitySet v k) R (handoffOpening v k R d) := by rw [heq]; exact ht.2
  refine ⟨d,⟨hsur,order_of_move hv k P R hm d hsur hmove,?_⟩,heq⟩
  intro i hi ha
  have hle := hmax i (by simp [S,hi,ha])
  have hdpos : 0≤reading v k d := abs_nonneg _
  exact ⟨common_returner_captured hv k P R hm c hb i hi ha,by linarith only [hle,hdpos]⟩

theorem single_into_compact {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8)
    (hs : Fresh.NativeSingleReturnRelay.SingleReturn v k P R c) (hc : InWay (reading v k c) R) : CompactEntry v k P R c := by
  have hsur := (survivor_iff hv k P R hm c).2 ⟨hs.1,hc⟩
  refine ⟨hsur,equal_readings_order k P R c (fun i hi=>hs.2.2 i hi.1 hi.2.1),?_⟩
  intro i hi ha
  have heq := hs.2.2 i hi ha
  rw [heq]
  exact ⟨hc,by have hh : 0≤reading v k c := abs_nonneg _; linarith⟩

theorem reset_return_iff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hr : Reset v k P R c) (i : Fin 8) (hi : i≠k) :
    0 < advance (reading v k i) R (handoffOpening v k R c) ↔
      advance (reading v k i) P R=0 ∧ closing (reading v k i) P<handoffOpening v k R c := by
  have ht := reset_move hv k P R hm c hr
  by_cases hz : advance (reading v k i) P R=0
  · have hid := advance_identity (reading v k i) P R (abs_nonneg _) (le_of_isMove (disparitySet_pos hv k) hm)
    simp only [hz,Nat.cast_zero,add_zero] at hid
    have hipos : 0 < reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
    rw [positive_iff_closing_passed _ R _ hipos ht.1.le]
    simp only [closing,hid,hz,true_and]
  · have hreset := hr.2.2 i hi (by omega)
    constructor
    · intro h
      omega
    · intro h
      exact (hz h.1).elim

theorem reset_zero_iff_fits {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hr : Reset v k P R c) :
    NoReturnSecond v k R c ↔ GroupFits v k P R c := by
  constructor
  · intro hz i hi hold
    by_contra hn
    have ha := (reset_return_iff hv k P R hm c hr i hi).2 ⟨hold,lt_of_not_ge hn⟩
    have hh := hz i hi
    omega
  · intro hf i hi
    by_contra hn
    have ha : 0 < advance (reading v k i) R (handoffOpening v k R c) := by omega
    have hh := (reset_return_iff hv k P R hm c hr i hi).1 ha
    exact not_lt_of_ge (hf i hi hh.1) hh.2

theorem reset_capture_iff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hr : Reset v k P R c) (i : Fin 8) (hi : i≠k) :
    InWay (reading v k i) (handoffOpening v k R c) ↔
      advance (reading v k i) P R=0 ∧ closing (reading v k i) P<handoffOpening v k R c ∧
        reading v k i*handoffOpening v k R c<(label (reading v k i*handoffOpening v k R c) : ℝ)+1/8 := by
  have ht := reset_move hv k P R hm c hr
  have hb : InWay (reading v k i) (handoffOpening v k R c) ↔
      0 < advance (reading v k i) R (handoffOpening v k R c) ∧
        reading v k i*handoffOpening v k R c<(label (reading v k i*handoffOpening v k R c) : ℝ)+1/8 :=
    capture_iff_returned_lower hv k R _ ht.2 i hi
  rw [hb,reset_return_iff hv k P R hm c hr i hi]
  exact and_assoc

#print axioms reset_move
#print axioms compact_into_reset
#print axioms common_returner_captured
#print axioms common_move
#print axioms common_into_reset
#print axioms common_compact_representative
#print axioms single_into_compact
#print axioms reset_return_iff
#print axioms reset_zero_iff_fits
#print axioms reset_capture_iff
end Fresh.NativeReturnGroupRelay
