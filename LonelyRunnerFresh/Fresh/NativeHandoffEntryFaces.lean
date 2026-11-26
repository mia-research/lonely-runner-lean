import Fresh.NativeReturnHandoffArrangement

/-! At a given native handoff entry, one original first-closing face
characterizes unchanged successor labels exactly. This is a local input
characterization; it neither forces the face nor bounds subsequent moves. -/
namespace Fresh.NativeHandoffEntryFaces
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement

noncomputable def FirstClosing (v : Fin 8 → ℝ) (k : Fin 8) (P : ℝ) (c : Fin 8) : Prop :=
  c≠k ∧ ∀ i : Fin 8, i≠k →
    reading v k i*((label (reading v k c*P) : ℝ)+7/8) ≤
      reading v k c*((label (reading v k i*P) : ℝ)+7/8)

noncomputable def SharpEntrySecond (v : Fin 8 → ℝ) (k : Fin 8) (P : ℝ) (j c : Fin 8) : Prop :=
  FirstClosing v k P c ∧
    reading v k c*((label (reading v k j*P) : ℝ)+1/8-reading v k j*P) ≤
      reading v k j*((label (reading v k c*P) : ℝ)+7/8-reading v k c*P)

-- STANDING: DEFINITION
noncomputable def HandoffSharpClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (Q P : ℝ) (j c : Fin 8), HandoffEntry v k Q P j ∧ SharpEntrySecond v k P j c

-- STANDING: DEFINITION
noncomputable def SoleSharpClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (Q P : ℝ) (j c : Fin 8), 0<Q ∧ IsMove (disparitySet v k) Q P ∧
    Survivor v k Q P j ∧ (∀ i : Fin 8, Survivor v k Q P i → i=j) ∧ SharpEntrySecond v k P j c

theorem noReturn_iff_original_upper {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (j : Fin 8) (he : HandoffEntry v k Q P j) :
    NoReturnSecond v k P j ↔ ∀ i : Fin 8, i≠k →
      reading v k i*handoffOpening v k P j ≤ (label (reading v k i*P) : ℝ)+7/8 := by
  have ht := forced_handoff hv k Q P he.2.1 j he.2.2.1 he.2.2.2
  constructor
  · intro hz i hi
    have hid := advance_identity (reading v k i) P (handoffOpening v k P j) (abs_nonneg _) ht.1.le
    rw [hz i hi] at hid
    simp only [Nat.cast_zero,add_zero] at hid
    have hb := ((entry_interval _ _ _).1 (label_entry (reading v k i) (handoffOpening v k P j))).2
    simpa only [hid] using hb
  · intro hu i hi
    have hb := ((entry_interval _ _ _).1 (label_entry (reading v k i) P)).1
    have hinc := mul_le_mul_of_nonneg_left ht.1.le (show 0≤reading v k i from abs_nonneg _)
    have hw := (entry_interval (reading v k i) (handoffOpening v k P j) (label (reading v k i*P))).2
      ⟨lt_of_lt_of_le hb hinc,hu i hi⟩
    have hl := (entry_iff_label _ _ _).1 hw
    simp only [advance,hl,sub_self,Int.toNat_zero]

theorem sharp_iff_noReturn {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (j c : Fin 8) (he : HandoffEntry v k Q P j) (hc : FirstClosing v k P c) :
    SharpEntrySecond v k P j c ↔ NoReturnSecond v k P j := by
  have hjk := he.2.2.1.1
  have hd : 0<reading v k j := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨j,hjk,rfl⟩)
  have hcp : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc.1,rfl⟩)
  have hid := handoff_identity hv k j P hjk
  have heq := Fresh.NativeFirstClosing.deficit_iff_upper (reading v k j) (reading v k c)
    P (handoffOpening v k P j) (label (reading v k j*P)) (label (reading v k c*P)) hd hid
  rw [noReturn_iff_original_upper hv k Q P j he]
  constructor
  · intro hs i hi
    exact Fresh.NativeFirstClosing.propagate_upper _ _ _ _ _ (abs_nonneg _) hcp (heq.1 hs.2) (hc.2 i hi)
  · intro hu
    exact ⟨hc,heq.2 (hu c hc.1)⟩

theorem noReturn_exists_sharp {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (j : Fin 8) (he : HandoffEntry v k Q P j) (hz : NoReturnSecond v k P j) :
    ∃ c : Fin 8, SharpEntrySecond v k P j c := by
  obtain ⟨c,hc,hfirst⟩ := Fresh.NativeFirstClosing.exists_first_closing hv k (fun i=>label (reading v k i*P))
  exact ⟨c,(sharp_iff_noReturn hv k Q P j c he ⟨hc,hfirst⟩).2 hz⟩

theorem sharp_into_noReturn {v : Fin 8 → ℝ} {k : Fin 8} (h : HandoffSharpClass v k) : HandoffNoReturnClass v k := by
  obtain ⟨hv,Q,P,j,c,he,hs⟩ := h
  exact ⟨hv,Q,P,j,he,(sharp_iff_noReturn hv k Q P j c he hs.1).1 hs⟩

theorem noReturn_into_sharp {v : Fin 8 → ℝ} {k : Fin 8} (h : HandoffNoReturnClass v k) : HandoffSharpClass v k := by
  obtain ⟨hv,Q,P,j,he,hz⟩ := h
  obtain ⟨c,hc⟩ := noReturn_exists_sharp hv k Q P j he hz
  exact ⟨hv,Q,P,j,c,he,hc⟩

theorem quarter_into_sharp {v : Fin 8 → ℝ} {k : Fin 8} (h : HandoffQuarterClass v k) : HandoffSharpClass v k := by
  obtain ⟨hv,Q,P,j,c,he,hb⟩ := h
  have hcap := capture_at_label (reading v k j) P ((survivor_iff hv k Q P he.2.1 j).1 he.2.2.1).2
  exact ⟨hv,Q,P,j,c,he,⟨hb.1,hb.2.1⟩,
    Fresh.NativeFirstClosing.quarter_implies_deficit _ _ P _ _ (abs_nonneg _) hcap.1 hb.2.2⟩

theorem sole_sharp_into_handoff {v : Fin 8 → ℝ} {k : Fin 8} (h : SoleSharpClass v k) : HandoffSharpClass v k := by
  obtain ⟨hv,Q,P,j,c,hQ,hm,hj,hsole,hb⟩ := h
  exact ⟨hv,Q,P,j,c,⟨hQ,hm,hj,sole_survivor_order k Q P j hsole⟩,hb⟩

theorem sharp_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : HandoffSharpClass v k) : Isolation v k :=
  handoff_noReturn_isolation (sharp_into_noReturn h)

theorem noReturn_iff_closer_zero {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (j c : Fin 8) (he : HandoffEntry v k Q P j) (hc : FirstClosing v k P c) :
    NoReturnSecond v k P j ↔ advance (reading v k c) P (handoffOpening v k P j)=0 := by
  constructor
  · intro hz
    exact hz c hc.1
  · intro hz
    have ht := forced_handoff hv k Q P he.2.1 j he.2.2.1 he.2.2.2
    have hid := advance_identity (reading v k c) P (handoffOpening v k P j) (abs_nonneg _) ht.1.le
    rw [hz] at hid
    simp only [Nat.cast_zero,add_zero] at hid
    have hb := ((entry_interval _ _ _).1 (label_entry (reading v k c) (handoffOpening v k P j))).2
    have hu : reading v k c*handoffOpening v k P j ≤ (label (reading v k c*P) : ℝ)+7/8 := by
      simpa only [hid] using hb
    apply (noReturn_iff_original_upper hv k Q P j he).2
    intro i hi
    have hcp : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc.1,rfl⟩)
    exact Fresh.NativeFirstClosing.propagate_upper _ _ _ _ _ (abs_nonneg _) hcp hu (hc.2 i hi)

theorem failed_sharp_forces_closer_return {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (j c : Fin 8) (he : HandoffEntry v k Q P j) (hc : FirstClosing v k P c)
    (hfail : ¬ SharpEntrySecond v k P j c) :
    0<advance (reading v k c) P (handoffOpening v k P j) := by
  have hn : ¬ NoReturnSecond v k P j := fun hz=>hfail ((sharp_iff_noReturn hv k Q P j c he hc).2 hz)
  have hz : advance (reading v k c) P (handoffOpening v k P j)≠0 :=
    fun hz=>hn ((noReturn_iff_closer_zero hv k Q P j c he hc).2 hz)
  omega

#print axioms noReturn_iff_closer_zero
#print axioms failed_sharp_forces_closer_return
#print axioms noReturn_iff_original_upper
#print axioms sharp_iff_noReturn
#print axioms noReturn_exists_sharp
#print axioms sharp_into_noReturn
#print axioms noReturn_into_sharp
#print axioms quarter_into_sharp
#print axioms sole_sharp_into_handoff
#print axioms sharp_isolation
end Fresh.NativeHandoffEntryFaces
