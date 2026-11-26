import Fresh.NativeHandoffEntryFaces

/-! Positive advances at chronological given states form an initial segment
of the original closing-boundary order. Equal closing boundaries return
simultaneously; independent advance magnitudes remain unbounded. -/
namespace Fresh.NativeReturnClosingOrder
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement Fresh.NativeHandoffEntryFaces

noncomputable def closing (s P : ℝ) : ℝ := ((label (s*P) : ℝ)+7/8)/s

theorem zero_iff_original_upper (s P R : ℝ) (hs : 0 ≤ s) (hPR : P ≤ R) :
    advance s P R=0 ↔ s*R ≤ (label (s*P) : ℝ)+7/8 := by
  constructor
  · intro hz
    have hid := advance_identity s P R hs hPR
    rw [hz] at hid
    simp only [Nat.cast_zero,add_zero] at hid
    have hb := ((entry_interval _ _ _).1 (label_entry s R)).2
    simpa only [hid] using hb
  · intro hu
    have hb := ((entry_interval _ _ _).1 (label_entry s P)).1
    have hinc := mul_le_mul_of_nonneg_left hPR hs
    have hw := (entry_interval s R (label (s*P))).2 ⟨lt_of_lt_of_le hb hinc,hu⟩
    have hl := (entry_iff_label _ _ _).1 hw
    simp only [advance,hl,sub_self,Int.toNat_zero]

theorem positive_iff_original_upper_crossed (s P R : ℝ) (hs : 0 ≤ s) (hPR : P ≤ R) :
    0 < advance s P R ↔ (label (s*P) : ℝ)+7/8<s*R := by
  have hz := zero_iff_original_upper s P R hs hPR
  constructor
  · intro ha
    by_contra hn
    have he := hz.2 (le_of_not_gt hn)
    omega
  · intro hcross
    have hn : advance s P R ≠ 0 := fun he=>not_lt_of_ge (hz.1 he) hcross
    omega

theorem positive_iff_closing_passed (s P R : ℝ) (hs : 0 < s) (hPR : P ≤ R) :
    0 < advance s P R ↔ closing s P<R := by
  rw [positive_iff_original_upper_crossed s P R hs.le hPR]
  simpa only [closing,mul_comm] using (div_lt_iff₀ hs : ((label (s*P) : ℝ)+7/8)/s<R ↔ (label (s*P) : ℝ)+7/8<R*s).symm

theorem earlier_closing_returns (s t P R : ℝ) (hs : 0 < s) (ht : 0 < t) (hPR : P ≤ R)
    (horder : closing s P ≤ closing t P) (hreturn : 0 < advance t P R) : 0 < advance s P R := by
  apply (positive_iff_closing_passed s P R hs hPR).2
  exact lt_of_le_of_lt horder ((positive_iff_closing_passed t P R ht hPR).1 hreturn)

theorem tied_closings_return_together (s t P R : ℝ) (hs : 0 < s) (ht : 0 < t) (hPR : P ≤ R)
    (htie : closing s P=closing t P) : 0 < advance s P R ↔ 0 < advance t P R := by
  rw [positive_iff_closing_passed s P R hs hPR,positive_iff_closing_passed t P R ht hPR,htie]

theorem returned_before_nonreturner (s t P R : ℝ) (hs : 0 < s) (ht : 0 < t) (hPR : P ≤ R)
    (ha : 0 < advance s P R) (hz : advance t P R=0) : closing s P< closing t P := by
  have hleft := (positive_iff_closing_passed s P R hs hPR).1 ha
  have hright : R ≤ closing t P := by
    apply (le_div_iff₀ ht).2
    have hh := (zero_iff_original_upper t P R ht.le hPR).1 hz
    nlinarith only [hh]
  exact lt_of_lt_of_le hleft hright

theorem handoff_returner_before_setter {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (j : Fin 8) (he : HandoffEntry v k Q P j) (i : Fin 8) (hi : i ≠ k)
    (ha : 0 < advance (reading v k i) P (handoffOpening v k P j)) :
    closing (reading v k i) P< closing (reading v k j) P := by
  have ht := forced_handoff hv k Q P he.2.1 j he.2.2.1 he.2.2.2
  have hiPos : 0 < reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  have hjPos : 0 < reading v k j := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨j,he.2.2.1.1,rfl⟩)
  exact returned_before_nonreturner _ _ P _ hiPos hjPos ht.1.le ha
    (handoff_selected_zero hv k Q P he.2.1 j he.2.2.1)

theorem setter_first_closing_noReturn {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Q P : ℝ)
    (j : Fin 8) (he : HandoffEntry v k Q P j) (hc : FirstClosing v k P j) : NoReturnSecond v k P j :=
  (noReturn_iff_closer_zero hv k Q P j j he hc).2
    (handoff_selected_zero hv k Q P he.2.1 j he.2.2.1)

-- STANDING: DEFINITION
noncomputable def SelfClosingClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (Q P : ℝ) (j : Fin 8), HandoffEntry v k Q P j ∧ FirstClosing v k P j

-- STANDING: DEFINITION
noncomputable def SoleSelfClosingClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (Q P : ℝ) (j : Fin 8), 0 < Q ∧ IsMove (disparitySet v k) Q P ∧
    Survivor v k Q P j ∧ (∀ i : Fin 8, Survivor v k Q P i → i=j) ∧ FirstClosing v k P j

theorem selfClosing_into_noReturn {v : Fin 8 → ℝ} {k : Fin 8} (h : SelfClosingClass v k) : HandoffNoReturnClass v k := by
  obtain ⟨hv,Q,P,j,he,hc⟩ := h
  exact ⟨hv,Q,P,j,he,setter_first_closing_noReturn hv k Q P j he hc⟩

theorem soleSelfClosing_into_selfClosing {v : Fin 8 → ℝ} {k : Fin 8} (h : SoleSelfClosingClass v k) : SelfClosingClass v k := by
  obtain ⟨hv,Q,P,j,hQ,hm,hj,hsole,hc⟩ := h
  exact ⟨hv,Q,P,j,⟨hQ,hm,hj,sole_survivor_order k Q P j hsole⟩,hc⟩

theorem selfClosing_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : SelfClosingClass v k) : Isolation v k :=
  handoff_noReturn_isolation (selfClosing_into_noReturn h)

#print axioms zero_iff_original_upper
#print axioms positive_iff_original_upper_crossed
#print axioms positive_iff_closing_passed
#print axioms earlier_closing_returns
#print axioms tied_closings_return_together
#print axioms returned_before_nonreturner
#print axioms handoff_returner_before_setter
#print axioms setter_first_closing_noReturn
#print axioms selfClosing_into_noReturn
#print axioms soleSelfClosing_into_selfClosing
#print axioms selfClosing_isolation
end Fresh.NativeReturnClosingOrder
