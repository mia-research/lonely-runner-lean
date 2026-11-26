import Fresh.NativeRepeatedReturnArrangement

/-! Joint native capture labels constrain repeated returns in addition to
the disparity ratio. All labels and return levels remain unbounded. -/
namespace Fresh.NativeRepeatedReturnLabels
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement Fresh.NativeReturnClosingOrder
  Fresh.NativeRepeatedReturn

theorem returned_label_positive (s P R : ℝ) (hs : 0 ≤ s) (hP : 0 ≤ P) (hPR : P ≤ R)
    (ha : 0 < advance s P R) : 1 ≤ label (s*R) := by
  have hz : label 0=0 := by norm_num [label]
  have hnonneg : 0 ≤ label (s*P) := by
    have hh := label_monotone (mul_nonneg hs hP)
    simpa only [hz] using hh
  have hid := advance_identity s P R hs hPR
  have hapos : (0 : ℤ)<(advance s P R : ℤ) := by exact_mod_cast ha
  omega

theorem captured_repeat_label_ladder {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hP : 0 ≤ P) (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (i : Fin 8) (hi : i≠k) (hcap : InWay (reading v k i) R)
    (m : ℕ) (hmp : 1 ≤ m) (ha : m ≤ advance (reading v k i) R (handoffOpening v k R c)) :
    (8*(m : ℤ)-2)*label (reading v k c*R)-(m : ℤ)<2*label (reading v k i*R) := by
  have hPR := le_of_isMove (disparitySet_pos hv k) hm
  have hN := returned_label_positive (reading v k c) P R (abs_nonneg _) hP hPR hc.2.1
  have hNR : (1 : ℝ) ≤ (label (reading v k c*R) : ℝ) := by exact_mod_cast hN
  have ht := forced_handoff hv k P R hm c hc ho
  have hcapc := capture_at_label (reading v k c) R ((survivor_iff hv k P R hm c).1 hc).2
  have hcapi := capture_at_label (reading v k i) R hcap
  have hlevel := (advance_ge_iff_level (reading v k i) R _ (show 0 ≤ reading v k i from abs_nonneg _) ht.1.le m hmp).1 ha
  have hopen := handoff_identity hv k c R hc.1
  have hip : 0 < reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  have hR : 0<R := by
    have hdpos : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc.1,rfl⟩)
    nlinarith only [hcapc.1,hNR,hdpos]
  have hiT : 0<reading v k i*handoffOpening v k R c := mul_pos hip (lt_trans hR ht.1)
  have hdT : 0<reading v k c*handoffOpening v k R c := by rw [hopen]; linarith only [hNR]
  have hlow : 0<(label (reading v k c*R) : ℝ)-1/8 := by linarith only [hNR]
  have hphase : reading v k i*handoffOpening v k R c*((label (reading v k c*R) : ℝ)-1/8)<
      ((label (reading v k i*R) : ℝ)+1/8)*((label (reading v k c*R) : ℝ)+1/8) := by
    calc
      _ < reading v k i*handoffOpening v k R c*(reading v k c*R) := mul_lt_mul_of_pos_left hcapc.1 hiT
      _ = (reading v k i*R)*(reading v k c*handoffOpening v k R c) := by ring
      _ < ((label (reading v k i*R) : ℝ)+1/8)*(reading v k c*handoffOpening v k R c) := mul_lt_mul_of_pos_right hcapi.2 hdT
      _ = _ := by rw [hopen]
  have hscaled := mul_lt_mul_of_pos_right hlevel hlow
  have hreal : (8*(m : ℝ)-2)*(label (reading v k c*R) : ℝ)-(m : ℝ)<2*(label (reading v k i*R) : ℝ) := by
    nlinarith only [hscaled,hphase]
  exact_mod_cast hreal

theorem captured_repeat_label_triple {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hP : 0 ≤ P) (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (i : Fin 8) (hi : i≠k) (hcap : InWay (reading v k i) R)
    (ha : 0 < advance (reading v k i) R (handoffOpening v k R c)) :
    3*label (reading v k c*R) ≤ label (reading v k i*R) := by
  have hh := captured_repeat_label_ladder hv k P R hP hm c hc ho i hi hcap 1 (by omega) (by omega)
  norm_num only [Nat.cast_one] at hh
  omega

theorem captured_repeat_label_seven {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hP : 0 ≤ P) (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (i : Fin 8) (hi : i≠k) (hcap : InWay (reading v k i) R)
    (ha : 2 ≤ advance (reading v k i) R (handoffOpening v k R c)) :
    7*label (reading v k c*R) ≤ label (reading v k i*R) := by
  have hh := captured_repeat_label_ladder hv k P R hP hm c hc ho i hi hcap 2 (by omega) ha
  norm_num only [Nat.cast_ofNat] at hh
  omega

theorem carried_repeat_label_ladder {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hP : 0 ≤ P) (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (i : Fin 8) (hi : i≠k)
    (m : ℕ) (hmp : 1 ≤ m) (ha : m ≤ advance (reading v k i) R (handoffOpening v k R c)) :
    32*((m : ℤ)-1)*label (reading v k c*R)-4*(m : ℤ)-3<8*label (reading v k i*R) := by
  have hPR := le_of_isMove (disparitySet_pos hv k) hm
  have hN := returned_label_positive (reading v k c) P R (abs_nonneg _) hP hPR hc.2.1
  have hNR : (1 : ℝ) ≤ (label (reading v k c*R) : ℝ) := by exact_mod_cast hN
  have ht := forced_handoff hv k P R hm c hc ho
  have hcapc := capture_at_label (reading v k c) R ((survivor_iff hv k P R hm c).1 hc).2
  have hiupper := ((entry_interval _ _ _).1 (label_entry (reading v k i) R)).2
  have hlevel := (advance_ge_iff_level (reading v k i) R _ (show 0 ≤ reading v k i from abs_nonneg _) ht.1.le m hmp).1 ha
  have hopen := handoff_identity hv k c R hc.1
  have hip : 0 < reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  have hR : 0<R := lt_of_le_of_lt hP (predecessor_strict hv k P R hm c hc)
  have hiT : 0<reading v k i*handoffOpening v k R c := mul_pos hip (lt_trans hR ht.1)
  have hdT : 0<reading v k c*handoffOpening v k R c := by rw [hopen]; linarith only [hNR]
  have hlow : 0<(label (reading v k c*R) : ℝ)-1/8 := by linarith only [hNR]
  have hphase : reading v k i*handoffOpening v k R c*((label (reading v k c*R) : ℝ)-1/8)<
      ((label (reading v k i*R) : ℝ)+7/8)*((label (reading v k c*R) : ℝ)+1/8) := by
    calc
      _ < reading v k i*handoffOpening v k R c*(reading v k c*R) := mul_lt_mul_of_pos_left hcapc.1 hiT
      _ = (reading v k i*R)*(reading v k c*handoffOpening v k R c) := by ring
      _ ≤ ((label (reading v k i*R) : ℝ)+7/8)*(reading v k c*handoffOpening v k R c) := mul_le_mul_of_nonneg_right hiupper hdT.le
      _ = _ := by rw [hopen]
  have hscaled := mul_lt_mul_of_pos_right hlevel hlow
  have hreal : 32*((m : ℝ)-1)*(label (reading v k c*R) : ℝ)-4*(m : ℝ)-3<8*(label (reading v k i*R) : ℝ) := by
    nlinarith only [hscaled,hphase]
  exact_mod_cast hreal

theorem carried_repeat_label_four {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hP : 0 ≤ P) (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (i : Fin 8) (hi : i≠k)
    (ha : 2 ≤ advance (reading v k i) R (handoffOpening v k R c)) :
    4*label (reading v k c*R)-1 ≤ label (reading v k i*R) := by
  have hh := carried_repeat_label_ladder hv k P R hP hm c hc ho i hi 2 (by omega) ha
  norm_num only [Nat.cast_ofNat] at hh
  omega

#print axioms carried_repeat_label_ladder
#print axioms carried_repeat_label_four
#print axioms returned_label_positive
#print axioms captured_repeat_label_ladder
#print axioms captured_repeat_label_triple
#print axioms captured_repeat_label_seven
end Fresh.NativeRepeatedReturnLabels
