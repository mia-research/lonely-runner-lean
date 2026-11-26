import Fresh.NativeReturnGroupFaces

/-! Repeated native returns have exact unbounded level-crossing laws.
The captured branch's ratio ladder comes from the selected capture width;
it is not a global bound on moves, times or independent return indices. -/
namespace Fresh.NativeRepeatedReturn
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement Fresh.NativeReturnClosingOrder
  Fresh.NativeReturnGroupFaces

theorem advance_ge_iff_level (s R T : ℝ) (hs : 0 ≤ s) (hRT : R ≤ T) (m : ℕ) (hm : 1 ≤ m) :
    m ≤ advance s R T ↔ (label (s*R) : ℝ)+(m : ℝ)-1/8<s*T := by
  have hid : (label (s*T) : ℝ)=(label (s*R) : ℝ)+(advance s R T : ℝ) := by
    exact_mod_cast advance_identity s R T hs hRT
  have he := (entry_interval s T _).1 (label_entry s T)
  constructor
  · intro ha
    have hac : (m : ℝ) ≤ (advance s R T : ℝ) := by exact_mod_cast ha
    linarith only [hid,he.1,hac]
  · intro hcross
    by_contra hn
    have hle : advance s R T+1 ≤ m := by omega
    have hlec : (advance s R T : ℝ)+1 ≤ (m : ℝ) := by exact_mod_cast hle
    linarith only [hid,he.2,hlec,hcross]

theorem advance_ge_iff_remaining (s R T : ℝ) (hs : 0 ≤ s) (hRT : R ≤ T) (m : ℕ) (hm : 1 ≤ m) :
    m ≤ advance s R T ↔
      (label (s*R) : ℝ)+7/8-s*R+(m : ℝ)-1<s*(T-R) := by
  rw [advance_ge_iff_level s R T hs hRT m hm]
  constructor <;> intro h <;> nlinarith only [h]

theorem handoff_level_iff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (i : Fin 8) (hi : i≠k) (m : ℕ) (hmp : 1 ≤ m) :
    m ≤ advance (reading v k i) R (handoffOpening v k R c) ↔
      reading v k c*((label (reading v k i*R) : ℝ)+7/8-reading v k i*R+(m : ℝ)-1)<
        reading v k i*((label (reading v k c*R) : ℝ)+1/8-reading v k c*R) := by
  have ht := forced_handoff hv k P R hm c hc ho
  have hd : 0 < reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc.1,rfl⟩)
  have hid := handoff_identity hv k c R hc.1
  rw [advance_ge_iff_remaining (reading v k i) R (handoffOpening v k R c) (show 0 ≤ reading v k i from abs_nonneg _) ht.1.le m hmp]
  have hdisp : reading v k c*(reading v k i*(handoffOpening v k R c-R))=
      reading v k i*((label (reading v k c*R) : ℝ)+1/8-reading v k c*R) := by
    calc
      _ = reading v k i*(reading v k c*handoffOpening v k R c-reading v k c*R) := by ring
      _ = _ := by rw [hid]
  rw [←hdisp]
  exact (mul_lt_mul_iff_right₀ hd).symm

theorem captured_return_ratio {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (i : Fin 8) (hi : i≠k) (hcap : InWay (reading v k i) R)
    (m : ℕ) (hmp : 1 ≤ m) (ha : m ≤ advance (reading v k i) R (handoffOpening v k R c)) :
    (4*(m : ℝ)-1)*reading v k c<reading v k i := by
  have hface := (handoff_level_iff hv k P R hm c hc ho i hi m hmp).1 ha
  have hci := capture_at_label (reading v k i) R hcap
  have hcc := capture_at_label (reading v k c) R ((survivor_iff hv k P R hm c).1 hc).2
  have hip : 0 < reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  have hcp : 0 < reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc.1,rfl⟩)
  have hleft := mul_lt_mul_of_pos_left hci.2 hcp
  have hright := mul_lt_mul_of_pos_left hcc.1 hip
  nlinarith only [hface,hleft,hright]

theorem captured_repeat_fast {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (i : Fin 8) (hi : i≠k) (hcap : InWay (reading v k i) R)
    (ha : 0 < advance (reading v k i) R (handoffOpening v k R c)) :
    3*reading v k c<reading v k i := by
  have hh := captured_return_ratio hv k P R hm c hc ho i hi hcap 1 (by omega) (by omega)
  norm_num only [Nat.cast_one] at hh
  linarith only [hh]

theorem captured_repeat_one_if_le_seven {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (i : Fin 8) (hi : i≠k) (hcap : InWay (reading v k i) R)
    (ha : 0 < advance (reading v k i) R (handoffOpening v k R c))
    (hratio : reading v k i ≤ 7*reading v k c) : advance (reading v k i) R (handoffOpening v k R c)=1 := by
  by_contra hn
  have htwo : 2 ≤ advance (reading v k i) R (handoffOpening v k R c) := by omega
  have hh := captured_return_ratio hv k P R hm c hc ho i hi hcap 2 (by omega) htwo
  norm_num only [Nat.cast_ofNat] at hh
  linarith only [hh,hratio]

theorem failed_group_first_returns {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c g : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (hg : GroupFirst v k P R g) (hfail : ¬SharpGroup v k P R c g) :
    0 < advance (reading v k g) R (handoffOpening v k R c) := by
  have ht := forced_handoff hv k P R hm c hc ho
  have hd : 0 < reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc.1,rfl⟩)
  have heq := Fresh.NativeFirstClosing.deficit_iff_upper (reading v k c) (reading v k g) R _
    (label (reading v k c*R)) (label (reading v k g*R)) hd (handoff_identity hv k c R hc.1)
  by_contra hn
  have hz : advance (reading v k g) R (handoffOpening v k R c)=0 := by omega
  have hu := (zero_iff_original_upper (reading v k g) R _ (abs_nonneg _) ht.1.le).1 hz
  exact hfail ⟨hg,heq.2 hu⟩

theorem failed_group_split {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c g : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (hg : GroupFirst v k P R g) (hfail : ¬SharpGroup v k P R c g) :
    (InWay (reading v k g) R ∧ 3*reading v k c<reading v k g) ∨
      ((label (reading v k g*R) : ℝ)+1/8 ≤ reading v k g*R ∧
        reading v k g*R ≤ (label (reading v k g*R) : ℝ)+7/8 ∧
        0 < advance (reading v k g) P R ∧ 0 < advance (reading v k g) R (handoffOpening v k R c)) := by
  have ha := failed_group_first_returns hv k P R hm c g hc ho hg hfail
  by_cases hcap : InWay (reading v k g) R
  · exact Or.inl ⟨hcap,captured_repeat_fast hv k P R hm c hc ho g hg.1 hcap ha⟩
  · have hlo : (label (reading v k g*R) : ℝ)+1/8 ≤ reading v k g*R :=
      le_of_not_gt (fun hh=>hcap ((inWay_iff_lower_not_passed _ _).2 hh))
    have hhi := ((entry_interval _ _ _).1 (label_entry (reading v k g) R)).2
    exact Or.inr ⟨hlo,hhi,hg.2.1,ha⟩

theorem recovered_remaining_gap (s R : ℝ) (hclear : ¬InWay s R) :
    0 ≤ (label (s*R) : ℝ)+7/8-s*R ∧ (label (s*R) : ℝ)+7/8-s*R ≤ 3/4 := by
  have hupper := ((entry_interval _ _ _).1 (label_entry s R)).2
  have hlower : (label (s*R) : ℝ)+1/8 ≤ s*R :=
    le_of_not_gt (fun hh=>hclear ((inWay_iff_lower_not_passed _ _).2 hh))
  constructor <;> linarith only [hupper,hlower]

theorem repeated_first_level_iff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (i : Fin 8) (hi : i≠k) :
    0 < advance (reading v k i) R (handoffOpening v k R c) ↔
      reading v k c*((label (reading v k i*R) : ℝ)+7/8-reading v k i*R)<
        reading v k i*((label (reading v k c*R) : ℝ)+1/8-reading v k c*R) := by
  have hh := handoff_level_iff hv k P R hm c hc ho i hi 1 (by omega)
  norm_num only [Nat.cast_one,add_sub_cancel_right] at hh
  constructor
  · intro ha
    exact hh.1 (by omega)
  · intro ha
    have hh' := hh.2 ha
    omega

theorem carried_return_ratio {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (i : Fin 8) (hi : i≠k)
    (m : ℕ) (hmp : 1 ≤ m) (ha : m ≤ advance (reading v k i) R (handoffOpening v k R c)) :
    4*((m : ℝ)-1)*reading v k c<reading v k i := by
  have hface := (handoff_level_iff hv k P R hm c hc ho i hi m hmp).1 ha
  have hiupper := ((entry_interval _ _ _).1 (label_entry (reading v k i) R)).2
  have hcc := capture_at_label (reading v k c) R ((survivor_iff hv k P R hm c).1 hc).2
  have hip : 0 < reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  have hcp : 0 ≤ reading v k c := abs_nonneg _
  have hleft := mul_le_mul_of_nonneg_left hiupper hcp
  have hright := mul_lt_mul_of_pos_left hcc.1 hip
  nlinarith only [hface,hleft,hright]

#print axioms carried_return_ratio
#print axioms recovered_remaining_gap
#print axioms repeated_first_level_iff
#print axioms advance_ge_iff_level
#print axioms advance_ge_iff_remaining
#print axioms handoff_level_iff
#print axioms captured_return_ratio
#print axioms captured_repeat_fast
#print axioms captured_repeat_one_if_le_seven
#print axioms failed_group_first_returns
#print axioms failed_group_split
end Fresh.NativeRepeatedReturn
