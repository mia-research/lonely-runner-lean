import Fresh.NativeReturnExcursion

/-! Independent entry excursion bands allow many returned disparities to
recover while one disparity remains captured. That survivor forces a new
handoff; native retained faces can then join the prior relative family. -/
namespace Fresh.NativeExcursionArrangement
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement Fresh.NativeReturnClosingOrder
  Fresh.NativeReturnExcursion

noncomputable def Bands (v : Fin 8 → ℝ) (k : Fin 8) (R : ℝ) (c : Fin 8) (A : Fin 8 → ℕ) : Prop :=
  ∀ i : Fin 8, i≠k →
    reading v k c*((A i : ℝ)-1)<excursion (reading v k c) (reading v k i) R
      (label (reading v k c*R)) (label (reading v k i*R)) ∧
    excursion (reading v k c) (reading v k i) R (label (reading v k c*R)) (label (reading v k i*R)) ≤ reading v k c*(A i : ℝ)

noncomputable def RecoveredBand (v : Fin 8 → ℝ) (k : Fin 8) (R : ℝ) (c : Fin 8) (A : Fin 8 → ℕ) (i : Fin 8) : Prop :=
  reading v k c*((A i : ℝ)-3/4) ≤ excursion (reading v k c) (reading v k i) R
    (label (reading v k c*R)) (label (reading v k i*R))

noncomputable def SurvivingGroup (v : Fin 8 → ℝ) (k : Fin 8) (R : ℝ) (c g : Fin 8) (A : Fin 8 → ℕ) : Prop :=
  g≠k ∧ excursion (reading v k c) (reading v k g) R (label (reading v k c*R)) (label (reading v k g*R))<
    reading v k c*((A g : ℝ)-3/4) ∧
    ∀ i : Fin 8, i≠k → reading v k i≠reading v k g → RecoveredBand v k R c A i

noncomputable def RetainedFaces (v : Fin 8 → ℝ) (k : Fin 8) (R : ℝ) (c g : Fin 8) (A : Fin 8 → ℕ) : Prop :=
  ∀ i : Fin 8, i≠k → reading v k i≠reading v k g →
    reading v k i/4 ≤ reading v k g*((label (reading v k i*R) : ℝ)+(A i : ℝ)+7/8-reading v k i*handoffOpening v k R c)

theorem bands_force_advances {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (A : Fin 8 → ℕ) (hb : Bands v k R c A) :
    ∀ i : Fin 8, i≠k → advance (reading v k i) R (handoffOpening v k R c)=A i := by
  have ht := forced_handoff hv k P R hm c hc ho
  have hd : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc.1,rfl⟩)
  intro i hi
  exact (advance_exact_iff _ _ R _ _ (A i) hd (abs_nonneg _) ht.1.le (handoff_identity hv k c R hc.1)).2 (hb i hi)

theorem recovered_iff_clear {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (A : Fin 8 → ℕ) (hb : Bands v k R c A) (i : Fin 8) (hi : i≠k) :
    RecoveredBand v k R c A i ↔ ¬InWay (reading v k i) (handoffOpening v k R c) := by
  have ht := forced_handoff hv k P R hm c hc ho
  have hd : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc.1,rfl⟩)
  have ha := bands_force_advances hv k P R hm c hc ho A hb i hi
  have hh := clear_iff_excursion _ _ R _ _ (A i) hd (abs_nonneg _) ht.1.le (handoff_identity hv k c R hc.1) ha
  exact ⟨fun h=>not_lt.mpr (hh.2 h),fun h=>hh.1 (not_lt.mp h)⟩

theorem group_survivors {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c g : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (A : Fin 8 → ℕ) (hb : Bands v k R c A)
    (hg : SurvivingGroup v k R c g A) (i : Fin 8) :
    Survivor v k R (handoffOpening v k R c) i ↔ i≠k ∧ reading v k i=reading v k g := by
  have ht := forced_handoff hv k P R hm c hc ho
  have hd : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc.1,rfl⟩)
  have hag := bands_force_advances hv k P R hm c hc ho A hb g hg.1
  have hcapg := (capture_iff_excursion _ _ R _ _ (A g) hd (abs_nonneg _) ht.1.le (handoff_identity hv k c R hc.1) hag).2 hg.2.1
  constructor
  · intro hs
    refine ⟨hs.1,?_⟩
    by_contra hn
    have hclear := (recovered_iff_clear hv k P R hm c hc ho A hb i hs.1).1 (hg.2.2 i hs.1 hn)
    exact hclear ((survivor_iff hv k R _ ht.2 i).1 hs).2
  · intro hi
    exact (survivor_iff hv k R _ ht.2 i).2 ⟨hi.1,by simpa only [hi.2] using hcapg⟩

theorem group_forces_move {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c g : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (A : Fin 8 → ℕ) (hb : Bands v k R c A)
    (hg : SurvivingGroup v k R c g A) :
    handoffOpening v k R c<handoffOpening v k (handoffOpening v k R c) g ∧
      IsMove (disparitySet v k) (handoffOpening v k R c) (handoffOpening v k (handoffOpening v k R c) g) := by
  have ht := forced_handoff hv k P R hm c hc ho
  have hsur := (group_survivors hv k P R hm c g hc ho A hb hg g).2 ⟨hg.1,rfl⟩
  exact equal_readings_handoff hv k R _ ht.2 g hsur
    (fun i hi=>(group_survivors hv k P R hm c g hc ho A hb hg i).1 hi |>.2)

theorem retained_into_relative {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c g : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (A : Fin 8 → ℕ) (hb : Bands v k R c A)
    (hg : SurvivingGroup v k R c g A) (hf : RetainedFaces v k R c g A) :
    RelativeEntrySecond v k R (handoffOpening v k R c) g := by
  have ht := forced_handoff hv k P R hm c hc ho
  intro i hi hig
  constructor
  · intro hs
    have heq := ((group_survivors hv k P R hm c g hc ho A hb hg i).1 hs).2
    rw [heq]
    have hp : 0 ≤ reading v k g := abs_nonneg _
    linarith only [hp]
  · intro hn
    have hneq : reading v k i≠reading v k g := fun heq=>hn ((group_survivors hv k P R hm c g hc ho A hb hg i).2 ⟨hi,heq⟩)
    have ha := bands_force_advances hv k P R hm c hc ho A hb i hi
    have hid := advance_identity (reading v k i) R (handoffOpening v k R c) (abs_nonneg _) ht.1.le
    rw [ha] at hid
    have hidR : (label (reading v k i*handoffOpening v k R c) : ℝ)=
      (label (reading v k i*R) : ℝ)+(A i : ℝ) := by exact_mod_cast hid
    rw [hidR]
    exact hf i hi hneq

-- STANDING: DEFINITION
noncomputable def RecoveryClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (P R : ℝ) (c : Fin 8) (A : Fin 8 → ℕ),
    0<P ∧ IsMove (disparitySet v k) P R ∧ Survivor v k P R c ∧ OpeningOrder v k P R c ∧
      Bands v k R c A ∧ ∀ i : Fin 8, i≠k → RecoveredBand v k R c A i

-- STANDING: DEFINITION
noncomputable def RelayClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (P R : ℝ) (c g : Fin 8) (A : Fin 8 → ℕ),
    0<P ∧ IsMove (disparitySet v k) P R ∧ Survivor v k P R c ∧ OpeningOrder v k P R c ∧
      Bands v k R c A ∧ SurvivingGroup v k R c g A ∧ RetainedFaces v k R c g A

theorem recovery_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : RecoveryClass v k) : Isolation v k := by
  obtain ⟨hv,P,R,c,A,hP,hm,hc,ho,hb,hr⟩ := h
  have ht := forced_handoff hv k P R hm c hc ho
  refine ⟨handoffOpening v k R c,lt_trans (lt_of_lt_of_le hP (le_of_isMove (disparitySet_pos hv k) hm)) ht.1,?_⟩
  intro i hi
  rw [←Fresh.Localisation.distInt_abs_mul]
  exact not_lt.mp ((recovered_iff_clear hv k P R hm c hc ho A hb i hi).1 (hr i hi))

theorem relay_into_relative {v : Fin 8 → ℝ} {k : Fin 8} (h : RelayClass v k) : HandoffRelativeClass v k := by
  obtain ⟨hv,P,R,c,g,A,hP,hm,hc,ho,hb,hg,hf⟩ := h
  have ht := forced_handoff hv k P R hm c hc ho
  have hR := lt_of_lt_of_le hP (le_of_isMove (disparitySet_pos hv k) hm)
  have hsur := (group_survivors hv k P R hm c g hc ho A hb hg g).2 ⟨hg.1,rfl⟩
  exact ⟨hv,R,handoffOpening v k R c,g,⟨hR,ht.2,hsur,equal_readings_order k R _ g
    (fun i hi=>((group_survivors hv k P R hm c g hc ho A hb hg i).1 hi).2)⟩,
    retained_into_relative hv k P R hm c g hc ho A hb hg hf⟩

theorem relay_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : RelayClass v k) : Isolation v k :=
  handoff_relative_isolation (relay_into_relative h)

theorem recovery_into_recovered {v : Fin 8 → ℝ} {k : Fin 8} (h : RecoveryClass v k) : HandoffRecoveredClass v k := by
  obtain ⟨hv,P,R,c,A,hP,hm,hc,ho,hb,hr⟩ := h
  refine ⟨hv,P,R,c,⟨hP,hm,hc,ho⟩,?_⟩
  intro i hi ha
  have hclear := (recovered_iff_clear hv k P R hm c hc ho A hb i hi).1 (hr i hi)
  have hpass : (label (reading v k i*handoffOpening v k R c) : ℝ)+1/8 ≤ reading v k i*handoffOpening v k R c :=
    le_of_not_gt (fun hh=>hclear ((inWay_iff_lower_not_passed _ _).2 hh))
  have hmul := mul_le_mul_of_nonneg_left hpass (show 0 ≤ reading v k c from abs_nonneg _)
  have hid := handoff_identity hv k c R hc.1
  have hscaled := congrArg (fun x : ℝ=>reading v k i*x) hid
  nlinarith only [hmul,hscaled]

#print axioms recovery_into_recovered
#print axioms bands_force_advances
#print axioms recovered_iff_clear
#print axioms group_survivors
#print axioms group_forces_move
#print axioms retained_into_relative
#print axioms recovery_isolation
#print axioms relay_into_relative
#print axioms relay_isolation
end Fresh.NativeExcursionArrangement
