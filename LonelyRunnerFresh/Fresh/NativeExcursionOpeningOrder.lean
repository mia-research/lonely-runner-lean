import Fresh.NativeExcursionArrangement

/-! Remaining lower-face displacements order simultaneous captures using
only the previous entry excursion and its independent return levels. -/
namespace Fresh.NativeExcursionOpeningOrder
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement Fresh.NativeReturnClosingOrder
  Fresh.NativeReturnExcursion Fresh.NativeExcursionArrangement

noncomputable def residual (d s R : ℝ) (N K : ℤ) (a : ℕ) : ℝ :=
  d*((a : ℝ)-3/4)-excursion d s R N K

noncomputable def ResidualOrder (v : Fin 8 → ℝ) (k : Fin 8) (R : ℝ) (c g : Fin 8) (A : Fin 8 → ℕ) : Prop :=
  ∀ i : Fin 8, i≠k → residual (reading v k c) (reading v k i) R
      (label (reading v k c*R)) (label (reading v k i*R)) (A i)>0 →
    reading v k g*residual (reading v k c) (reading v k i) R
      (label (reading v k c*R)) (label (reading v k i*R)) (A i) ≤ 
    reading v k i*residual (reading v k c) (reading v k g) R
      (label (reading v k c*R)) (label (reading v k g*R)) (A g)

theorem residual_identity (d s R T : ℝ) (N : ℤ) (a : ℕ) (hs : 0 ≤ s) (hRT : R ≤ T)
    (ho : d*T=(N : ℝ)+1/8) (ha : advance s R T=a) :
    residual d s R N (label (s*R)) a=d*((label (s*T) : ℝ)+1/8-s*T) := by
  have hid := advance_identity s R T hs hRT
  rw [ha] at hid
  have hidR : (label (s*T) : ℝ)=(label (s*R) : ℝ)+(a : ℝ) := by exact_mod_cast hid
  dsimp [residual]
  rw [excursion_identity d s R T N _ ho,hidR]
  ring

theorem residual_positive_iff (d s R T : ℝ) (N : ℤ) (a : ℕ) (hd : 0<d) (hs : 0 ≤ s) (hRT : R ≤ T)
    (ho : d*T=(N : ℝ)+1/8) (ha : advance s R T=a) :
    0<residual d s R N (label (s*R)) a ↔ InWay s T := by
  rw [residual_identity d s R T N a hs hRT ho ha,inWay_iff_lower_not_passed]
  constructor <;> intro hh <;> nlinarith only [hh,hd]

theorem residual_order_iff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c g : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (A : Fin 8 → ℕ) (hb : Bands v k R c A) (hgk : g≠k) :
    ResidualOrder v k R c g A ↔ OpeningOrder v k R (handoffOpening v k R c) g := by
  have ht := forced_handoff hv k P R hm c hc ho
  have hd : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc.1,rfl⟩)
  have hopen := handoff_identity hv k c R hc.1
  have hlabels : ∀ i : Fin 8, i≠k → residual (reading v k c) (reading v k i) R
      (label (reading v k c*R)) (label (reading v k i*R)) (A i)=
      reading v k c*((label (reading v k i*handoffOpening v k R c) : ℝ)+1/8-reading v k i*handoffOpening v k R c) := by
    intro i hi
    exact residual_identity _ _ R _ _ (A i) (abs_nonneg _) ht.1.le hopen
      (bands_force_advances hv k P R hm c hc ho A hb i hi)
  have hgidentity := hlabels g hgk
  constructor
  · intro hr i hi
    have hw := ((survivor_iff hv k R _ ht.2 i).1 hi).2
    have hp := (residual_positive_iff _ _ R _ _ (A i) hd (abs_nonneg _) ht.1.le hopen
      (bands_force_advances hv k P R hm c hc ho A hb i hi.1)).2 hw
    have hh := hr i hi.1 hp
    rw [hlabels i hi.1,hgidentity] at hh
    nlinarith only [hh,hd]
  · intro hr i hi hpos
    have hw := (residual_positive_iff _ _ R _ _ (A i) hd (abs_nonneg _) ht.1.le hopen
      (bands_force_advances hv k P R hm c hc ho A hb i hi)).1 hpos
    have hs := (survivor_iff hv k R _ ht.2 i).2 ⟨hi,hw⟩
    have hh := hr i hs
    rw [hlabels i hi,hgidentity]
    nlinarith only [hh,hd]

theorem residual_forces_handoff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c g : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (A : Fin 8 → ℕ) (hb : Bands v k R c A) (hgk : g≠k)
    (hg : 0<residual (reading v k c) (reading v k g) R (label (reading v k c*R)) (label (reading v k g*R)) (A g))
    (hr : ResidualOrder v k R c g A) :
    handoffOpening v k R c<handoffOpening v k (handoffOpening v k R c) g ∧
      IsMove (disparitySet v k) (handoffOpening v k R c) (handoffOpening v k (handoffOpening v k R c) g) := by
  have ht := forced_handoff hv k P R hm c hc ho
  have hd : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc.1,rfl⟩)
  have ha := bands_force_advances hv k P R hm c hc ho A hb g hgk
  have hw := (residual_positive_iff _ _ R _ _ (A g) hd (abs_nonneg _) ht.1.le (handoff_identity hv k c R hc.1) ha).1 hg
  have hsur := (survivor_iff hv k R _ ht.2 g).2 ⟨hgk,hw⟩
  exact forced_handoff hv k R _ ht.2 g hsur ((residual_order_iff hv k P R hm c g hc ho A hb hgk).1 hr)

noncomputable def NextFaces (v : Fin 8 → ℝ) (k : Fin 8) (R : ℝ) (c g : Fin 8) (A : Fin 8 → ℕ) : Prop :=
  ∀ i : Fin 8, i≠k → i≠g →
    (0<residual (reading v k c) (reading v k i) R (label (reading v k c*R)) (label (reading v k i*R)) (A i) →
      reading v k i ≤ 3*reading v k g) ∧
    (residual (reading v k c) (reading v k i) R (label (reading v k c*R)) (label (reading v k i*R)) (A i) ≤ 0 →
      reading v k i/4 ≤ reading v k g*((label (reading v k i*R) : ℝ)+(A i : ℝ)+7/8-reading v k i*handoffOpening v k R c))

theorem nextFaces_into_relative {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hm : IsMove (disparitySet v k) P R) (c g : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (A : Fin 8 → ℕ) (hb : Bands v k R c A) (hf : NextFaces v k R c g A) :
    RelativeEntrySecond v k R (handoffOpening v k R c) g := by
  have ht := forced_handoff hv k P R hm c hc ho
  have hd : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc.1,rfl⟩)
  intro i hi hig
  have ha := bands_force_advances hv k P R hm c hc ho A hb i hi
  have hiff := residual_positive_iff _ _ R _ _ (A i) hd (show 0 ≤ reading v k i from abs_nonneg _) ht.1.le (handoff_identity hv k c R hc.1) ha
  constructor
  · intro hsur
    exact (hf i hi hig).1 (hiff.2 ((survivor_iff hv k R _ ht.2 i).1 hsur).2)
  · intro hn
    have hnon : residual (reading v k c) (reading v k i) R (label (reading v k c*R)) (label (reading v k i*R)) (A i) ≤ 0 :=
      le_of_not_gt (fun hp=>hn ((survivor_iff hv k R _ ht.2 i).2 ⟨hi,hiff.1 hp⟩))
    have hid := advance_identity (reading v k i) R (handoffOpening v k R c) (abs_nonneg _) ht.1.le
    rw [ha] at hid
    have hidR : (label (reading v k i*handoffOpening v k R c) : ℝ)=(label (reading v k i*R) : ℝ)+(A i : ℝ) := by exact_mod_cast hid
    rw [hidR]
    exact (hf i hi hig).2 hnon

-- STANDING: DEFINITION
noncomputable def RelayClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (P R : ℝ) (c g : Fin 8) (A : Fin 8 → ℕ),
    0<P ∧ IsMove (disparitySet v k) P R ∧ Survivor v k P R c ∧ OpeningOrder v k P R c ∧
    Bands v k R c A ∧ g≠k ∧
    0<residual (reading v k c) (reading v k g) R (label (reading v k c*R)) (label (reading v k g*R)) (A g) ∧
    ResidualOrder v k R c g A ∧ NextFaces v k R c g A

theorem relay_into_relative {v : Fin 8 → ℝ} {k : Fin 8} (h : RelayClass v k) : HandoffRelativeClass v k := by
  obtain ⟨hv,P,R,c,g,A,hP,hm,hc,ho,hb,hgk,hg,hr,hf⟩ := h
  have ht := forced_handoff hv k P R hm c hc ho
  have hd : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc.1,rfl⟩)
  have hw := (residual_positive_iff _ _ R _ _ (A g) hd (abs_nonneg _) ht.1.le (handoff_identity hv k c R hc.1)
    (bands_force_advances hv k P R hm c hc ho A hb g hgk)).1 hg
  have hR := lt_of_lt_of_le hP (le_of_isMove (disparitySet_pos hv k) hm)
  exact ⟨hv,R,handoffOpening v k R c,g,⟨hR,ht.2,(survivor_iff hv k R _ ht.2 g).2 ⟨hgk,hw⟩,
    (residual_order_iff hv k P R hm c g hc ho A hb hgk).1 hr⟩,
    nextFaces_into_relative hv k P R hm c g hc ho A hb hf⟩

theorem relay_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : RelayClass v k) : Isolation v k :=
  handoff_relative_isolation (relay_into_relative h)

theorem singleGroup_into_residual {v : Fin 8 → ℝ} {k : Fin 8}
    (h : Fresh.NativeExcursionArrangement.RelayClass v k) : RelayClass v k := by
  obtain ⟨hv,P,R,c,g,A,hP,hm,hc,ho,hb,hg,hf⟩ := h
  have ht := forced_handoff hv k P R hm c hc ho
  have hd : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc.1,rfl⟩)
  have hopen := handoff_identity hv k c R hc.1
  have hsur := (group_survivors hv k P R hm c g hc ho A hb hg g).2 ⟨hg.1,rfl⟩
  have hmove := group_forces_move hv k P R hm c g hc ho A hb hg
  have horder := order_of_move hv k R _ ht.2 g hsur hmove.2
  have hrel := retained_into_relative hv k P R hm c g hc ho A hb hg hf
  refine ⟨hv,P,R,c,g,A,hP,hm,hc,ho,hb,hg.1,?_,
    (residual_order_iff hv k P R hm c g hc ho A hb hg.1).2 horder,?_⟩
  · exact (residual_positive_iff _ _ R _ _ (A g) hd (abs_nonneg _) ht.1.le hopen
      (bands_force_advances hv k P R hm c hc ho A hb g hg.1)).2 ((survivor_iff hv k R _ ht.2 g).1 hsur).2
  · intro i hi hig
    have ha := bands_force_advances hv k P R hm c hc ho A hb i hi
    have hiff := residual_positive_iff _ _ R _ _ (A i) hd (show 0 ≤ reading v k i from abs_nonneg _) ht.1.le hopen ha
    constructor
    · intro hp
      exact (hrel i hi hig).1 ((survivor_iff hv k R _ ht.2 i).2 ⟨hi,hiff.1 hp⟩)
    · intro hnon
      have hn : ¬Survivor v k R (handoffOpening v k R c) i := by
        intro hs
        exact not_lt_of_ge hnon (hiff.2 ((survivor_iff hv k R _ ht.2 i).1 hs).2)
      have hh := (hrel i hi hig).2 hn
      have hid := advance_identity (reading v k i) R (handoffOpening v k R c) (abs_nonneg _) ht.1.le
      rw [ha] at hid
      have hidR : (label (reading v k i*handoffOpening v k R c) : ℝ)=(label (reading v k i*R) : ℝ)+(A i : ℝ) := by exact_mod_cast hid
      simpa only [hidR] using hh

#print axioms singleGroup_into_residual
#print axioms residual_forces_handoff
#print axioms nextFaces_into_relative
#print axioms relay_into_relative
#print axioms relay_isolation
#print axioms residual_identity
#print axioms residual_positive_iff
#print axioms residual_order_iff
end Fresh.NativeExcursionOpeningOrder
