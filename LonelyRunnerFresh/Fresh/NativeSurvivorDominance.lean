import Fresh.NativeExcursionOpeningOrder

/-! A slower captured reading with no smaller current label strictly
outlasts a faster one. Such a dominated reading cannot set the next move;
this removes candidates without deleting their physical clearance duties. -/
namespace Fresh.NativeSurvivorDominance
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement Fresh.NativeReturnClosingOrder

theorem dominated_opening_strict {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hP : 0 ≤ P) (hm : IsMove (disparitySet v k) P R) (i j : Fin 8)
    (hi : Survivor v k P R i) (hj : Survivor v k P R j)
    (hs : reading v k j<reading v k i) (hl : label (reading v k i*R) ≤ label (reading v k j*R)) :
    handoffOpening v k R i<handoffOpening v k R j := by
  have hip : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi.1,rfl⟩)
  have hjp : 0<reading v k j := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨j,hj.1,rfl⟩)
  have hpos := Fresh.NativeRepeatedReturnLabels.returned_label_positive (reading v k j) P R hjp.le hP
    (le_of_isMove (disparitySet_pos hv k) hm) hj.2.1
  have hposR : (1 : ℝ) ≤ (label (reading v k j*R) : ℝ) := by exact_mod_cast hpos
  have hlR : (label (reading v k i*R) : ℝ) ≤ (label (reading v k j*R) : ℝ) := by exact_mod_cast hl
  dsimp [handoffOpening,Fresh.FastestCaptureRetention.opening]
  apply (div_lt_div_iff₀ hip hjp).2
  have ha := mul_le_mul_of_nonneg_right hlR hjp.le
  have hb := mul_pos (sub_pos.mpr hs) (show 0<(label (reading v k j*R) : ℝ)+1/8 by linarith only [hposR])
  nlinarith only [ha,hb]

theorem dominated_not_selected {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hP : 0 ≤ P) (hm : IsMove (disparitySet v k) P R) (i j : Fin 8)
    (hi : Survivor v k P R i) (hj : Survivor v k P R j)
    (hs : reading v k j<reading v k i) (hl : label (reading v k i*R) ≤ label (reading v k j*R)) :
    ¬OpeningOrder v k P R i := by
  intro ho
  have hlt := dominated_opening_strict hv k P R hP hm i j hi hj hs hl
  have hmove := (forced_handoff hv k P R hm i hi ho).2
  have hci := (survivor_iff hv k P R hm j).1 hj
  have hmem : reading v k j∈disparitySet v k := mem_disparitySet.mpr ⟨j,hci.1,rfl⟩
  have hle : nextOpening (reading v k j) R ≤ handoffOpening v k R i := by
    rcases hmove with hfixed|⟨s,hs',hws,hid,hmax⟩
    · exact (hfixed.1 _ hmem hci.2).elim
    · exact hmax _ hmem hci.2
  rw [next_at_label _ R hci.2] at hle
  exact not_lt_of_ge hle hlt

theorem selected_label_record {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hP : 0 ≤ P) (hm : IsMove (disparitySet v k) P R) (g : Fin 8)
    (hg : Survivor v k P R g) (ho : OpeningOrder v k P R g) (j : Fin 8)
    (hj : Survivor v k P R j) (hs : reading v k j<reading v k g) :
    label (reading v k j*R)<label (reading v k g*R) := by
  by_contra hn
  exact dominated_not_selected hv k P R hP hm g j hg hj hs (le_of_not_gt hn) ho

noncomputable def LabelRecord (v : Fin 8 → ℝ) (k : Fin 8) (P R : ℝ) (g : Fin 8) : Prop :=
  ∀ j : Fin 8, Survivor v k P R j → reading v k j<reading v k g →
    label (reading v k j*R)<label (reading v k g*R)

noncomputable def UniqueFrontier (v : Fin 8 → ℝ) (k : Fin 8) (P R : ℝ) (g : Fin 8) : Prop :=
  ∀ j : Fin 8, Survivor v k P R j → LabelRecord v k P R j → reading v k j=reading v k g

theorem unique_frontier_handoff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hP : 0 ≤ P) (hm : IsMove (disparitySet v k) P R) (g : Fin 8) (hg : Survivor v k P R g)
    (hunique : UniqueFrontier v k P R g) :
    R<handoffOpening v k R g ∧ IsMove (disparitySet v k) R (handoffOpening v k R g) := by
  obtain ⟨j,hj,ho,ht,hmove⟩ := exists_handoff hv k P R hm ⟨g,hg⟩
  have hrec : LabelRecord v k P R j := fun i hi hsl=>selected_label_record hv k P R hP hm j hj ho i hi hsl
  have heq := hunique j hj hrec
  have hop : handoffOpening v k R j=handoffOpening v k R g := by simp only [handoffOpening,heq]
  exact ⟨by simpa only [hop] using ht,by simpa only [hop] using hmove⟩

-- STANDING: DEFINITION
noncomputable def FrontierQuarterClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (P R : ℝ) (g a : Fin 8), 0<P ∧ IsMove (disparitySet v k) P R ∧
    Survivor v k P R g ∧ UniqueFrontier v k P R g ∧ QuarterEntrySecond v k R g a

theorem frontier_into_quarter {v : Fin 8 → ℝ} {k : Fin 8} (h : FrontierQuarterClass v k) : HandoffQuarterClass v k := by
  obtain ⟨hv,P,R,g,a,hP,hm,hg,hunique,hq⟩ := h
  have ht := unique_frontier_handoff hv k P R hP.le hm g hg hunique
  exact ⟨hv,P,R,g,a,⟨hP,hm,hg,order_of_move hv k P R hm g hg ht.2⟩,hq⟩

theorem frontier_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : FrontierQuarterClass v k) : Isolation v k :=
  handoff_quarter_isolation (frontier_into_quarter h)

theorem entry_selected_label_record {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (P R : ℝ)
    (hP : 0 ≤ P) (hm : IsMove (disparitySet v k) P R) (c g : Fin 8) (hc : Survivor v k P R c)
    (ho : OpeningOrder v k P R c) (A : Fin 8 → ℕ) (hb : Fresh.NativeExcursionArrangement.Bands v k R c A)
    (hgk : g≠k)
    (hg : 0<Fresh.NativeExcursionOpeningOrder.residual (reading v k c) (reading v k g) R
      (label (reading v k c*R)) (label (reading v k g*R)) (A g))
    (hr : Fresh.NativeExcursionOpeningOrder.ResidualOrder v k R c g A)
    (j : Fin 8) (hjk : j≠k)
    (hj : 0<Fresh.NativeExcursionOpeningOrder.residual (reading v k c) (reading v k j) R
      (label (reading v k c*R)) (label (reading v k j*R)) (A j))
    (hslow : reading v k j<reading v k g) :
    label (reading v k j*R)+(A j : ℤ)<label (reading v k g*R)+(A g : ℤ) := by
  have ht := forced_handoff hv k P R hm c hc ho
  have ht2 := Fresh.NativeExcursionOpeningOrder.residual_forces_handoff hv k P R hm c g hc ho A hb hgk hg hr
  have hd : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc.1,rfl⟩)
  have hsur : ∀ i : Fin 8, i≠k →
      0<Fresh.NativeExcursionOpeningOrder.residual (reading v k c) (reading v k i) R
        (label (reading v k c*R)) (label (reading v k i*R)) (A i) → Survivor v k R (handoffOpening v k R c) i := by
    intro i hi hpos
    have ha := Fresh.NativeExcursionArrangement.bands_force_advances hv k P R hm c hc ho A hb i hi
    have hw := (Fresh.NativeExcursionOpeningOrder.residual_positive_iff _ _ R _ _ (A i) hd
      (show 0 ≤ reading v k i from abs_nonneg _) ht.1.le (handoff_identity hv k c R hc.1) ha).1 hpos
    exact (survivor_iff hv k R _ ht.2 i).2 ⟨hi,hw⟩
  have hrec := selected_label_record hv k R _ (le_trans hP (le_of_isMove (disparitySet_pos hv k) hm)) ht.2 g
    (hsur g hgk hg) (order_of_move hv k R _ ht.2 g (hsur g hgk hg) ht2.2) j (hsur j hjk hj) hslow
  have hjid := advance_identity (reading v k j) R (handoffOpening v k R c) (abs_nonneg _) ht.1.le
  have hgid := advance_identity (reading v k g) R (handoffOpening v k R c) (abs_nonneg _) ht.1.le
  rw [Fresh.NativeExcursionArrangement.bands_force_advances hv k P R hm c hc ho A hb j hjk] at hjid
  rw [Fresh.NativeExcursionArrangement.bands_force_advances hv k P R hm c hc ho A hb g hgk] at hgid
  simpa only [hjid,hgid] using hrec

#print axioms entry_selected_label_record
#print axioms unique_frontier_handoff
#print axioms frontier_into_quarter
#print axioms frontier_isolation
#print axioms dominated_opening_strict
#print axioms dominated_not_selected
#print axioms selected_label_record
end Fresh.NativeSurvivorDominance
