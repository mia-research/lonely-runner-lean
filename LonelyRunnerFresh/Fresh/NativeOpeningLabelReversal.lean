import Fresh.NativeLabelBoundaryFrontiers
import Fresh.NativeOpeningReversal

/-! Local relations between a processed own-opening anchor and the next
captured setter. A sufficiently high current setter label forces the old
anchor's closing guard; immediate recapture forces a threefold label gap.
The exact advance-weighted face retains independent unbounded advances.
No label descent or global move/label budget is asserted. -/
namespace Fresh.NativeOpeningLabelReversal
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels
  Fresh.NativeReturnHandoff Fresh.NativeReturnClosingOrder Fresh.NativeReturnSurvivors
  Fresh.NativeOpeningReversal Fresh.NativeLabelBoundaryFrontiers
  Fresh.FastestCaptureRetention

theorem opening_label_compact (d s B : ℝ) (N : ℤ) (hB : 0 < B)
    (ho : d*B=(N : ℝ)+1/8) (hw : InWay s B)
    (hl : N < 3*label (s*B)) : d < 3*s := by
  have hlo := (capture_at_label s B hw).1
  have hi : N+1 ≤ 3*label (s*B) := by omega
  have hr : (N : ℝ)+1 ≤ 3*(label (s*B) : ℝ) := by exact_mod_cast hi
  by_contra hn
  have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hB.le
  nlinarith only [ho,hlo,hr,hm]

theorem label_cone_retained_window (d s B C : ℝ) (N : ℤ) (hd : 0 < d)
    (hs : 0 < s) (hB : 0 < B) (ho : d*B=(N : ℝ)+1/8)
    (hw : InWay s B) (hc : s*C=(label (s*B) : ℝ)+1/8)
    (hl : N < 3*label (s*B)) :
    (N : ℝ)+1/8 ≤ d*C ∧ d*C < (N : ℝ)+7/8 :=
  own_opening_retained s d B C _ N hs hd.le
    (opening_label_compact d s B N hB ho hw hl).le ho hw hc rfl

theorem label_cone_closing_zero (d s B C : ℝ) (N : ℤ) (hd : 0 < d)
    (hs : 0 < s) (hB : 0 < B) (ho : d*B=(N : ℝ)+1/8)
    (hw : InWay s B) (hc : s*C=(label (s*B) : ℝ)+1/8)
    (hl : N < 3*label (s*B)) :
    C ≤ closing d B ∧ advance d B C=0 ∧ ¬InWay d C := by
  have hh := label_cone_retained_window d s B C N hd hs hB ho hw hc hl
  have hlabel := Fresh.NativeCohortOutsiderRelay.label_at_opening d B N ho
  have ht := Fresh.NativeOpeningRetention.capture_advance s B C _ hs hc
    (capture_at_label s B hw).1 (capture_at_label s B hw).2
  have hu : d*C ≤ (label (d*B) : ℝ)+7/8 := by rw [hlabel]; exact hh.2.le
  refine ⟨?_,(zero_iff_original_upper d B C hd.le (by linarith only [ht.1])).2 hu,
    not_lt.mpr (clear_of_window N hh.1 hh.2.le)⟩
  apply (le_div_iff₀ hd).2
  simpa only [closing,mul_comm] using hu

theorem recapture_label_floor (d s B C : ℝ) (N : ℤ) (hd : 0 < d)
    (hs : 0 < s) (hB : 0 < B) (ho : d*B=(N : ℝ)+1/8)
    (hw : InWay s B) (hc : s*C=(label (s*B) : ℝ)+1/8)
    (hret : InWay d C) : 3*label (s*B) ≤ N := by
  apply le_of_not_gt
  intro hl
  exact (label_cone_closing_zero d s B C N hd hs hB ho hw hc hl).2.2 hret

theorem recapture_advance_label_face (d s B C : ℝ) (N : ℤ) (hd : 0 < d)
    (hs : 0 < s) (hB : 0 < B) (ho : d*B=(N : ℝ)+1/8)
    (hw : InWay s B) (hc : s*C=(label (s*B) : ℝ)+1/8)
    (hret : InWay d C) :
    (4*(advance d B C : ℤ)-1)*(8*label (s*B)-1) < 8*N+1 := by
  have hsep := recapture_forces_separation d s B C N _ hd hs ho hw hc rfl hret
  have ht := Fresh.NativeOpeningRetention.capture_advance s B C _ hs hc
    (capture_at_label s B hw).1 (capture_at_label s B hw).2
  have ha := opening_recapture_positive d B C N hd (by linarith only [ht.1]) ho hret
  have har : (1 : ℝ) ≤ (advance d B C : ℝ) := by exact_mod_cast ha
  have hp : 0 < 4*(advance d B C : ℝ)-1 := by linarith only [har]
  have hlo := mul_lt_mul_of_pos_left (capture_at_label s B hw).1 hp
  have hm := mul_lt_mul_of_pos_right hsep hB
  have hr : (4*(advance d B C : ℝ)-1)*(8*(label (s*B) : ℝ)-1) < 8*(N : ℝ)+1 := by
    nlinarith only [hlo,hm,ho]
  exact_mod_cast hr

theorem selected_anchor_retained {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k a g : Fin 8) (B : ℝ) (N : ℤ) (ha : a≠k) (hg : g≠k) (hB : 0 < B)
    (ho : reading v k a*B=(N : ℝ)+1/8) (hw : InWay (reading v k g) B)
    (hl : N < 3*label (reading v k g*B)) :
    handoffOpening v k B g ≤ closing (reading v k a) B ∧
      advance (reading v k a) B (handoffOpening v k B g)=0 ∧
      ¬InWay (reading v k a) (handoffOpening v k B g) := by
  have hap := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hgp := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  exact label_cone_closing_zero _ _ B _ N hap hgp hB ho hw (handoff_identity hv k g B hg) hl

theorem selected_anchor_recapture_floor {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k a g : Fin 8) (B : ℝ) (N : ℤ) (ha : a≠k) (hg : g≠k) (hB : 0 < B)
    (ho : reading v k a*B=(N : ℝ)+1/8) (hw : InWay (reading v k g) B)
    (hret : InWay (reading v k a) (handoffOpening v k B g)) :
    3*label (reading v k g*B) ≤ N := by
  have hap := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hgp := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  exact recapture_label_floor _ _ B _ N hap hgp hB ho hw (handoff_identity hv k g B hg) hret

theorem opening_packet_retained {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k g : Fin 8) (B : ℝ) (I : Finset (Fin 8)) (hI : I ⊆ Finset.univ.erase k)
    (hg : g≠k) (hB : 0 < B) (hw : InWay (reading v k g) B)
    (hanchors : ∀ i∈I, ∃ N : ℤ, reading v k i*B=(N : ℝ)+1/8 ∧ N < 3*label (reading v k g*B)) :
    ∀ i∈I, handoffOpening v k B g ≤ closing (reading v k i) B ∧
      advance (reading v k i) B (handoffOpening v k B g)=0 ∧
      ¬InWay (reading v k i) (handoffOpening v k B g) := by
  intro i hi
  obtain ⟨N,ho,hl⟩ := hanchors i hi
  exact selected_anchor_retained hv k i g B N (Finset.mem_erase.mp (hI hi)).1 hg hB ho hw hl

theorem boundary_defect_identity (d s B C : ℝ) (N : ℤ)
    (ho : d*B=(N : ℝ)+1/8) (hc : s*C=(label (s*B) : ℝ)+1/8)
    (he : N=3*label (s*B)) :
    (24*(label (s*B) : ℝ)+7)*(s*B-((label (s*B) : ℝ)-1/8))-1 =
      8*(s*B)*((N : ℝ)+7/8-d*C) := by
  have hNr : (N : ℝ)=3*(label (s*B) : ℝ) := by exact_mod_cast he
  have hb : (s*B)*(d*C)=((N : ℝ)+1/8)*((label (s*B) : ℝ)+1/8) := by
    calc
      _ = (d*B)*(s*C) := by ring
      _ = _ := by rw [ho,hc]
  rw [hNr] at hb ⊢
  nlinarith only [hb]

theorem floor_equal_next_upper (d s B C : ℝ) (N : ℤ) (hs : 0 < s) (hB : 0 < B)
    (ho : d*B=(N : ℝ)+1/8) (hw : InWay s B)
    (hc : s*C=(label (s*B) : ℝ)+1/8)
    (hM : 0 < label (s*B)) (he : N=3*label (s*B)) : d*C < (N : ℝ)+9/8 := by
  have hNr : (N : ℝ)=3*(label (s*B) : ℝ) := by exact_mod_cast he
  have hMr : (1 : ℝ) ≤ (label (s*B) : ℝ) := by exact_mod_cast hM
  have hp : 0 < (N : ℝ)+9/8 := by rw [hNr]; linarith only [hMr]
  have hb : ((N : ℝ)+1/8)*((label (s*B) : ℝ)+1/8) <
      ((label (s*B) : ℝ)-1/8)*((N : ℝ)+9/8) := by
    rw [hNr]
    nlinarith only [hMr]
  have hm := mul_lt_mul_of_pos_right (capture_at_label s B hw).1 hp
  have hscaled : (s*B)*(d*C) < (s*B)*((N : ℝ)+9/8) := by
    calc
      (s*B)*(d*C) = (d*B)*(s*C) := by ring
      _ = ((N : ℝ)+1/8)*((label (s*B) : ℝ)+1/8) := by rw [ho,hc]
      _ < ((label (s*B) : ℝ)-1/8)*((N : ℝ)+9/8) := hb
      _ < (s*B)*((N : ℝ)+9/8) := hm
  have hx := mul_pos hs hB
  nlinarith only [hscaled,hx]

theorem floor_equal_capture_iff (d s B C : ℝ) (N : ℤ) (hd : 0 < d)
    (hs : 0 < s) (hB : 0 < B) (ho : d*B=(N : ℝ)+1/8)
    (hw : InWay s B) (hc : s*C=(label (s*B) : ℝ)+1/8)
    (hM : 0 < label (s*B)) (he : N=3*label (s*B)) :
    InWay d C ↔ (24*(label (s*B) : ℝ)+7)*(s*B-((label (s*B) : ℝ)-1/8)) < 1 := by
  have hid := boundary_defect_identity d s B C N ho hc he
  have hx : 0 < 8*(s*B) := by positivity
  have ht := Fresh.NativeOpeningRetention.capture_advance s B C _ hs hc
    (capture_at_label s B hw).1 (capture_at_label s B hw).2
  have hlow : (N : ℝ)+1/8 ≤ d*C := by
    have hm := mul_nonneg hd.le ht.1.le
    nlinarith only [hm,ho]
  have hu := floor_equal_next_upper d s B C N hs hB ho hw hc hM he
  constructor
  · intro hwc
    have hcross : (N : ℝ)+7/8 < d*C := by
      apply lt_of_not_ge
      intro hupper
      exact not_lt_of_ge (clear_of_window N hlow hupper) hwc
    have hm := mul_neg_of_pos_of_neg hx (show (N : ℝ)+7/8-d*C < 0 by linarith only [hcross])
    linarith only [hid,hm]
  · intro hface
    have hcross : (N : ℝ)+7/8 < d*C := by
      apply lt_of_not_ge
      intro hn
      have hm := mul_nonneg hx.le (show 0 ≤ (N : ℝ)+7/8-d*C by linarith only [hn])
      linarith only [hid,hm,hface]
    have hh : |d*C-((N+1 : ℤ) : ℝ)| < 1/8 := by
      rw [abs_lt]
      push_cast
      constructor <;> linarith only [hcross,hu]
    exact lt_of_le_of_lt (Fresh.Cascade.distInt_le _ _) hh

theorem equal_label_boundary_closing_zero (d s B C : ℝ) (N : ℤ) (hd : 0 < d)
    (hs : 0 < s) (hB : 0 < B) (ho : d*B=(N : ℝ)+1/8)
    (hw : InWay s B) (hc : s*C=(label (s*B) : ℝ)+1/8)
    (he : N=3*label (s*B))
    (hface : 1 ≤ (24*(label (s*B) : ℝ)+7)*(s*B-((label (s*B) : ℝ)-1/8))) :
    C ≤ closing d B ∧ advance d B C=0 ∧ ¬InWay d C := by
  have hid := boundary_defect_identity d s B C N ho hc he
  have hx : 0 < 8*(s*B) := by positivity
  have huN : d*C ≤ (N : ℝ)+7/8 := by
    apply le_of_not_gt
    intro hn
    have hm := mul_neg_of_pos_of_neg hx (show (N : ℝ)+7/8-d*C < 0 by linarith only [hn])
    linarith only [hid,hm,hface]
  have hlabel := Fresh.NativeCohortOutsiderRelay.label_at_opening d B N ho
  have ht := Fresh.NativeOpeningRetention.capture_advance s B C _ hs hc
    (capture_at_label s B hw).1 (capture_at_label s B hw).2
  have hu : d*C ≤ (label (d*B) : ℝ)+7/8 := by rw [hlabel]; exact huN
  have hlow : (N : ℝ)+1/8 ≤ d*C := by
    have hm := mul_nonneg hd.le ht.1.le
    nlinarith only [hm,ho]
  refine ⟨?_,(zero_iff_original_upper d B C hd.le (by linarith only [ht.1])).2 hu,
    not_lt.mpr (clear_of_window N hlow huN)⟩
  apply (le_div_iff₀ hd).2
  simpa only [closing,mul_comm] using hu

theorem floor_equality_advance_one (d s B C : ℝ) (N : ℤ) (hd : 0 < d)
    (hs : 0 < s) (hB : 0 < B) (ho : d*B=(N : ℝ)+1/8)
    (hw : InWay s B) (hc : s*C=(label (s*B) : ℝ)+1/8)
    (hret : InWay d C) (hM : 0 < label (s*B)) (he : N=3*label (s*B)) :
    advance d B C=1 := by
  have hf := recapture_advance_label_face d s B C N hd hs hB ho hw hc hret
  rw [he] at hf
  have ht := Fresh.NativeOpeningRetention.capture_advance s B C _ hs hc
    (capture_at_label s B hw).1 (capture_at_label s B hw).2
  have ha := opening_recapture_positive d B C N hd (by linarith only [ht.1]) ho hret
  by_contra hn
  have htwo : (2 : ℤ) ≤ (advance d B C : ℤ) := by omega
  have hm := mul_le_mul_of_nonneg_right (show (7 : ℤ) ≤ 4*(advance d B C : ℤ)-1 by omega)
    (show (0 : ℤ) ≤ 8*label (s*B)-1 by omega)
  nlinarith only [hf,hm,hM]

theorem recapture_boundary_alternatives (d s B C : ℝ) (N : ℤ) (hd : 0 < d)
    (hs : 0 < s) (hB : 0 < B) (ho : d*B=(N : ℝ)+1/8)
    (hw : InWay s B) (hc : s*C=(label (s*B) : ℝ)+1/8)
    (hret : InWay d C) (hM : 0 < label (s*B)) :
    3*label (s*B)+1 ≤ N ∨
      (N=3*label (s*B) ∧ advance d B C=1 ∧ (24*(label (s*B) : ℝ)+7)*(s*B-((label (s*B) : ℝ)-1/8)) < 1) := by
  have hf := recapture_label_floor d s B C N hd hs hB ho hw hc hret
  by_cases he : N=3*label (s*B)
  · refine Or.inr ⟨he,floor_equality_advance_one d s B C N hd hs hB ho hw hc hret hM he,?_⟩
    exact (floor_equal_capture_iff d s B C N hd hs hB ho hw hc hM he).1 hret
  · exact Or.inl (by omega)

theorem label_anchors_into_retained {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k g : Fin 8) (B : ℝ) (hB : 0 < B) (hp : Fresh.NativeCurrentLabelPacket.Packet v k B g)
    (hfront : ∀ f : Fin 8, f≠k → InWay (reading v k f) B →
      (∀ i : Fin 8, i≠k → InWay (reading v k i) B →
        label (reading v k i*B)=label (reading v k f*B) → reading v k f ≤ reading v k i) →
      handoffOpening v k B f ≤ handoffOpening v k B g)
    (hclose : ∀ f : Fin 8, f≠k → ¬InWay (reading v k f) B →
      (∀ i : Fin 8, i≠k → ¬InWay (reading v k i) B →
        label (reading v k i*B)=label (reading v k f*B) → reading v k i ≤ reading v k f) →
      (∃ N : ℤ, reading v k f*B=(N : ℝ)+1/8 ∧
        (N < 3*label (reading v k g*B) ∨
          (N=3*label (reading v k g*B) ∧ 1 ≤ (24*(label (reading v k g*B) : ℝ)+7)*
            (reading v k g*B-((label (reading v k g*B) : ℝ)-1/8))))) ∨
        handoffOpening v k B g ≤ closing (reading v k f) B) :
    Fresh.NativeCurrentLabelPacket.RetainedClass v k := by
  apply frontier_retained_packet hv k g B hB hp hfront
  intro f hf hw hmax
  rcases hclose f hf hw hmax with ⟨N,ho,hl⟩|hc
  · rcases hl with hl|⟨he,hphase⟩
    · exact (selected_anchor_retained hv k f g B N hf hp.1 hB ho hp.2.1 hl).1
    · exact (equal_label_boundary_closing_zero _ _ B _ N
        (disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨f,hf,rfl⟩))
        (disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hp.1,rfl⟩))
        hB ho hp.2.1 (handoff_identity hv k g B hp.1) he hphase).1
  · exact hc

#print axioms boundary_defect_identity
#print axioms floor_equal_next_upper
#print axioms floor_equal_capture_iff
#print axioms equal_label_boundary_closing_zero
#print axioms floor_equality_advance_one
#print axioms recapture_boundary_alternatives

#print axioms opening_label_compact
#print axioms label_cone_retained_window
#print axioms label_cone_closing_zero
#print axioms recapture_label_floor
#print axioms recapture_advance_label_face
#print axioms selected_anchor_retained
#print axioms selected_anchor_recapture_floor
#print axioms opening_packet_retained
#print axioms label_anchors_into_retained
end Fresh.NativeOpeningLabelReversal
