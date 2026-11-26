import Fresh.NativeSurvivorDominance

/-! Entry time cancels from the scaled displacement faces. Given the same
canonical entry labels, all independent excursion bands and next-setter
residual comparisons are invariant within that native labelled entry. -/
namespace Fresh.NativeExcursionEntryInvariance
open Fresh Fresh.NativeEntryLabels Fresh.NativeReturnHandoff Fresh.NativeReturnExcursion
  Fresh.NativeExcursionArrangement Fresh.NativeExcursionOpeningOrder

theorem excursion_cancel (d s R : ℝ) (N K : ℤ) :
    excursion d s R N K=s*((N : ℝ)+1/8)-d*((K : ℝ)+7/8) := by
  unfold excursion
  ring

theorem residual_cancel (d s R : ℝ) (N K : ℤ) (a : ℕ) :
    residual d s R N K a=d*((K : ℝ)+(a : ℝ)+1/8)-s*((N : ℝ)+1/8) := by
  unfold Fresh.NativeExcursionOpeningOrder.residual
  rw [excursion_cancel]
  ring

theorem same_labels_excursion (d s R S : ℝ)
    (hd : label (d*R)=label (d*S)) (hs : label (s*R)=label (s*S)) :
    excursion d s R (label (d*R)) (label (s*R))=
      excursion d s S (label (d*S)) (label (s*S)) := by
  rw [excursion_cancel,excursion_cancel,hd,hs]

theorem same_labels_residual (d s R S : ℝ) (a : ℕ)
    (hd : label (d*R)=label (d*S)) (hs : label (s*R)=label (s*S)) :
    residual d s R (label (d*R)) (label (s*R)) a=
      residual d s S (label (d*S)) (label (s*S)) a := by
  rw [residual_cancel,residual_cancel,hd,hs]

theorem same_labels_opening {v : Fin 8 → ℝ} (k c : Fin 8) (R S : ℝ)
    (hc : label (reading v k c*R)=label (reading v k c*S)) :
    handoffOpening v k R c=handoffOpening v k S c := by
  simp only [handoffOpening,hc]

theorem bands_entry_invariant {v : Fin 8 → ℝ} (k c : Fin 8) (R S : ℝ) (A : Fin 8 → ℕ)
    (hc : c≠k) (hl : ∀ i : Fin 8, i≠k → label (reading v k i*R)=label (reading v k i*S)) :
    Bands v k R c A ↔ Bands v k S c A := by
  have hd := hl c hc
  constructor
  · intro hb i hi
    have hh := hb i hi
    rw [same_labels_excursion _ _ R S hd (hl i hi)] at hh
    exact hh
  · intro hb i hi
    have hh := hb i hi
    rw [←same_labels_excursion _ _ R S hd (hl i hi)] at hh
    exact hh

theorem residual_order_entry_invariant {v : Fin 8 → ℝ} (k c g : Fin 8) (R S : ℝ) (A : Fin 8 → ℕ)
    (hc : c≠k) (hg : g≠k)
    (hl : ∀ i : Fin 8, i≠k → label (reading v k i*R)=label (reading v k i*S)) :
    ResidualOrder v k R c g A ↔ ResidualOrder v k S c g A := by
  have hd := hl c hc
  have heqg := same_labels_residual (reading v k c) (reading v k g) R S (A g) hd (hl g hg)
  constructor
  · intro ho i hi hp
    have heqi := same_labels_residual (reading v k c) (reading v k i) R S (A i) hd (hl i hi)
    have hpR : 0<residual (reading v k c) (reading v k i) R (label (reading v k c*R)) (label (reading v k i*R)) (A i) := by simpa only [heqi] using hp
    have hh := ho i hi hpR
    simpa only [heqi,heqg] using hh
  · intro ho i hi hp
    have heqi := same_labels_residual (reading v k c) (reading v k i) R S (A i) hd (hl i hi)
    have hpS : 0<residual (reading v k c) (reading v k i) S (label (reading v k c*S)) (label (reading v k i*S)) (A i) := by simpa only [←heqi] using hp
    have hh := ho i hi hpS
    simpa only [←heqi,←heqg] using hh

theorem earlier_same_labels_move {v : Fin 8 → ℝ} (hv : IsArrangement v) (k c : Fin 8)
    (S R : ℝ) (hSR : S ≤ R) (hc : c≠k)
    (hwc : Fresh.InWay (reading v k c) R)
    (hm : Fresh.IsMove (Fresh.disparitySet v k) R (handoffOpening v k R c))
    (hl : ∀ i : Fin 8, i≠k → label (reading v k i*S)=label (reading v k i*R)) :
    Fresh.IsMove (Fresh.disparitySet v k) S (handoffOpening v k R c) := by
  have hmem : reading v k c∈Fresh.disparitySet v k := Fresh.Localisation.mem_disparitySet.mpr ⟨c,hc,rfl⟩
  have hd := Fresh.Cascade.disparitySet_pos hv k _ hmem
  have hcR := capture_at_label (reading v k c) R hwc
  have hinc := mul_le_mul_of_nonneg_left hSR hd.le
  have hlowS := ((entry_interval _ _ _).1 (label_entry (reading v k c) S)).1
  have hwS : Fresh.InWay (reading v k c) S := by
    apply (Fresh.NativeReturnSurvivors.inWay_iff_lower_not_passed _ _).2
    rw [hl c hc]
    linarith only [hinc,hcR.2]
  have hnextS : Fresh.nextOpening (reading v k c) S=handoffOpening v k R c := by
    rw [next_at_label _ S hwS]
    simp only [handoffOpening,hl c hc]
  refine Or.inr ⟨reading v k c,hmem,hwS,hnextS.symm,?_⟩
  intro s hs hws
  obtain ⟨i,hi,rfl⟩ := Fresh.Localisation.mem_disparitySet.mp hs
  change Fresh.InWay (reading v k i) S at hws
  change Fresh.nextOpening (reading v k i) S ≤ handoffOpening v k R c
  have hip : 0<reading v k i := Fresh.Cascade.disparitySet_pos hv k _ (Fresh.Localisation.mem_disparitySet.mpr ⟨i,hi,rfl⟩)
  have hnexti : Fresh.nextOpening (reading v k i) S=handoffOpening v k R i := by
    rw [next_at_label _ S hws]
    simp only [handoffOpening,hl i hi]
  rw [hnexti]
  by_cases hwi : Fresh.InWay (reading v k i) R
  · have hle : Fresh.nextOpening (reading v k i) R ≤ handoffOpening v k R c := by
      rcases hm with hfix|⟨d,hd',hwd,hT,hmax⟩
      · exact (hfix.1 _ (Fresh.Localisation.mem_disparitySet.mpr ⟨i,hi,rfl⟩) hwi).elim
      · exact hmax _ (Fresh.Localisation.mem_disparitySet.mpr ⟨i,hi,rfl⟩) hwi
    simpa only [next_at_label _ R hwi,handoffOpening] using hle
  · have hpass : (label (reading v k i*R) : ℝ)+1/8 ≤ reading v k i*R :=
      le_of_not_gt (fun hh=>hwi ((Fresh.NativeReturnSurvivors.inWay_iff_lower_not_passed _ _).2 hh))
    have hleR : handoffOpening v k R i ≤ R := by
      dsimp [handoffOpening,Fresh.FastestCaptureRetention.opening]
      apply (div_le_iff₀ hip).2
      nlinarith only [hpass]
    have hRc : R<handoffOpening v k R c := by
      simpa only [next_at_label _ R hwc,handoffOpening] using Fresh.Cascade.lt_nextOpening hd hwc
    exact le_trans hleR hRc.le

theorem same_labels_advances (s S R T : ℝ) (hl : label (s*S)=label (s*R)) :
    advance s S T=advance s R T := by
  simp only [advance,hl]

#print axioms earlier_same_labels_move
#print axioms same_labels_advances
#print axioms excursion_cancel
#print axioms residual_cancel
#print axioms same_labels_excursion
#print axioms same_labels_residual
#print axioms same_labels_opening
#print axioms bands_entry_invariant
#print axioms residual_order_entry_invariant
end Fresh.NativeExcursionEntryInvariance
