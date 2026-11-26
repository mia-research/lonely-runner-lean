import Fresh.NativeMixedGroupTransport

/-! Native boundary comparisons compressed by canonical label groups.
No shared-opening cohort premise: within an entry-label group, the slowest
reading dominates openings and the fastest dominates closings. Within a
terminal-label group, the slowest dominates the recovery lower comparison.
Labels, their number over a history, and return advances remain unbounded. -/
namespace Fresh.NativeLabelBoundaryFrontiers
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels
  Fresh.NativeReturnHandoff Fresh.NativeReturnClosingOrder Fresh.NativeReturnSurvivors
  Fresh.FastestCaptureRetention

theorem positive_phase_label_nonnegative (s R : ℝ) (hs : 0 < s) (hR : 0 < R) :
    0 ≤ label (s*R) := by
  have hu := ((entry_interval s R _).1 (label_entry s R)).2
  have hprod := mul_pos hs hR
  by_contra hn
  have hi : label (s*R) ≤ -1 := by omega
  have hr : (label (s*R) : ℝ) ≤ -1 := by exact_mod_cast hi
  linarith only [hu,hprod,hr]

theorem common_label_opening_order (p q R : ℝ) (hp : 0 < p) (hpq : p ≤ q)
    (hR : 0 < R) (hl : label (p*R)=label (q*R)) :
    opening q (label (q*R)) ≤ opening p (label (p*R)) := by
  have hN := positive_phase_label_nonnegative p R hp hR
  have hn : (0 : ℝ) ≤ (label (p*R) : ℝ)+1/8 := by
    have hh : (0 : ℝ) ≤ (label (p*R) : ℝ) := by exact_mod_cast hN
    linarith only [hh]
  dsimp [opening]
  rw [←hl]
  exact div_le_div_of_nonneg_left hn hp hpq

theorem common_label_closing_order (p q R : ℝ) (hp : 0 < p) (hpq : p ≤ q)
    (hR : 0 < R) (hl : label (p*R)=label (q*R)) :
    closing q R ≤ closing p R := by
  have hN := positive_phase_label_nonnegative p R hp hR
  have hn : (0 : ℝ) ≤ (label (p*R) : ℝ)+7/8 := by
    have hh : (0 : ℝ) ≤ (label (p*R) : ℝ) := by exact_mod_cast hN
    linarith only [hh]
  dsimp [closing]
  rw [←hl]
  exact div_le_div_of_nonneg_left hn hp hpq

theorem common_terminal_recovery (d p q T : ℝ) (N : ℤ) (hpq : p ≤ q)
    (hN : 0 ≤ (N : ℝ)+1/8) (hl : label (p*T)=label (q*T))
    (hface : d*((label (p*T) : ℝ)+1/8) ≤ p*((N : ℝ)+1/8)) :
    d*((label (q*T) : ℝ)+1/8) ≤ q*((N : ℝ)+1/8) := by
  rw [←hl]
  exact hface.trans (mul_le_mul_of_nonneg_right hpq hN)

theorem group_opening_iff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (I : Finset (Fin 8)) (hI : I ⊆ Finset.univ.erase k) (R V : ℝ) (hR : 0 < R)
    (p : Fin 8) (hp : p∈I)
    (hmin : ∀ i∈I, reading v k p ≤ reading v k i)
    (hl : ∀ i∈I, label (reading v k i*R)=label (reading v k p*R)) :
    (∀ i∈I, handoffOpening v k R i ≤ V) ↔ handoffOpening v k R p ≤ V := by
  constructor
  · intro h; exact h p hp
  · intro h i hi
    have hpp : 0 < reading v k p := disparitySet_pos hv k _
      (mem_disparitySet.mpr ⟨p,(Finset.mem_erase.mp (hI hp)).1,rfl⟩)
    exact (common_label_opening_order _ _ R hpp (hmin i hi) hR (hl i hi).symm).trans h

theorem group_closing_iff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (I : Finset (Fin 8)) (hI : I ⊆ Finset.univ.erase k) (R V : ℝ) (hR : 0 < R)
    (q : Fin 8) (hq : q∈I)
    (hmax : ∀ i∈I, reading v k i ≤ reading v k q)
    (hl : ∀ i∈I, label (reading v k i*R)=label (reading v k q*R)) :
    (∀ i∈I, V ≤ closing (reading v k i) R) ↔ V ≤ closing (reading v k q) R := by
  constructor
  · intro h; exact h q hq
  · intro h i hi
    have hip : 0 < reading v k i := disparitySet_pos hv k _
      (mem_disparitySet.mpr ⟨i,(Finset.mem_erase.mp (hI hi)).1,rfl⟩)
    exact h.trans (common_label_closing_order _ _ R hip (hmax i hi) hR (hl i hi))

theorem group_recovery_iff (v : Fin 8 → ℝ) (k : Fin 8) (I : Finset (Fin 8))
    (T d : ℝ) (N : ℤ) (hN : 0 ≤ (N : ℝ)+1/8) (p : Fin 8) (hp : p∈I)
    (hmin : ∀ i∈I, reading v k p ≤ reading v k i)
    (hl : ∀ i∈I, label (reading v k i*T)=label (reading v k p*T)) :
    (∀ i∈I, d*((label (reading v k i*T) : ℝ)+1/8) ≤ reading v k i*((N : ℝ)+1/8)) ↔
      d*((label (reading v k p*T) : ℝ)+1/8) ≤ reading v k p*((N : ℝ)+1/8) := by
  constructor
  · intro h; exact h p hp
  · intro h i hi
    exact common_terminal_recovery d _ _ T N (hmin i hi) hN (hl i hi).symm h

theorem closing_frontiers_iff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (I : Finset (Fin 8)) (hI : I ⊆ Finset.univ.erase k) (R V : ℝ) (hR : 0 < R) :
    (∀ i∈I, V ≤ closing (reading v k i) R) ↔
      ∀ f∈I, (∀ i∈I, label (reading v k i*R)=label (reading v k f*R) →
        reading v k i ≤ reading v k f) → V ≤ closing (reading v k f) R := by
  classical
  constructor
  · intro h f hf _; exact h f hf
  · intro h i hi
    let J := I.filter (fun j=>label (reading v k j*R)=label (reading v k i*R))
    have him : i∈J := by simp [J,hi]
    obtain ⟨f,hf,hmax⟩ := Finset.exists_max_image J (reading v k) ⟨i,him⟩
    have hfi := (Finset.mem_filter.mp hf).1
    have hfl := (Finset.mem_filter.mp hf).2
    have hface := h f hfi (by
      intro j hj hl
      exact hmax j (by simp only [J,Finset.mem_filter]; exact ⟨hj,hl.trans hfl⟩))
    have his : J ⊆ Finset.univ.erase k := fun j hj=>hI (Finset.mem_filter.mp hj).1
    exact ((group_closing_iff hv k J his R V hR f hf hmax (by
      intro j hj; exact (Finset.mem_filter.mp hj).2.trans hfl.symm)).2 hface) i him

theorem opening_frontiers_iff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8)
    (I : Finset (Fin 8)) (hI : I ⊆ Finset.univ.erase k) (R V : ℝ) (hR : 0 < R) :
    (∀ i∈I, handoffOpening v k R i ≤ V) ↔
      ∀ f∈I, (∀ i∈I, label (reading v k i*R)=label (reading v k f*R) →
        reading v k f ≤ reading v k i) → handoffOpening v k R f ≤ V := by
  classical
  constructor
  · intro h f hf _; exact h f hf
  · intro h i hi
    let J := I.filter (fun j=>label (reading v k j*R)=label (reading v k i*R))
    have him : i∈J := by simp [J,hi]
    obtain ⟨f,hf,hmin⟩ := Finset.exists_min_image J (reading v k) ⟨i,him⟩
    have hfi := (Finset.mem_filter.mp hf).1
    have hfl := (Finset.mem_filter.mp hf).2
    have hface := h f hfi (by
      intro j hj hl
      exact hmin j (by simp only [J,Finset.mem_filter]; exact ⟨hj,hl.trans hfl⟩))
    have his : J ⊆ Finset.univ.erase k := fun j hj=>hI (Finset.mem_filter.mp hj).1
    exact ((group_opening_iff hv k J his R V hR f hf hmin (by
      intro j hj; exact (Finset.mem_filter.mp hj).2.trans hfl.symm)).2 hface) i him

theorem recovery_frontiers_iff (v : Fin 8 → ℝ) (k : Fin 8) (I : Finset (Fin 8))
    (T d : ℝ) (N : ℤ) (hN : 0 ≤ (N : ℝ)+1/8) :
    (∀ i∈I, d*((label (reading v k i*T) : ℝ)+1/8) ≤ reading v k i*((N : ℝ)+1/8)) ↔
      ∀ f∈I, (∀ i∈I, label (reading v k i*T)=label (reading v k f*T) →
        reading v k f ≤ reading v k i) →
        d*((label (reading v k f*T) : ℝ)+1/8) ≤ reading v k f*((N : ℝ)+1/8) := by
  classical
  constructor
  · intro h f hf _; exact h f hf
  · intro h i hi
    let J := I.filter (fun j=>label (reading v k j*T)=label (reading v k i*T))
    have him : i∈J := by simp [J,hi]
    obtain ⟨f,hf,hmin⟩ := Finset.exists_min_image J (reading v k) ⟨i,him⟩
    have hfi := (Finset.mem_filter.mp hf).1
    have hfl := (Finset.mem_filter.mp hf).2
    have hface := h f hfi (by
      intro j hj hl
      exact hmin j (by simp only [J,Finset.mem_filter]; exact ⟨hj,hl.trans hfl⟩))
    exact ((group_recovery_iff v k J T d N hN f hf hmin (by
      intro j hj; exact (Finset.mem_filter.mp hj).2.trans hfl.symm)).2 hface) i him

theorem frontier_selected_move {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k g : Fin 8) (R : ℝ) (hR : 0 < R) (hg : g≠k) (hwg : InWay (reading v k g) R)
    (hfront : ∀ f : Fin 8, f≠k → InWay (reading v k f) R →
      (∀ i : Fin 8, i≠k → InWay (reading v k i) R →
        label (reading v k i*R)=label (reading v k f*R) → reading v k f ≤ reading v k i) →
      handoffOpening v k R f ≤ handoffOpening v k R g) :
    IsMove (disparitySet v k) R (handoffOpening v k R g) := by
  classical
  let I := (Finset.univ.erase k).filter (fun i=>InWay (reading v k i) R)
  have hI : I ⊆ Finset.univ.erase k := fun i hi=>(Finset.mem_filter.mp hi).1
  have hall := (opening_frontiers_iff hv k I hI R (handoffOpening v k R g) hR).2 (by
    intro f hf hmin
    have hfm := Finset.mem_filter.mp hf
    apply hfront f (Finset.mem_erase.mp hfm.1).1 hfm.2
    intro i hi hwi hl
    exact hmin i (by simp [I,hi,hwi]) hl)
  refine Or.inr ⟨reading v k g,mem_disparitySet.mpr ⟨g,hg,rfl⟩,hwg,(next_at_label _ R hwg).symm,?_⟩
  intro d hd hwd
  obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hd
  change InWay (reading v k i) R at hwd
  change nextOpening (reading v k i) R ≤ handoffOpening v k R g
  rw [next_at_label _ R hwd]
  exact hall i (by simp [I,hi,hwd])

theorem frontier_retained_packet {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k g : Fin 8) (R : ℝ) (hR : 0 < R) (hp : Fresh.NativeCurrentLabelPacket.Packet v k R g)
    (hfront : ∀ f : Fin 8, f≠k → InWay (reading v k f) R →
      (∀ i : Fin 8, i≠k → InWay (reading v k i) R →
        label (reading v k i*R)=label (reading v k f*R) → reading v k f ≤ reading v k i) →
      handoffOpening v k R f ≤ handoffOpening v k R g)
    (hclose : ∀ f : Fin 8, f≠k → ¬InWay (reading v k f) R →
      (∀ i : Fin 8, i≠k → ¬InWay (reading v k i) R →
        label (reading v k i*R)=label (reading v k f*R) → reading v k i ≤ reading v k f) →
      handoffOpening v k R g ≤ closing (reading v k f) R) :
    Fresh.NativeCurrentLabelPacket.RetainedClass v k := by
  classical
  let I := (Finset.univ.erase k).filter (fun i=>¬InWay (reading v k i) R)
  have hI : I ⊆ Finset.univ.erase k := fun i hi=>(Finset.mem_filter.mp hi).1
  have hall := (closing_frontiers_iff hv k I hI R (handoffOpening v k R g) hR).2 (by
    intro f hf hmax
    have hfm := Finset.mem_filter.mp hf
    apply hclose f (Finset.mem_erase.mp hfm.1).1 hfm.2
    intro i hi hwi hl
    exact hmax i (by simp [I,hi,hwi]) hl)
  refine ⟨hv,R,g,hR,hp,frontier_selected_move hv k g R hR hp.1 hp.2.1 hfront,?_⟩
  intro i hi hwi
  exact hall i (by simp [I,hi,hwi])

theorem frontier_recovered_canonical {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k g : Fin 8) (R : ℝ) (hR : 0 < R) (hg : g≠k) (hwg : InWay (reading v k g) R)
    (hfront : ∀ f : Fin 8, f≠k → InWay (reading v k f) R →
      (∀ i : Fin 8, i≠k → InWay (reading v k i) R →
        label (reading v k i*R)=label (reading v k f*R) → reading v k f ≤ reading v k i) →
      handoffOpening v k R f ≤ handoffOpening v k R g)
    (hrec : ∀ f : Fin 8, f≠k → 0 < advance (reading v k f) R (handoffOpening v k R g) →
      (∀ i : Fin 8, i≠k → 0 < advance (reading v k i) R (handoffOpening v k R g) →
        label (reading v k i*handoffOpening v k R g)=label (reading v k f*handoffOpening v k R g) →
        reading v k f ≤ reading v k i) →
      reading v k g*((label (reading v k f*handoffOpening v k R g) : ℝ)+1/8) ≤
        reading v k f*((label (reading v k g*R) : ℝ)+1/8)) :
    Fresh.NativeCanonicalReturn.CanonicalReturnClass v k := by
  classical
  let T := handoffOpening v k R g
  let I := (Finset.univ.erase k).filter (fun i=>0 < advance (reading v k i) R T)
  have hgp : 0 < reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  have hN := positive_phase_label_nonnegative _ R hgp hR
  have hn : (0 : ℝ) ≤ (label (reading v k g*R) : ℝ)+1/8 := by
    have hh : (0 : ℝ) ≤ (label (reading v k g*R) : ℝ) := by exact_mod_cast hN
    linarith only [hh]
  have hall := (recovery_frontiers_iff v k I T (reading v k g) _ hn).2 (by
    intro f hf hmin
    have hfm := Finset.mem_filter.mp hf
    apply hrec f (Finset.mem_erase.mp hfm.1).1 hfm.2
    intro i hi ha hl
    exact hmin i (by simp [I,T,hi,ha]) hl)
  have hc := capture_at_label (reading v k g) R hwg
  refine ⟨hv,g,R,label (reading v k g*R),hg,hR,hc.1,hc.2,
    frontier_selected_move hv k g R hR hg hwg hfront,?_⟩
  intro i hi ha
  change 0 < advance (reading v k i) R (handoffOpening v k R g) at ha
  exact hall i (by simp [I,T,hi,ha])

theorem transported_label_cases (p s q R T : ℝ) (hR : 0 < R) (hT : 0 ≤ T)
    (hrel : 7*T < 9*R) (hps : p ≤ s) (hsq : s ≤ q)
    (hp : InWay p R) (hq : InWay q R) (hl : label (p*R)=label (q*R)) :
    label (s*T)=label (p*T) ∨ label (s*T)=label (p*T)+1 := by
  have hd := Fresh.NativeMixedGroupTransport.transported_label_diameter p q R T hR hT hrel hp hq hl
  have hlo := label_monotone (mul_le_mul_of_nonneg_right hps hT)
  have hhi := label_monotone (mul_le_mul_of_nonneg_right hsq hT)
  omega

#print axioms transported_label_cases

#print axioms frontier_selected_move
#print axioms frontier_retained_packet
#print axioms frontier_recovered_canonical

#print axioms closing_frontiers_iff
#print axioms opening_frontiers_iff
#print axioms recovery_frontiers_iff

#print axioms positive_phase_label_nonnegative
#print axioms common_label_opening_order
#print axioms common_label_closing_order
#print axioms common_terminal_recovery
#print axioms group_opening_iff
#print axioms group_closing_iff
#print axioms group_recovery_iff
end Fresh.NativeLabelBoundaryFrontiers
