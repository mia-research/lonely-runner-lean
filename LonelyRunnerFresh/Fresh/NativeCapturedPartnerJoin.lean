import Fresh.NativeOpeningFaceExchange

/-! A captured partner can retain its window by a compact disparity ratio
OR by sharing the selected opening exactly, at arbitrary disparity ratio.
Clear outsiders retain their original closing comparisons independently. -/
namespace Fresh.NativeCapturedPartnerJoin
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement Fresh.NativeReturnClosingOrder

noncomputable def PartnerConditions (v : Fin 8 → ℝ) (k : Fin 8) (R : ℝ) (c : Fin 8) : Prop :=
  ∀ i : Fin 8, i≠k →
    (InWay (reading v k i) R → reading v k i ≤ 3*reading v k c ∨ handoffOpening v k R i=handoffOpening v k R c) ∧
    (¬InWay (reading v k i) R → handoffOpening v k R c ≤ closing (reading v k i) R)

theorem partner_zero {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R : ℝ) (c : Fin 8)
    (hc : c≠k) (hcap : InWay (reading v k c) R)
    (hm : IsMove (disparitySet v k) R (handoffOpening v k R c)) (hb : PartnerConditions v k R c) :
    ∀ i : Fin 8, i≠k → advance (reading v k i) R (handoffOpening v k R c)=0 := by
  have hd : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc,rfl⟩)
  have hcc := capture_at_label (reading v k c) R hcap
  have hid := handoff_identity hv k c R hc
  have hRT : R<handoffOpening v k R c := by
    simpa only [next_at_label _ R hcap,handoffOpening] using lt_nextOpening hd hcap
  intro i hi
  by_cases hwi : InWay (reading v k i) R
  · have hci := capture_at_label (reading v k i) R hwi
    rcases (hb i hi).1 hwi with hratio|htie
    · have hmem : reading v k i∈disparitySet v k := mem_disparitySet.mpr ⟨i,hi,rfl⟩
      have horder := Fresh.FastestCaptureRecovery.captured_order_of_move _ _ hm hmem hd
        (disparitySet_pos hv k _ hmem) hid hci.1 hci.2
      have hw := Fresh.NativeRelativeCapture.captured_window _ _ R _ _ _ hd hratio hid hcc.1 hcc.2 hci.2 horder
      have hl := (entry_iff_label _ _ _).1 (Or.inl ⟨hw.1,hw.2.le⟩)
      simp only [advance,hl,sub_self,Int.toNat_zero]
    · have hidi := handoff_identity hv k i R hi
      rw [htie] at hidi
      exact selected_advance_zero _ R _ _ hci.1 hci.2 hidi
  · have hip : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
    have hclose := (hb i hi).2 hwi
    apply (zero_iff_original_upper (reading v k i) R _ hip.le hRT.le).2
    dsimp [closing] at hclose
    have hh := (le_div_iff₀ hip).1 hclose
    nlinarith only [hh]

-- STANDING: DEFINITION
noncomputable def PartnerClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (R : ℝ) (c : Fin 8), 0<R ∧ c≠k ∧ InWay (reading v k c) R ∧
    IsMove (disparitySet v k) R (handoffOpening v k R c) ∧ PartnerConditions v k R c

-- STANDING: DEFINITION
noncomputable def CohortClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (R : ℝ) (c : Fin 8), 0<R ∧ c≠k ∧ InWay (reading v k c) R ∧
    (∀ i : Fin 8, i≠k → InWay (reading v k i) R → handoffOpening v k R i=handoffOpening v k R c) ∧
    (∀ i : Fin 8, i≠k → ¬InWay (reading v k i) R → handoffOpening v k R c ≤ closing (reading v k i) R)

theorem cohort_move {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R : ℝ) (c : Fin 8)
    (hc : c≠k) (hw : InWay (reading v k c) R)
    (htie : ∀ i : Fin 8, i≠k → InWay (reading v k i) R → handoffOpening v k R i=handoffOpening v k R c) :
    IsMove (disparitySet v k) R (handoffOpening v k R c) := by
  have hmem : reading v k c∈disparitySet v k := mem_disparitySet.mpr ⟨c,hc,rfl⟩
  have hn := next_at_label (reading v k c) R hw
  refine Or.inr ⟨reading v k c,hmem,hw,hn.symm,?_⟩
  intro s hs hws
  obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hs
  change InWay (reading v k i) R at hws
  change nextOpening (reading v k i) R ≤ handoffOpening v k R c
  rw [next_at_label _ R hws]
  exact le_of_eq (htie i hi hws)

theorem cohort_into_partner {v : Fin 8 → ℝ} {k : Fin 8} (h : CohortClass v k) : PartnerClass v k := by
  obtain ⟨hv,R,c,hR,hc,hw,htie,hretain⟩ := h
  exact ⟨hv,R,c,hR,hc,hw,cohort_move hv k R c hc hw htie,fun i hi=>⟨fun hwi=>Or.inr (htie i hi hwi),hretain i hi⟩⟩

theorem partner_into_noReturn {v : Fin 8 → ℝ} {k : Fin 8} (h : PartnerClass v k) :
    Fresh.NativeCanonicalReturn.NoReturnClass v k := by
  obtain ⟨hv,R,c,hR,hc,hw,hm,hb⟩ := h
  have hcap := capture_at_label (reading v k c) R hw
  exact ⟨hv,c,R,label (reading v k c*R),hc,hR,hcap.1,hcap.2,hm,partner_zero hv k R c hc hw hm hb⟩

theorem partner_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : PartnerClass v k) : Isolation v k :=
  Fresh.NativeCanonicalReturn.noReturn_isolation (partner_into_noReturn h)

theorem cohort_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : CohortClass v k) : Isolation v k :=
  partner_isolation (cohort_into_partner h)

theorem cohort_residue_one {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (R : ℝ) (c : Fin 8)
    (hR : 0<R) (hc : c≠k) (hw : InWay (reading v k c) R)
    (htie : ∀ i : Fin 8, i≠k → InWay (reading v k i) R → handoffOpening v k R i=handoffOpening v k R c) :
    ∃ h : ℝ, 0<h ∧ ∀ i : Fin 8, i≠k → InWay (reading v k i) R →
      reading v k i=h*(8*(label (reading v k i*R) : ℝ)+1) := by
  have hd : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc,rfl⟩)
  have hRT : R<handoffOpening v k R c := by
    simpa only [next_at_label _ R hw,handoffOpening] using lt_nextOpening hd hw
  have hT := lt_trans hR hRT
  refine ⟨1/(8*handoffOpening v k R c),by positivity,?_⟩
  intro i hi hwi
  have hid := handoff_identity hv k i R hi
  rw [htie i hi hwi] at hid
  exact Fresh.NativeOpeningFaceExchange.opening_scale _ _ _ hT hid

-- STANDING: DEFINITION
noncomputable def CompactClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (R : ℝ) (c : Fin 8), 0<R ∧ c≠k ∧ InWay (reading v k c) R ∧
    IsMove (disparitySet v k) R (handoffOpening v k R c) ∧
    (∀ i : Fin 8, i≠k → InWay (reading v k i) R → reading v k i ≤ 3*reading v k c) ∧
    (∀ i : Fin 8, i≠k → ¬InWay (reading v k i) R → handoffOpening v k R c ≤ closing (reading v k i) R)

theorem compact_into_partner {v : Fin 8 → ℝ} {k : Fin 8} (h : CompactClass v k) : PartnerClass v k := by
  obtain ⟨hv,R,c,hR,hc,hw,hm,hcaps,hclear⟩ := h
  exact ⟨hv,R,c,hR,hc,hw,hm,fun i hi=>⟨fun hwi=>Or.inl (hcaps i hi hwi),hclear i hi⟩⟩

theorem partner_into_compact {v : Fin 8 → ℝ} {k : Fin 8} (h : PartnerClass v k) : CompactClass v k := by
  classical
  obtain ⟨hv,R,c,hR,hc,hw,hm,hb⟩ := h
  let S := Finset.univ.filter (fun i : Fin 8=>i≠k ∧ InWay (reading v k i) R ∧ handoffOpening v k R i=handoffOpening v k R c)
  have hcmem : c∈S := by simp [S,hc,hw]
  have hne : S.Nonempty := ⟨c,hcmem⟩
  obtain ⟨q,hq,hmax⟩ := Finset.exists_max_image S (reading v k) hne
  have hqm := (Finset.mem_filter.mp hq).2
  have hcq := hmax c hcmem
  have hmove : IsMove (disparitySet v k) R (handoffOpening v k R q) := by rw [hqm.2.2]; exact hm
  refine ⟨hv,R,q,hR,hqm.1,hqm.2.1,hmove,?_,?_⟩
  · intro i hi hwi
    rcases (hb i hi).1 hwi with hratio|htie
    · linarith only [hratio,hcq]
    · have hle := hmax i (by simp [S,hi,hwi,htie])
      have hqp : 0 ≤ reading v k q := abs_nonneg _
      linarith only [hle,hqp]
  · intro i hi hwi
    rw [hqm.2.2]
    exact (hb i hi).2 hwi

theorem compact_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : CompactClass v k) : Isolation v k :=
  partner_isolation (compact_into_partner h)

theorem relative_into_compact {v : Fin 8 → ℝ} {k : Fin 8} (h : HandoffRelativeClass v k) : CompactClass v k := by
  obtain ⟨hv,Q,R,c,he,hb⟩ := h
  have hc := (survivor_iff hv k Q R he.2.1 c).1 he.2.2.1
  have ht := forced_handoff hv k Q R he.2.1 c he.2.2.1 he.2.2.2
  have hR := lt_trans he.1 (predecessor_strict hv k Q R he.2.1 c he.2.2.1)
  have hd : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc.1,rfl⟩)
  have hcc := capture_at_label (reading v k c) R hc.2
  have hid := handoff_identity hv k c R hc.1
  refine ⟨hv,R,c,hR,hc.1,hc.2,ht.2,?_,?_⟩
  · intro i hi hwi
    by_cases hic : i=c
    · rw [hic]; linarith only [hd]
    · exact (hb i hi hic).1 ((survivor_iff hv k Q R he.2.1 i).2 ⟨hi,hwi⟩)
  · intro i hi hwi
    have hic : i≠c := by intro heq; subst i; exact hwi hc.2
    have hn : ¬Survivor v k Q R i := fun hs=>hwi ((survivor_iff hv k Q R he.2.1 i).1 hs).2
    have hquarter := (hb i hi hic).2 hn
    have hlower : (label (reading v k i*R) : ℝ)+1/8 ≤ reading v k i*R :=
      le_of_not_gt (fun hh=>hwi ((inWay_iff_lower_not_passed _ _).2 hh))
    have hw := Fresh.NativeRelativeCapture.retained_window _ _ R _ _ _ hd (abs_nonneg _) hid hcc.1 hcc.2 hlower hquarter
    have hip : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
    dsimp [closing]
    apply (le_div_iff₀ hip).2
    simpa only [reading,mul_comm] using hw.2

-- STANDING: DEFINITION
noncomputable def FaceClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (P R : ℝ) (g h : Fin 8), 0<P ∧ IsMove (disparitySet v k) P R ∧
    Survivor v k P R g ∧ Survivor v k P R h ∧
    (∀ i : Fin 8, Survivor v k P R i → i≠g → i≠h →
      handoffOpening v k R i ≤ max (handoffOpening v k R g) (handoffOpening v k R h)) ∧
    ((handoffOpening v k R g ≤ handoffOpening v k R h ∧ PartnerConditions v k R h) ∨
      (handoffOpening v k R h ≤ handoffOpening v k R g ∧ PartnerConditions v k R g))

theorem face_into_partner {v : Fin 8 → ℝ} {k : Fin 8} (h : FaceClass v k) : PartnerClass v k := by
  obtain ⟨hv,P,R,g,j,hP,hm,hg,hj,hrest,hbranch⟩ := h
  have ht := Fresh.NativeOpeningFaceExchange.two_candidate_move hv k P R hm g j hg hj hrest
  have hR := lt_of_lt_of_le hP (le_of_isMove (disparitySet_pos hv k) hm)
  rcases hbranch with ⟨hgj,hb⟩|⟨hjg,hb⟩
  · have hw := ((survivor_iff hv k P R hm j).1 hj).2
    exact ⟨hv,R,j,hR,hj.1,hw,by simpa only [max_eq_right hgj] using ht.2,hb⟩
  · have hw := ((survivor_iff hv k P R hm g).1 hg).2
    exact ⟨hv,R,g,hR,hg.1,hw,by simpa only [max_eq_left hjg] using ht.2,hb⟩

theorem face_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : FaceClass v k) : Isolation v k :=
  partner_isolation (face_into_partner h)

theorem scaled_opening (s R h : ℝ) (hs : 0<s) (hh : 0<h)
    (hscale : s=h*(8*(label (s*R) : ℝ)+1)) :
    Fresh.FastestCaptureRetention.opening s (label (s*R))=1/(8*h) := by
  dsimp [Fresh.FastestCaptureRetention.opening]
  apply (div_eq_div_iff hs.ne' (by positivity : 8*h≠0)).2
  nlinarith only [hscale]

-- STANDING: DEFINITION
noncomputable def GridCohortClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (R h : ℝ) (c : Fin 8), 0<R ∧ 0<h ∧ c≠k ∧ InWay (reading v k c) R ∧
    (∀ i : Fin 8, i≠k → InWay (reading v k i) R → reading v k i=h*(8*(label (reading v k i*R) : ℝ)+1)) ∧
    (∀ i : Fin 8, i≠k → ¬InWay (reading v k i) R → 1/(8*h) ≤ closing (reading v k i) R)

theorem grid_into_cohort {v : Fin 8 → ℝ} {k : Fin 8} (h : GridCohortClass v k) : CohortClass v k := by
  obtain ⟨hv,R,u,c,hR,hu,hc,hw,hscale,hclear⟩ := h
  have hd : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc,rfl⟩)
  have hcopen : handoffOpening v k R c=1/(8*u) := scaled_opening _ R u hd hu (hscale c hc hw)
  refine ⟨hv,R,c,hR,hc,hw,?_,?_⟩
  · intro i hi hwi
    have hip : 0<reading v k i := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,hi,rfl⟩)
    rw [hcopen]
    exact scaled_opening _ R u hip hu (hscale i hi hwi)
  · intro i hi hwi
    rw [hcopen]
    exact hclear i hi hwi

theorem cohort_into_grid {v : Fin 8 → ℝ} {k : Fin 8} (h : CohortClass v k) : GridCohortClass v k := by
  obtain ⟨hv,R,c,hR,hc,hw,htie,hclear⟩ := h
  obtain ⟨u,hu,hscale⟩ := cohort_residue_one hv k R c hR hc hw htie
  have hd : 0<reading v k c := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨c,hc,rfl⟩)
  have hcopen : handoffOpening v k R c=1/(8*u) := scaled_opening _ R u hd hu (hscale c hc hw)
  refine ⟨hv,R,u,c,hR,hu,hc,hw,hscale,?_⟩
  intro i hi hwi
  rw [←hcopen]
  exact hclear i hi hwi

#print axioms scaled_opening
#print axioms grid_into_cohort
#print axioms cohort_into_grid
#print axioms relative_into_compact
#print axioms face_into_partner
#print axioms face_isolation
#print axioms compact_into_partner
#print axioms partner_into_compact
#print axioms compact_isolation
#print axioms partner_zero
#print axioms cohort_move
#print axioms cohort_into_partner
#print axioms partner_into_noReturn
#print axioms partner_isolation
#print axioms cohort_isolation
#print axioms cohort_residue_one
end Fresh.NativeCapturedPartnerJoin
