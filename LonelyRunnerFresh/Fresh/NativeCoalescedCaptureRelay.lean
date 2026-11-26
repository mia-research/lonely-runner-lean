import Fresh.NativeOneReaderDeformation

/-! Different captures and different intermediate selected openings can rejoin
one actual fixed-group opening. Fixed-reader canonical labels, not a global
move budget, control this local coalescence. Every clearance duty remains. -/
open Classical
namespace Fresh.NativeCoalescedCaptureRelay
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnHandoffArrangement Fresh.NativeReturnClosingOrder
  Fresh.NativeOneReaderDeformation Fresh.NativeCohortOutsiderRelay Fresh.NativeCapturedPartnerJoin
  Fresh.FastestCaptureRetention

theorem move_of_opening_record {ds : Finset ℝ} (hpos : ∀ d∈ds,0<d) (U C : ℝ)
    (hUC : U ≤ C) (hcover : ∀ d∈ds,labelledOpening d U ≤ C)
    (hanchor : ∃ d∈ds,labelledOpening d U=C) : IsMove ds U C := by
  by_cases he : U=C
  · refine Or.inl ⟨?_,he.symm⟩
    intro d hd hw
    have hh := lt_nextOpening (hpos d hd) hw
    rw [captured_opening d U hw] at hh
    exact not_lt_of_ge (le_trans (hcover d hd) he.ge) hh
  · have hlt : U<C := lt_of_le_of_ne hUC he
    obtain ⟨d,hd,ho⟩ := hanchor
    have hp := hpos d hd
    have hid : (label (d*U) : ℝ)+1/8=C*d := by
      exact (div_eq_iff hp.ne').1 ho
    have hw : InWay d U := by
      apply (inWay_iff_lower_not_passed d U).2
      have hh := mul_lt_mul_of_pos_right hlt hp
      nlinarith only [hh,hid]
    refine Or.inr ⟨d,hd,hw,?_,?_⟩
    · rw [captured_opening d U hw]
      exact ho.symm
    · intro s hs hws
      rw [captured_opening s U hws]
      exact hcover s hs

theorem same_labels_nonfixed_move {ds : Finset ℝ} (hpos : ∀ d∈ds,0<d) (R S C : ℝ)
    (hm : IsMove ds R C) (hRC : R<C) (hSC : S ≤ C)
    (hl : ∀ d∈ds,label (d*S)=label (d*R)) : IsMove ds S C := by
  apply move_of_opening_record hpos S C hSC
  · intro d hd
    have hp := hpos d hd
    have hh := move_passes_entry_opening hpos R C d hm hd
    dsimp [labelledOpening,opening]
    rw [hl d hd]
    apply (div_le_iff₀ hp).2
    simpa only [mul_comm] using hh
  · rcases hm with hf|⟨d,hd,hw,hC,hmax⟩
    · exact (ne_of_lt hRC hf.2.symm).elim
    · refine ⟨d,hd,?_⟩
      rw [captured_opening d R hw] at hC
      simpa only [labelledOpening,hl d hd] using hC.symm

theorem own_opening_labelled (s T : ℝ) (M : ℤ) (hs : 0<s)
    (ho : s*T=(M : ℝ)+1/8) : labelledOpening s T=T := by
  dsimp [labelledOpening,opening]
  rw [label_at_opening s T M ho]
  apply (div_eq_iff hs.ne').2
  nlinarith only [ho]

theorem own_opening_next_move {ds : Finset ℝ} (hpos : ∀ d∈ds,0<d) (s T C : ℝ) (M : ℤ)
    (hs : 0<s) (ho : s*T=(M : ℝ)+1/8) (hm : IsMove ds T C) :
    IsMove (insert s ds) T C := by
  have hh := insert_move hpos s T C hs hm
  rw [own_opening_labelled s T M hs ho,max_eq_left (le_of_isMove hpos hm)] at hh
  exact hh

theorem own_opening_next_step {ds : Finset ℝ} (hpos : ∀ d∈ds,0<d) (s T : ℝ) (M : ℤ)
    (hs : 0<s) (ho : s*T=(M : ℝ)+1/8) : step (insert s ds) T=step ds T := by
  exact isMove_unique (isMove_step _ _) (own_opening_next_move hpos s T _ M hs ho (isMove_step ds T))

theorem two_stage_coalescence {ds : Finset ℝ} (hpos : ∀ d∈ds,0<d) (s U B C : ℝ)
    (hs : 0<s) (hUB : IsMove ds U B) (hBC : IsMove ds B C)
    (hfirst : (label (s*U) : ℝ)+1/8 ≤ s*B)
    (hsecond : (label (s*B) : ℝ)+1/8 ≤ s*C) :
    IsMove (insert s ds) U B ∧ IsMove (insert s ds) B C := by
  exact ⟨(unchanged_move_iff hpos s U B hs hUB).2 hfirst,
    (unchanged_move_iff hpos s B C hs hBC).2 hsecond⟩

theorem delete_current_capture_move {ds : Finset ℝ} (s U B : ℝ) (hs : 0<s)
    (hm : IsMove (insert s ds) U B) (hw : InWay s B) : IsMove ds U B := by
  rcases hm with hf|⟨d,hd,hwd,hB,hmax⟩
  · exact (hf.1 s (Finset.mem_insert_self _ _) (hf.2 ▸ hw)).elim
  · have hneq : d≠s := by
      intro he
      subst d
      rw [hB] at hw
      exact not_inWay_at_nextOpening hs hw
    have hmem : d∈ds := (Finset.mem_insert.mp hd).resolve_left hneq
    exact Or.inr ⟨d,hmem,hwd,hB,fun q hq hwq=>hmax q (Finset.mem_insert_of_mem hq) hwq⟩

theorem clear_part_preserves_move {ds : Finset ℝ} (hpos : ∀ d∈ds,0<d) (U B : ℝ)
    (hm : IsMove ds U B) :
    IsMove (ds.filter (fun d=>¬InWay d B)) U B ∧ LonelyAt (ds.filter (fun d=>¬InWay d B)) B := by
  refine ⟨?_,?_⟩
  · rcases hm with hf|⟨d,hd,hwd,hB,hmax⟩
    · exact Or.inl ⟨fun q hq=>hf.1 q (Finset.mem_filter.mp hq).1,hf.2⟩
    · have hclear : ¬InWay d B := by rw [hB]; exact not_inWay_at_nextOpening (hpos d hd)
      exact Or.inr ⟨d,Finset.mem_filter.mpr ⟨hd,hclear⟩,hwd,hB,
        fun q hq hwq=>hmax q (Finset.mem_filter.mp hq).1 hwq⟩
  · intro d hd
    exact not_lt.mp (Finset.mem_filter.mp hd).2

theorem captured_part_sets_next {ds : Finset ℝ} (B C : ℝ) (hm : IsMove ds B C) :
    IsMove (ds.filter (fun d=>InWay d B)) B C := by
  rcases hm with hf|⟨d,hd,hwd,hC,hmax⟩
  · exact Or.inl ⟨fun q hq=>hf.1 q (Finset.mem_filter.mp hq).1,hf.2⟩
  · exact Or.inr ⟨d,Finset.mem_filter.mpr ⟨hd,hwd⟩,hwd,hC,
      fun q hq hwq=>hmax q (Finset.mem_filter.mp hq).1 hwq⟩

theorem selected_openings_recoalesce {ds : Finset ℝ} (hpos : ∀ d∈ds,0<d)
    (s t T V R C : ℝ) (M N : ℤ) (hs : 0<s) (ht : 0<t)
    (hos : s*T=(M : ℝ)+1/8) (hot : t*V=(N : ℝ)+1/8)
    (hm : IsMove ds R C) (hRC : R<C) (hTC : T ≤ C) (hVC : V ≤ C)
    (hlT : ∀ d∈ds,label (d*T)=label (d*R))
    (hlV : ∀ d∈ds,label (d*V)=label (d*R)) :
    IsMove (insert s ds) T C ∧ IsMove (insert t ds) V C := by
  exact ⟨own_opening_next_move hpos s T C M hs hos
      (same_labels_nonfixed_move hpos R T C hm hRC hTC hlT),
    own_opening_next_move hpos t V C N ht hot
      (same_labels_nonfixed_move hpos R V C hm hRC hVC hlV)⟩

theorem label_between (x z y : ℝ) (hxz : x ≤ z) (hzy : z ≤ y) (hl : label x=label y) :
    label z=label y := by
  have h1 := label_monotone hxz
  have h2 := label_monotone hzy
  omega

theorem speed_interval_label (a s b U : ℝ) (has : a ≤ s) (hsb : s ≤ b) (hU : 0 ≤ U)
    (hl : label (a*U)=label (b*U)) : label (s*U)=label (a*U) := by
  exact (label_between _ _ _ (mul_le_mul_of_nonneg_right has hU)
    (mul_le_mul_of_nonneg_right hsb hU) hl).trans hl.symm

theorem speed_interval_capture (a s b B : ℝ) (has : a ≤ s) (hsb : s ≤ b) (hB : 0 ≤ B)
    (hl : label (a*B)=label (b*B)) (hb : InWay b B) : InWay s B := by
  apply (inWay_iff_lower_not_passed s B).2
  rw [speed_interval_label a s b B has hsb hB hl,hl]
  have hh := mul_le_mul_of_nonneg_right hsb hB
  exact lt_of_le_of_lt hh ((inWay_iff_lower_not_passed b B).1 hb)

theorem interval_opening_bounds (a s b : ℝ) (M : ℤ) (ha : 0<a) (has : a ≤ s) (hsb : s ≤ b)
    (hM : 0 ≤ (M : ℝ)+1/8) : opening b M ≤ opening s M ∧ opening s M ≤ opening a M := by
  have hs := lt_of_lt_of_le ha has
  exact ⟨div_le_div_of_nonneg_left hM hs hsb,div_le_div_of_nonneg_left hM ha has⟩

theorem delayed_interval_moves {ds : Finset ℝ} (hpos : ∀ d∈ds,0<d)
    (a s b B C : ℝ) (M : ℤ) (ha : 0<a) (has : a ≤ s) (hsb : s ≤ b) (hB : 0<B)
    (hla : label (a*B)=M) (hlb : label (b*B)=M) (hwb : InWay b B)
    (hbase : step ds B ≤ opening b M)
    (hnext : IsMove ds (opening a M) C) (hstrict : opening a M<C)
    (hlabels : ∀ d∈ds,label (d*opening b M)=label (d*opening a M)) :
    B<opening s M ∧ IsMove (insert s ds) B (opening s M) ∧
      IsMove (insert s ds) (opening s M) C := by
  have hs := lt_of_lt_of_le ha has
  have hM0 := positive_entry_label a B ha hB
  rw [hla] at hM0
  have hMR : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM0
  have hM : (0 : ℝ) ≤ (M : ℝ)+1/8 := by linarith only [hMR]
  have bounds := interval_opening_bounds a s b M ha has hsb hM
  have hls : label (s*B)=M := (speed_interval_label a s b B has hsb hB.le (hla.trans hlb.symm)).trans hla
  have hf := insert_move hpos s B (step ds B) hs (isMove_step ds B)
  have hOs : labelledOpening s B=opening s M := by simp only [labelledOpening,hls]
  rw [hOs,max_eq_right (le_trans hbase bounds.1)] at hf
  have hrecord : ∀ d∈ds,label (d*opening s M)=label (d*opening a M) := by
    intro d hd
    exact label_between _ _ _ (mul_le_mul_of_nonneg_left bounds.1 (hpos d hd).le)
      (mul_le_mul_of_nonneg_left bounds.2 (hpos d hd).le) (hlabels d hd)
  have hm := same_labels_nonfixed_move hpos (opening a M) (opening s M) C hnext hstrict
    (le_trans bounds.2 hstrict.le) hrecord
  have ho : s*opening s M=(M : ℝ)+1/8 := by dsimp [opening]; field_simp
  have hw := speed_interval_capture a s b B has hsb hB.le (hla.trans hlb.symm) hwb
  have hstrictSelf := lt_nextOpening hs hw
  rw [captured_opening s B hw,hOs] at hstrictSelf
  exact ⟨hstrictSelf,hf,own_opening_next_move hpos s (opening s M) C M hs ho hm⟩

theorem interval_clearance (a s b C : ℝ) (has : a ≤ s) (hsb : s ≤ b) (hC : 0 ≤ C)
    (hl : label (a*C)=label (b*C)) (ha : ¬InWay a C) : ¬InWay s C := by
  have hlow := le_of_not_gt (fun h=>ha ((inWay_iff_lower_not_passed a C).2 h))
  apply not_lt.mpr
  apply clear_of_window (label (a*C))
  · exact le_trans hlow (mul_le_mul_of_nonneg_right has hC)
  · have hu := ((entry_interval b C _).1 (label_entry b C)).2
    rw [←hl] at hu
    exact le_trans (mul_le_mul_of_nonneg_right hsb hC) hu

theorem delayed_interval_isolated {ds : Finset ℝ} (a s b C : ℝ)
    (has : a ≤ s) (hsb : s ≤ b) (hC : 0 ≤ C) (hfixed : LonelyAt ds C)
    (hl : label (a*C)=label (b*C)) (ha : ¬InWay a C) :
    LonelyAt (insert s ds) C := by
  exact (inserted_lonely_iff ds s C).2 ⟨hfixed,interval_clearance a s b C has hsb hC hl ha⟩

-- The sole CAPTURE may coexist with several previously recovered returns.
theorem sole_capture_handoff {v : Fin 8 → ℝ} (hv : IsArrangement v) (k a : Fin 8) (U B : ℝ)
    (ha : a≠k) (hm : IsMove (disparitySet v k) U B) (hwa : InWay (reading v k a) B)
    (hother : ∀ i : Fin 8,i≠k → i≠a → ¬InWay (reading v k i) B) :
    B<handoffOpening v k B a ∧ IsMove (disparitySet v k) B (handoffOpening v k B a) := by
  apply sole_survivor_handoff hv k U B hm a ((survivor_iff hv k U B hm a).2 ⟨ha,hwa⟩)
  intro i hi
  by_contra hia
  exact hother i hi.1 hia ((survivor_iff hv k U B hm i).1 hi).2

theorem sole_capture_fits_partner {v : Fin 8 → ℝ} (hv : IsArrangement v) (k a : Fin 8) (U B : ℝ)
    (hU : 0<U) (ha : a≠k) (hm : IsMove (disparitySet v k) U B) (hwa : InWay (reading v k a) B)
    (hother : ∀ i : Fin 8,i≠k → i≠a → ¬InWay (reading v k i) B)
    (hfit : ∀ i : Fin 8,i≠k → i≠a → handoffOpening v k B a ≤ closing (reading v k i) B) :
    PartnerClass v k := by
  have ht := sole_capture_handoff hv k a U B ha hm hwa hother
  refine ⟨hv,B,a,lt_of_lt_of_le hU (le_of_isMove (disparitySet_pos hv k) hm),ha,hwa,ht.2,?_⟩
  intro i hi
  refine ⟨?_,?_⟩
  · intro hw
    have he : i=a := by by_contra hn; exact hother i hi hn hw
    exact Or.inr (by rw [he])
  · intro hc
    have hia : i≠a := by intro he; subst i; exact hc hwa
    exact hfit i hi hia

#print axioms move_of_opening_record
#print axioms same_labels_nonfixed_move
#print axioms own_opening_labelled
#print axioms own_opening_next_move
#print axioms own_opening_next_step
#print axioms two_stage_coalescence
#print axioms delete_current_capture_move
#print axioms clear_part_preserves_move
#print axioms captured_part_sets_next
#print axioms selected_openings_recoalesce
#print axioms label_between
#print axioms speed_interval_label
#print axioms speed_interval_capture
#print axioms interval_opening_bounds
#print axioms delayed_interval_moves
#print axioms interval_clearance
#print axioms delayed_interval_isolated
#print axioms sole_capture_handoff
#print axioms sole_capture_fits_partner
end Fresh.NativeCoalescedCaptureRelay
