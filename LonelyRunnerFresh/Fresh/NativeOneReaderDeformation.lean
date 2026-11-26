import Fresh.NativeTwoSetterPacket

/-! One physical speed deformation at a supplied cascade entry. The other
readings' actual move is retained, and the inserted reading changes that move
only across its exact opening face. No comparison state is assumed visited,
no reading's clearance duty is deleted, and labels remain unbounded. -/
namespace Fresh.NativeOneReaderDeformation
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnClosingOrder

noncomputable def labelledOpening (s U : ℝ) : ℝ :=
  Fresh.FastestCaptureRetention.opening s (label (s*U))

theorem clear_opening_le (s U : ℝ) (hs : 0<s) (hw : ¬InWay s U) :
    labelledOpening s U  ≤  U := by
  have hh := le_of_not_gt (fun h=>(hw ((inWay_iff_lower_not_passed s U).2 h)))
  dsimp [labelledOpening,Fresh.FastestCaptureRetention.opening]
  apply (div_le_iff₀ hs).2
  nlinarith only [hh]

theorem captured_opening (s U : ℝ) (hw : InWay s U) :
    nextOpening s U=labelledOpening s U := next_at_label s U hw

theorem insert_move {ds : Finset ℝ} (hpos : ∀ d∈ds,0<d) (s U B : ℝ)
    (hs : 0<s) (hm : IsMove ds U B) :
    IsMove (insert s ds) U (max B (labelledOpening s U)) := by
  have hUB := le_of_isMove hpos hm
  by_cases hw : InWay s U
  · have ho := captured_opening s U hw
    by_cases hle : labelledOpening s U  ≤  B
    · rw [max_eq_left hle]
      rcases hm with hf|⟨d,hd,hwd,hB,hmax⟩
      · have hstrict := lt_nextOpening hs hw
        rw [ho] at hstrict
        have hBU := hf.2
        exact (not_lt_of_ge (le_trans hle hBU.le) hstrict).elim
      · refine Or.inr ⟨d,Finset.mem_insert_of_mem hd,hwd,hB,?_⟩
        intro q hq hwq
        rcases Finset.mem_insert.mp hq with rfl|hq
        · simpa only [ho] using hle
        · exact hmax q hq hwq
    · rw [max_eq_right (le_of_not_ge hle)]
      refine Or.inr ⟨s,Finset.mem_insert_self _ _,hw,ho.symm,?_⟩
      intro q hq hwq
      rcases Finset.mem_insert.mp hq with rfl|hq
      · exact ho.le
      · rcases hm with hf|⟨d,hd,hwd,hB,hmax⟩
        · exact (hf.1 q hq hwq).elim
        · exact le_trans (hmax q hq hwq) (le_of_not_ge hle)
  · have hle := le_trans (clear_opening_le s U hs hw) hUB
    rw [max_eq_left hle]
    rcases hm with hf|⟨d,hd,hwd,hB,hmax⟩
    · refine Or.inl ⟨?_,hf.2⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl|hq
      · exact hw
      · exact hf.1 q hq
    · refine Or.inr ⟨d,Finset.mem_insert_of_mem hd,hwd,hB,?_⟩
      intro q hq hwq
      rcases Finset.mem_insert.mp hq with rfl|hq
      · exact (hw hwq).elim
      · exact hmax q hq hwq

theorem insert_step {ds : Finset ℝ} (hpos : ∀ d∈ds,0<d) (s U : ℝ) (hs : 0<s) :
    step (insert s ds) U=max (step ds U) (labelledOpening s U) := by
  exact isMove_unique (isMove_step _ _) (insert_move hpos s U _ hs (isMove_step ds U))

theorem unchanged_move_iff {ds : Finset ℝ} (hpos : ∀ d∈ds,0<d) (s U B : ℝ)
    (hs : 0<s) (hm : IsMove ds U B) :
    IsMove (insert s ds) U B  ↔  (label (s*U) : ℝ)+1/8  ≤  s*B := by
  have hfull := insert_move hpos s U B hs hm
  have ho : labelledOpening s U ≤ B  ↔  (label (s*U) : ℝ)+1/8 ≤ s*B := by
    dsimp [labelledOpening,Fresh.FastestCaptureRetention.opening]
    rw [div_le_iff₀ hs,mul_comm B s]
  constructor
  · intro hh
    have he := isMove_unique hfull hh
    exact ho.1 (he ▸ le_max_right B (labelledOpening s U))
  · intro hh
    simpa only [max_eq_left (ho.2 hh)] using hfull

theorem displacing_move {ds : Finset ℝ} (hpos : ∀ d∈ds,0<d) (s U B : ℝ)
    (hs : 0<s) (hm : IsMove ds U B)
    (hface : s*B<(label (s*U) : ℝ)+1/8) :
    B<labelledOpening s U ∧ IsMove (insert s ds) U (labelledOpening s U) := by
  have hlt : B<labelledOpening s U := by
    dsimp [labelledOpening,Fresh.FastestCaptureRetention.opening]
    apply (lt_div_iff₀ hs).2
    simpa only [mul_comm] using hface
  exact ⟨hlt,by simpa only [max_eq_right hlt.le] using insert_move hpos s U B hs hm⟩

theorem move_passes_entry_opening {ds : Finset ℝ} (hpos : ∀ d∈ds,0<d) (U B s : ℝ)
    (hm : IsMove ds U B) (hs : s∈ds) :
    (label (s*U) : ℝ)+1/8 ≤ s*B := by
  have hsp := hpos s hs
  by_cases hw : InWay s U
  · have hn : nextOpening s U ≤ B := by
      rcases hm with hf|⟨d,hd,hwd,hB,hmax⟩
      · exact (hf.1 s hs hw).elim
      · exact hmax s hs hw
    rw [captured_opening s U hw] at hn
    dsimp [labelledOpening,Fresh.FastestCaptureRetention.opening] at hn
    have hh := (div_le_iff₀ hsp).1 hn
    simpa only [mul_comm] using hh
  · have hn := clear_opening_le s U hsp hw
    have hle := le_trans hn (le_of_isMove hpos hm)
    dsimp [labelledOpening,Fresh.FastestCaptureRetention.opening] at hle
    have hh := (div_le_iff₀ hsp).1 hle
    simpa only [mul_comm] using hh

theorem union_move_iff {ds added : Finset ℝ} (hpos : ∀ d∈ds,0<d)
    (hadded : ∀ s∈added,0<s) (U B : ℝ) (hm : IsMove ds U B) :
    IsMove (ds∪added) U B ↔ ∀ s∈added,(label (s*U) : ℝ)+1/8 ≤ s*B := by
  have hboth : ∀ s∈ds∪added,0<s := by
    intro s hs
    rcases Finset.mem_union.mp hs with hs|hs
    · exact hpos s hs
    · exact hadded s hs
  constructor
  · intro hh s hs
    exact move_passes_entry_opening hboth U B s hh (Finset.mem_union_right _ hs)
  · intro hfaces
    rcases hm with hf|⟨d,hd,hwd,hB,hmax⟩
    · refine Or.inl ⟨?_,hf.2⟩
      intro s hs
      rcases Finset.mem_union.mp hs with hs|hs
      · exact hf.1 s hs
      · have hh := hfaces s hs
        rw [hf.2] at hh
        exact fun hw=>not_lt_of_ge hh ((inWay_iff_lower_not_passed s U).1 hw)
    · refine Or.inr ⟨d,Finset.mem_union_left _ hd,hwd,hB,?_⟩
      intro s hs hw
      rcases Finset.mem_union.mp hs with hs|hs
      · exact hmax s hs hw
      · rw [captured_opening s U hw]
        dsimp [labelledOpening,Fresh.FastestCaptureRetention.opening]
        apply (div_le_iff₀ (hadded s hs)).2
        simpa only [mul_comm] using hfaces s hs

noncomputable def others (v : Fin 8 → ℝ) (k a : Fin 8) : Finset ℝ :=
  ((Finset.univ.erase k).erase a).image (reading v k)

theorem others_pos {v : Fin 8 → ℝ} (hv : IsArrangement v) (k a : Fin 8) :
    ∀ s∈others v k a,0<s := by
  intro s hs
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hs
  exact disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨i,(Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1,rfl⟩)

theorem insert_others (v : Fin 8 → ℝ) (k a : Fin 8) (ha : a≠k) :
    insert (reading v k a) (others v k a)=disparitySet v k := by
  ext s
  constructor
  · intro hs
    rcases Finset.mem_insert.mp hs with rfl|hs
    · exact mem_disparitySet.mpr ⟨a,ha,rfl⟩
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hs
      exact mem_disparitySet.mpr ⟨i,(Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1,rfl⟩
  · intro hs
    obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hs
    by_cases hia : i=a
    · subst i; exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨i,Finset.mem_erase.mpr ⟨hia,Finset.mem_erase.mpr ⟨hi,Finset.mem_univ _⟩⟩,rfl⟩

theorem physical_step {v : Fin 8 → ℝ} (hv : IsArrangement v) (k a : Fin 8) (ha : a≠k) (U : ℝ) :
    step (disparitySet v k) U=max (step (others v k a) U) (labelledOpening (reading v k a) U) := by
  rw [←insert_others v k a ha]
  exact insert_step (others_pos hv k a) _ U (disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩))

theorem same_others {v w : Fin 8 → ℝ} (k a : Fin 8) (ha : a≠k)
    (he : ∀ i : Fin 8,i≠a → w i=v i) : others w k a=others v k a := by
  have hk := he k ha.symm
  unfold others
  apply Finset.image_congr
  intro i hi
  have hia := (Finset.mem_erase.mp hi).1
  simp only [reading,he i hia,hk]

theorem physical_deformation_step {v w : Fin 8 → ℝ} (hw : IsArrangement w) (k a : Fin 8)
    (ha : a≠k) (he : ∀ i : Fin 8,i≠a → w i=v i) (U : ℝ) :
    step (disparitySet w k) U=max (step (others v k a) U) (labelledOpening (reading w k a) U) := by
  rw [physical_step hw k a ha U,same_others k a ha he]

theorem physical_deformation_move_iff {v w : Fin 8 → ℝ} (hw : IsArrangement w) (k a : Fin 8)
    (ha : a≠k) (he : ∀ i : Fin 8,i≠a → w i=v i) (U B : ℝ)
    (hm : IsMove (others v k a) U B) :
    IsMove (disparitySet w k) U B ↔
      (label (reading w k a*U) : ℝ)+1/8 ≤ reading w k a*B := by
  have hp := disparitySet_pos hw k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hothers := others_pos hw k a
  rw [same_others k a ha he] at hothers
  rw [←insert_others w k a ha,same_others k a ha he]
  exact unchanged_move_iff hothers _ U B hp hm

theorem same_label_monotone {ds : Finset ℝ} (hpos : ∀ d∈ds,0<d) (s t U : ℝ)
    (hs : 0<s) (hst : s ≤ t) (hlabel : label (s*U)=label (t*U))
    (hN : 0 ≤ (label (s*U) : ℝ)+1/8) :
    step (insert t ds) U ≤ step (insert s ds) U := by
  have ht : 0<t := lt_of_lt_of_le hs hst
  rw [insert_step hpos t U ht,insert_step hpos s U hs]
  apply max_le_max le_rfl
  dsimp [labelledOpening,Fresh.FastestCaptureRetention.opening]
  rw [←hlabel]
  exact div_le_div_of_nonneg_left hN hs hst

theorem positive_entry_label (s U : ℝ) (hs : 0<s) (hU : 0<U) :
    0 ≤ label (s*U) := by
  have hb := ((entry_interval s U _).1 (label_entry s U)).2
  have hpos := mul_pos hs hU
  by_contra hn
  have hN : label (s*U) ≤ -1 := by omega
  have hR : (label (s*U) : ℝ) ≤ -1 := by exact_mod_cast hN
  linarith only [hb,hpos,hR]

theorem positive_same_label_monotone {ds : Finset ℝ} (hpos : ∀ d∈ds,0<d) (s t U : ℝ)
    (hs : 0<s) (hst : s ≤ t) (hU : 0<U) (hlabel : label (s*U)=label (t*U)) :
    step (insert t ds) U ≤ step (insert s ds) U := by
  have hN : (0 : ℝ) ≤ (label (s*U) : ℝ) := by exact_mod_cast positive_entry_label s U hs hU
  exact same_label_monotone hpos s t U hs hst hlabel (by linarith only [hN])

theorem same_comparison_coalesces {ds : Finset ℝ} (hpos : ∀ d∈ds,0<d) (s t U B : ℝ)
    (hs : 0<s) (ht : 0<t) (hm : IsMove ds U B)
    (hfs : (label (s*U) : ℝ)+1/8 ≤ s*B)
    (hft : (label (t*U) : ℝ)+1/8 ≤ t*B) :
    step (insert s ds) U=B ∧ step (insert t ds) U=B := by
  exact ⟨isMove_unique (isMove_step _ _) ((unchanged_move_iff hpos s U B hs hm).2 hfs),
    isMove_unique (isMove_step _ _) ((unchanged_move_iff hpos t U B ht hm).2 hft)⟩

theorem inserted_lonely_iff (ds : Finset ℝ) (s B : ℝ) :
    LonelyAt (insert s ds) B ↔ LonelyAt ds B ∧ ¬InWay s B := by
  constructor
  · intro h
    exact ⟨fun d hd=>h d (Finset.mem_insert_of_mem hd),not_lt.mpr (h s (Finset.mem_insert_self _ _))⟩
  · rintro ⟨h,hs⟩ d hd
    rcases Finset.mem_insert.mp hd with rfl|hd
    · exact not_lt.mp hs
    · exact h d hd

theorem clear_at_comparison_forces_move {ds : Finset ℝ} (hpos : ∀ d∈ds,0<d) (s U B : ℝ)
    (hs : 0<s) (hm : IsMove ds U B) (hclear : ¬InWay s B) :
    IsMove (insert s ds) U B := by
  apply (unchanged_move_iff hpos s U B hs hm).2
  have hUB := le_of_isMove hpos hm
  have hl := label_monotone (mul_le_mul_of_nonneg_left hUB hs.le)
  have hlR : (label (s*U) : ℝ) ≤ (label (s*B) : ℝ) := by exact_mod_cast hl
  have hlow := le_of_not_gt (fun h=>hclear ((inWay_iff_lower_not_passed s B).2 h))
  linarith only [hlR,hlow]

theorem isolating_comparison_iff {ds : Finset ℝ} (hpos : ∀ d∈ds,0<d) (s U B : ℝ)
    (hs : 0<s) (hm : IsMove ds U B) (hl : LonelyAt ds B) :
    (IsMove (insert s ds) U B ∧ LonelyAt (insert s ds) B) ↔ ¬InWay s B := by
  constructor
  · intro h
    exact ((inserted_lonely_iff ds s B).1 h.2).2
  · intro hc
    exact ⟨clear_at_comparison_forces_move hpos s U B hs hm hc,(inserted_lonely_iff ds s B).2 ⟨hl,hc⟩⟩

noncomputable def openingFace (s d : ℝ) (N K : ℤ) : ℝ := d*((N : ℝ)+1/8)-s*((K : ℝ)+1/8)
noncomputable def closingFace (s d : ℝ) (N K : ℤ) : ℝ := d*((N : ℝ)+7/8)-s*((K : ℝ)+7/8)

theorem paired_face_difference (s d : ℝ) (N K : ℤ) :
    closingFace s d N K-openingFace s d N K=(3/4)*(d-s) := by
  unfold closingFace openingFace
  ring

theorem opening_tie_closing_order (s d : ℝ) (N K : ℤ) (hs : 0<s) (hd : 0<d)
    (htie : Fresh.FastestCaptureRetention.opening s N=Fresh.FastestCaptureRetention.opening d K) :
    ((N : ℝ)+7/8)/s ≤ ((K : ℝ)+7/8)/d  ↔  d ≤ s := by
  have ho : openingFace s d N K=0 := by
    have hh := (div_eq_div_iff hs.ne' hd.ne').1 htie
    dsimp [openingFace]
    nlinarith only [hh]
  rw [div_le_div_iff₀ hs hd]
  have hf := paired_face_difference s d N K
  unfold closingFace at hf
  constructor <;> intro hh <;> nlinarith only [hf,ho,hh]

theorem both_ties_same_reading (s d : ℝ) (N K : ℤ)
    (ho : openingFace s d N K=0) (hc : closingFace s d N K=0) : s=d := by
  have hh := paired_face_difference s d N K
  linarith only [ho,hc,hh]

#print axioms positive_entry_label
#print axioms positive_same_label_monotone
#print axioms same_comparison_coalesces
#print axioms inserted_lonely_iff
#print axioms clear_at_comparison_forces_move
#print axioms isolating_comparison_iff
#print axioms clear_opening_le
#print axioms move_passes_entry_opening
#print axioms union_move_iff
#print axioms captured_opening
#print axioms insert_move
#print axioms insert_step
#print axioms unchanged_move_iff
#print axioms displacing_move
#print axioms others_pos
#print axioms insert_others
#print axioms physical_step
#print axioms same_others
#print axioms physical_deformation_step
#print axioms physical_deformation_move_iff
#print axioms same_label_monotone
#print axioms paired_face_difference
#print axioms opening_tie_closing_order
#print axioms both_ties_same_reading
end Fresh.NativeOneReaderDeformation
