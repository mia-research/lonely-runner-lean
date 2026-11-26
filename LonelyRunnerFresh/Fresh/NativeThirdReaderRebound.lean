import Fresh.NativeThirdReaderRetention

/-! A recaptured old partner forces a slow third reader. Either form of
its rebound then clears all three readers. This removes the composed-fit
hypothesis from the derived triple endpoint; outsiders remain explicit. -/
open Classical
namespace Fresh.NativeThirdReaderRebound
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeOneReaderDeformation Fresh.NativeOpeningReversal
  Fresh.NativeThirdReaderRetention Fresh.FastestCaptureRetention

theorem small_old_fit (a b c : ℝ) (ha : 0<a) (hc : 0<c) (hba : b ≤ a) (hbc : b ≤ c) :
    a*b+2*b*c ≤ 3*a*c := by
  have h1 := mul_le_mul_of_nonneg_left hbc ha.le
  have h2 := mul_le_mul_of_nonneg_right hba hc.le
  nlinarith only [h1,h2]

theorem three_clear (a b c T : ℝ) (ha : ¬InWay a T) (hb : ¬InWay b T) (hc : ¬InWay c T) :
    LonelyAt ({a,b,c} : Finset ℝ) T := by
  intro d hd
  simp only [Finset.mem_insert,Finset.mem_singleton] at hd
  rcases hd with he|he|he
  · subst d; exact not_lt.mp ha
  · subst d; exact not_lt.mp hb
  · subst d; exact not_lt.mp hc

noncomputable def reboundEnd (a b c C : ℝ) : ℝ :=
  if InWay a (labelledOpening c (labelledOpening a C)) then partnerEnd a b (thirdEnd a c C)
  else if InWay a (labelledOpening b (thirdEnd a c C)) then partnerEnd b a (labelledOpening b (thirdEnd a c C))
  else labelledOpening b (thirdEnd a c C)

noncomputable def forcedEnd (a b c C : ℝ) : ℝ :=
  if InWay b (thirdEnd a c C) then reboundEnd a b c C else thirdEnd a c C

theorem rebound_resolution (a b c C : ℝ) (M : ℤ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hab : 3*b<a) (ho : b*C=(M : ℝ)+1/8) (hw : InWay a C)
    (hthird : InWay c (labelledOpening a C)) (hret : InWay b (thirdEnd a c C)) :
    ∃ (H : Finset ℝ) (U : ℝ), H ⊆ {a,b,c} ∧ C ≤ U ∧ U<reboundEnd a b c C ∧
      IsMove H U (reboundEnd a b c C) ∧ LonelyAt ({a,b,c} : Finset ℝ) (reboundEnd a b c C) := by
  let E := labelledOpening a C
  let F := labelledOpening c E
  let T := thirdEnd a c C
  have hCE : C<E := by have hh := captured_labelled_advance a C ha hw; dsimp [E]; linarith only [hh.1]
  have hET : E<T := pair_end_after a c E ha hc _ (labelled_opening_identity a C ha) hthird
  have hslow := recaptured_old_forces_slow_third a b c C M ha hb hc hab ho hw hthird hret
  have hcb : c<b := by linarith only [hslow,hc]
  have hba : b<a := by linarith only [hab,hb]
  have hca := hcb.trans hba
  have hF : c*F=(label (c*E) : ℝ)+1/8 := labelled_opening_identity c E hc
  by_cases hr : InWay a F
  · have hT : T=labelledOpening a F := by
      change (if InWay a F then labelledOpening a F else F)=labelledOpening a F
      rw [if_pos hr]
    have hclear := triple_clear a c b F (label (c*E)) ha hc hb hF hr
      (by rw [←hT]; exact hret) (small_old_fit a c b ha hb hca.le hcb.le)
    have hpair := pair_last_move_and_clear a b T (label (a*F)) ha hb
      (by rw [hT]; exact labelled_opening_identity a F ha) hret
    obtain ⟨U,hTU,hUR,hm⟩ := hpair.1
    have hR : reboundEnd a b c C=partnerEnd a b T := by
      change (if InWay a F then partnerEnd a b T else _)=partnerEnd a b T
      rw [if_pos hr]
    rw [hR]
    refine ⟨{a,b},U,?_,hCE.le.trans (hET.le.trans hTU),hUR,hm,?_⟩
    · intro d hd; simp only [Finset.mem_insert,Finset.mem_singleton] at hd ⊢; tauto
    · have hclear' : LonelyAt ({a,c,b} : Finset ℝ) (partnerEnd a b T) := by
        simpa only [thirdEnd,hT] using hclear
      exact three_clear a b c _ (not_lt.mpr (hclear' _ (by simp)))
        (not_lt.mpr (hclear' _ (by simp))) (not_lt.mpr (hclear' _ (by simp)))
  · have hT : T=F := by
      change (if InWay a F then labelledOpening a F else F)=F
      rw [if_neg hr]
    have hTc : c*T=(label (c*E) : ℝ)+1/8 := hT.symm ▸ hF
    let U := labelledOpening b T
    have hTU : T<U := by have hh := captured_labelled_advance b T hb hret; dsimp [U]; linarith only [hh.1]
    have hU : b*U=(label (b*T) : ℝ)+1/8 := labelled_opening_identity b T hb
    by_cases hA : InWay a U
    · have hclear := triple_clear b c a T (label (c*E)) hb hc ha hTc hret hA
        (small_old_fit b c a hb ha hcb.le hca.le)
      obtain ⟨V,hUV,hVR,hm⟩ := (pair_last_move_and_clear b a U (label (b*T)) hb ha hU hA).1
      have hR : reboundEnd a b c C=partnerEnd b a U := by
        change (if InWay a F then _ else if InWay a U then partnerEnd b a U else U)=partnerEnd b a U
        rw [if_neg hr,if_pos hA]
      rw [hR]
      refine ⟨{b,a},V,?_,hCE.le.trans (hET.le.trans (hTU.le.trans hUV)),hVR,hm,?_⟩
      · intro d hd; simp only [Finset.mem_insert,Finset.mem_singleton] at hd ⊢; tauto
      · have hclear' : LonelyAt ({b,c,a} : Finset ℝ) (partnerEnd b a U) := hclear
        exact three_clear a b c _ (not_lt.mpr (hclear' _ (by simp)))
          (not_lt.mpr (hclear' _ (by simp))) (not_lt.mpr (hclear' _ (by simp)))
    · have hR : reboundEnd a b c C=U := by
        change (if InWay a F then _ else if InWay a U then _ else U)=U
        rw [if_neg hr,if_neg hA]
      have hcs := own_opening_retained b c T U (label (b*T)) (label (c*E)) hb hc.le
        (by linarith only [hcb,hb]) hTc hret hU rfl
      rw [hR]
      refine ⟨{b},T,?_,hCE.le.trans hET.le,hTU,singleton_captured_move b T hret,?_⟩
      · intro d hd; rw [Finset.mem_singleton.mp hd]; simp
      · exact three_clear a b c U hA
          (not_lt.mpr (clear_of_window _ hU.ge (by linarith only [hU])))
          (not_lt.mpr (clear_of_window _ hcs.1 hcs.2.le))

theorem forced_triple_resolution (a b c C : ℝ) (M : ℤ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hab : 3*b<a) (ho : b*C=(M : ℝ)+1/8) (hw : InWay a C)
    (hthird : InWay c (labelledOpening a C)) :
    ∃ (H : Finset ℝ) (U : ℝ), H ⊆ {a,b,c} ∧ C ≤ U ∧ U<forcedEnd a b c C ∧
      IsMove H U (forcedEnd a b c C) ∧ LonelyAt ({a,b,c} : Finset ℝ) (forcedEnd a b c C) := by
  by_cases hret : InWay b (thirdEnd a c C)
  · rw [forcedEnd,if_pos hret]
    exact rebound_resolution a b c C M ha hb hc hab ho hw hthird hret
  · have hinfo := pair_last_move_and_clear a c (labelledOpening a C) (label (a*C)) ha hc
      (labelled_opening_identity a C ha) hthird
    obtain ⟨U,hEU,hUR,hm⟩ := hinfo.1
    have hCE : C<labelledOpening a C := by have hh := captured_labelled_advance a C ha hw; linarith only [hh.1]
    rw [forcedEnd,if_neg hret]
    refine ⟨{a,c},U,?_,hCE.le.trans hEU,hUR,hm,?_⟩
    · intro d hd; simp only [Finset.mem_insert,Finset.mem_singleton] at hd ⊢; tauto
    · exact three_clear a b c _ (not_lt.mpr (hinfo.2 _ (by simp))) hret
        (not_lt.mpr (hinfo.2 _ (by simp)))

-- Independent third speeds with these labels coalesce to one rebound
-- endpoint even though their earlier opening times differ.
theorem anchor_rebound_endpoint (a b c C : ℝ) (K : ℤ)
    (hcap : InWay a (labelledOpening c (labelledOpening a C)))
    (hlabel : label (a*labelledOpening c (labelledOpening a C))=K)
    (hret : InWay b (opening a K)) : forcedEnd a b c C=partnerEnd a b (opening a K) := by
  have hT : thirdEnd a c C=opening a K := by
    unfold thirdEnd partnerEnd
    rw [if_pos hcap]
    change opening a (label (a*labelledOpening c (labelledOpening a C)))=opening a K
    rw [hlabel]
  unfold forcedEnd
  rw [hT,if_pos hret]
  unfold reboundEnd
  rw [if_pos hcap,hT]

theorem changed_anchor_rebound_endpoint (a b c C : ℝ) (L : ℤ)
    (hn : ¬InWay a (labelledOpening c (labelledOpening a C)))
    (hcap : InWay b (labelledOpening c (labelledOpening a C)))
    (hlabel : label (b*labelledOpening c (labelledOpening a C))=L) :
    forcedEnd a b c C=(if InWay a (opening b L) then partnerEnd b a (opening b L) else opening b L) := by
  have hT : thirdEnd a c C=labelledOpening c (labelledOpening a C) := by
    unfold thirdEnd partnerEnd
    rw [if_neg hn]
  have hU : labelledOpening b (labelledOpening c (labelledOpening a C))=opening b L := by
    change opening b (label (b*labelledOpening c (labelledOpening a C)))=opening b L
    rw [hlabel]
  unfold forcedEnd
  rw [hT,if_pos hcap]
  unfold reboundEnd
  rw [if_neg hn,hT,hU]

#print axioms anchor_rebound_endpoint
#print axioms changed_anchor_rebound_endpoint

#print axioms small_old_fit
#print axioms three_clear
#print axioms rebound_resolution
#print axioms forced_triple_resolution
end Fresh.NativeThirdReaderRebound
