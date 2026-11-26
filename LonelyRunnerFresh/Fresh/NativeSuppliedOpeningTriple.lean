import Fresh.NativeThirdReaderRebound

/-! A supplied incoming own-opening event replaces the implicit captured
anchor step. The previous reader's own opening can precede it by a closed
quarter phase, including coincident events. No history budget is used. -/
open Classical
namespace Fresh.NativeSuppliedOpeningTriple
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels
  Fresh.NativeReturnHandoff Fresh.NativeReturnSurvivors Fresh.NativeOneReaderDeformation
  Fresh.NativeOpeningReversal Fresh.NativeThirdReaderRetention Fresh.NativeThirdReaderRebound
  Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def reboundEnd (a b c E : ℝ) : ℝ :=
  if InWay a (labelledOpening c E) then partnerEnd a b (partnerEnd a c E)
  else if InWay a (labelledOpening b (partnerEnd a c E)) then
    partnerEnd b a (labelledOpening b (partnerEnd a c E))
  else labelledOpening b (partnerEnd a c E)
-- STANDING: DEFINITION
noncomputable def exitEnd (a b c E : ℝ) : ℝ :=
  if InWay b (partnerEnd a c E) then reboundEnd a b c E else partnerEnd a c E

theorem supplied_displacement (a c C E : ℝ) (hc : 0<c)
    (hquarter : a*(E-C)≤1/4) (hthird : InWay c E) (ha : 0<a) :
    a*c*(partnerEnd a c E-C)<(a+2*c)/4 := by
  have hi := mul_le_mul_of_nonneg_right hquarter hc.le
  have ht := pair_tail_weighted a c E ha hc hthird
  nlinarith only [hi,ht]

theorem supplied_old_retained (a b c C E : ℝ) (M L : ℤ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (ho : b*C=(M : ℝ)+1/8)
    (hCE : C≤E) (hquarter : a*(E-C)≤1/4) (hE : a*E=(L : ℝ)+1/8)
    (hthird : InWay c E) (hfit : a*b+2*b*c≤3*a*c) :
    (M : ℝ)+1/8≤b*partnerEnd a c E ∧ b*partnerEnd a c E<(M : ℝ)+7/8 := by
  have hET := pair_end_after a c E ha hc L hE hthird
  have hCT := hCE.trans_lt hET
  have hlo := mul_nonneg hb.le (sub_nonneg.mpr hCT.le)
  have ht := supplied_displacement a c C E hc hquarter hthird ha
  have hs := mul_lt_mul_of_pos_left ht hb
  have hu : b*(partnerEnd a c E-C)<3/4 := by
    have hp := mul_pos ha hc
    by_contra hn
    have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hp.le
    nlinarith only [hm,hs,hfit]
  constructor <;> nlinarith only [ho,hlo,hu]

theorem supplied_slow_third (a b c C E : ℝ) (M L : ℤ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hab : 3*b<a)
    (ho : b*C=(M : ℝ)+1/8) (hCE : C≤E) (hquarter : a*(E-C)≤1/4)
    (hE : a*E=(L : ℝ)+1/8) (hthird : InWay c E)
    (hret : InWay b (partnerEnd a c E)) : 7*c<3*b := by
  by_contra hn
  have hf := simple_seven_three_fit a b c ha hc hab (le_of_not_gt hn)
  have hw := supplied_old_retained a b c C E M L ha hb hc ho hCE hquarter hE hthird hf
  exact not_lt_of_ge (clear_of_window M hw.1 hw.2.le) hret

theorem rebound_resolution (a b c C E : ℝ) (M L : ℤ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hab : 3*b<a) (ho : b*C=(M : ℝ)+1/8) (hCE : C≤E) (hquarter : a*(E-C)≤1/4)
    (hE : a*E=(L : ℝ)+1/8) (hthird : InWay c E) (hret : InWay b (partnerEnd a c E)) :
    ∃ (H : Finset ℝ) (U : ℝ), H ⊆ {a,b,c} ∧ C ≤ U ∧ U<reboundEnd a b c E ∧
      IsMove H U (reboundEnd a b c E) ∧ LonelyAt ({a,b,c} : Finset ℝ) (reboundEnd a b c E) := by
  let F := labelledOpening c E
  let T := partnerEnd a c E
  have hET : E<T := pair_end_after a c E ha hc L hE hthird
  have hslow := supplied_slow_third a b c C E M L ha hb hc hab ho hCE hquarter hE hthird hret
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
    have hR : reboundEnd a b c E=partnerEnd a b T := by
      change (if InWay a F then partnerEnd a b T else _)=partnerEnd a b T
      rw [if_pos hr]
    rw [hR]
    refine ⟨{a,b},U,?_,hCE.trans (hET.le.trans hTU),hUR,hm,?_⟩
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
      have hR : reboundEnd a b c E=partnerEnd b a U := by
        change (if InWay a F then _ else if InWay a U then partnerEnd b a U else U)=partnerEnd b a U
        rw [if_neg hr,if_pos hA]
      rw [hR]
      refine ⟨{b,a},V,?_,hCE.trans (hET.le.trans (hTU.le.trans hUV)),hVR,hm,?_⟩
      · intro d hd; simp only [Finset.mem_insert,Finset.mem_singleton] at hd ⊢; tauto
      · have hclear' : LonelyAt ({b,c,a} : Finset ℝ) (partnerEnd b a U) := hclear
        exact three_clear a b c _ (not_lt.mpr (hclear' _ (by simp)))
          (not_lt.mpr (hclear' _ (by simp))) (not_lt.mpr (hclear' _ (by simp)))
    · have hR : reboundEnd a b c E=U := by
        change (if InWay a F then _ else if InWay a U then _ else U)=U
        rw [if_neg hr,if_neg hA]
      have hcs := own_opening_retained b c T U (label (b*T)) (label (c*E)) hb hc.le
        (by linarith only [hcb,hb]) hTc hret hU rfl
      rw [hR]
      refine ⟨{b},T,?_,hCE.trans hET.le,hTU,singleton_captured_move b T hret,?_⟩
      · intro d hd; rw [Finset.mem_singleton.mp hd]; simp
      · exact three_clear a b c U hA
          (not_lt.mpr (clear_of_window _ hU.ge (by linarith only [hU])))
          (not_lt.mpr (clear_of_window _ hcs.1 hcs.2.le))

theorem forced_triple_resolution (a b c C E : ℝ) (M L : ℤ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hab : 3*b<a) (ho : b*C=(M : ℝ)+1/8) (hCE : C≤E) (hquarter : a*(E-C)≤1/4)
    (hE : a*E=(L : ℝ)+1/8) (hthird : InWay c E) :
    ∃ (H : Finset ℝ) (U : ℝ), H ⊆ {a,b,c} ∧ C ≤ U ∧ U<exitEnd a b c E ∧
      IsMove H U (exitEnd a b c E) ∧ LonelyAt ({a,b,c} : Finset ℝ) (exitEnd a b c E) := by
  by_cases hret : InWay b (partnerEnd a c E)
  · rw [exitEnd,if_pos hret]
    exact rebound_resolution a b c C E M L ha hb hc hab ho hCE hquarter hE hthird hret
  · have hinfo := pair_last_move_and_clear a c E L ha hc hE hthird
    obtain ⟨U,hEU,hUR,hm⟩ := hinfo.1
    rw [exitEnd,if_neg hret]
    refine ⟨{a,c},U,?_,hCE.trans hEU,hUR,hm,?_⟩
    · intro d hd; simp only [Finset.mem_insert,Finset.mem_singleton] at hd ⊢; tauto
    · exact three_clear a b c _ (not_lt.mpr (hinfo.2 _ (by simp))) hret
        (not_lt.mpr (hinfo.2 _ (by simp)))


theorem opening_displacement (d U : ℝ) (hd : 0<d) (hw : InWay d U) :
    labelledOpening d U-U<1/(4*d) := by
  have hh := captured_labelled_advance d U hd hw
  apply (lt_div_iff₀ (show 0<4*d by positivity)).2
  nlinarith only [hh.2]

theorem pair_displacement (a c E : ℝ) (ha : 0<a) (hc : 0<c) (hw : InWay c E) :
    partnerEnd a c E-E<1/(4*a)+1/(4*c) := by
  have hh := pair_tail_weighted a c E ha hc hw
  have he : a*c*(1/(4*a)+1/(4*c))=(a+c)/4 := by
    field_simp [ha.ne',hc.ne']
    ring
  by_contra hn
  have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hn) (mul_pos ha hc).le
  linarith only [hm,he,hh]

theorem exit_displacement (a b c E : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hthird : InWay c E) :
    exitEnd a b c E-E<1/(4*c)+1/(2*a)+1/(2*b) := by
  let T := partnerEnd a c E
  let F := labelledOpening c E
  have ht : T-E<1/(4*a)+1/(4*c) := pair_displacement a c E ha hc hthird
  have ha4 : 0<(1 : ℝ)/(4*a) := by positivity
  have hb4 : 0<(1 : ℝ)/(4*b) := by positivity
  have hra : (1 : ℝ)/(2*a)=1/(4*a)+1/(4*a) := by ring
  have hrb : (1 : ℝ)/(2*b)=1/(4*b)+1/(4*b) := by ring
  rw [hra,hrb]
  by_cases hret : InWay b T
  · have he : exitEnd a b c E=reboundEnd a b c E := by
      unfold exitEnd; exact if_pos hret
    rw [he]
    by_cases hcap : InWay a F
    · have hend : reboundEnd a b c E=partnerEnd a b T := by
        change (if InWay a F then partnerEnd a b T else _)=partnerEnd a b T
        rw [if_pos hcap]
      rw [hend]
      have hp := pair_displacement a b T ha hb hret
      linarith only [ht,hp,ha4,hb4]
    · have hT : T=F := by
        change (if InWay a F then labelledOpening a F else F)=F
        rw [if_neg hcap]
      let U := labelledOpening b T
      have hu : U-T<1/(4*b) := opening_displacement b T hb hret
      by_cases hA : InWay a U
      · have hend : reboundEnd a b c E=partnerEnd b a U := by
          change (if InWay a F then _ else if InWay a U then partnerEnd b a U else U)=partnerEnd b a U
          rw [if_neg hcap,if_pos hA]
        rw [hend]
        have hp := pair_displacement b a U hb ha hA
        linarith only [ht,hu,hp]
      · have hend : reboundEnd a b c E=U := by
          change (if InWay a F then _ else if InWay a U then _ else U)=U
          rw [if_neg hcap,if_neg hA]
        rw [hend]
        linarith only [ht,hu,ha4,hb4]
  · have he : exitEnd a b c E=T := by
      unfold exitEnd; exact if_neg hret
    rw [he]
    linarith only [ht,ha4,hb4]

theorem exit_before_quiet_closing (a b c E : ℝ)
    (ha : 33/8≤a) (hb : 7/8<b) (hc : 7/10<c) (hE : E≤5/4)
    (hthird : InWay c E) : exitEnd a b c E<7/3 := by
  have hap : 0<a := by linarith only [ha]
  have hbp : 0<b := by linarith only [hb]
  have hcp : 0<c := by linarith only [hc]
  have hd := exit_displacement a b c E hap hbp hcp hthird
  have hia : (1 : ℝ)/(2*a)≤4/33 := by
    apply (div_le_iff₀ (show 0<2*a by positivity)).2
    nlinarith only [ha]
  have hib : (1 : ℝ)/(2*b)<4/7 := by
    apply (div_lt_iff₀ (show 0<2*b by positivity)).2
    nlinarith only [hb]
  have hic : (1 : ℝ)/(4*c)<5/14 := by
    apply (div_lt_iff₀ (show 0<4*c by positivity)).2
    nlinarith only [hc]
  linarith only [hd,hia,hib,hic,hE]

#print axioms exit_before_quiet_closing

#print axioms opening_displacement
#print axioms pair_displacement
#print axioms exit_displacement

#print axioms supplied_displacement
#print axioms supplied_old_retained
#print axioms supplied_slow_third
#print axioms rebound_resolution
#print axioms forced_triple_resolution
end Fresh.NativeSuppliedOpeningTriple
