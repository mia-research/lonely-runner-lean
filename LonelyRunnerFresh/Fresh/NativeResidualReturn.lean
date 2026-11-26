import Fresh.NativeThirdReaderForcedArrangement

/-! An initially clear reader may return from any residual phase. The new
setter's own opening transfers the continuation to the native pair family.
An inverse rebound is confined to a late, single-advance phase. No global
move bound or endpoint clearance premise is introduced. -/
open Classical
namespace Fresh.NativeResidualReturn
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeOneReaderDeformation Fresh.NativeFixedPrefixTransport
  Fresh.NativeOpeningReversal Fresh.NativeThirdReaderRetention

noncomputable def phase (d R : ℝ) : ℝ := d*R-(label (d*R) : ℝ)

noncomputable def residualEnd (d g R : ℝ) : ℝ :=
  if InWay d (labelledOpening g R) then partnerEnd g d (labelledOpening g R) else labelledOpening g R

theorem clear_phase_bounds (d R : ℝ) (hc : ¬InWay d R) : 1/8 ≤ phase d R ∧ phase d R ≤ 7/8 := by
  have hlo := le_of_not_gt (fun h=>hc ((inWay_iff_lower_not_passed d R).2 h))
  have hhi := ((entry_interval _ _ _).1 (label_entry d R)).2
  dsimp [phase]
  constructor <;> linarith only [hlo,hhi]

theorem clear_recapture_positive (d R S : ℝ) (hd : 0<d) (hRS : R ≤ S)
    (hc : ¬InWay d R) (hw : InWay d S) : 0<advance d R S := by
  by_contra hn
  have hz : advance d R S=0 := by omega
  have hi := advance_identity d R S hd.le hRS
  rw [hz] at hi
  simp only [Nat.cast_zero,add_zero] at hi
  have hlo := le_of_not_gt (fun h=>hc ((inWay_iff_lower_not_passed d R).2 h))
  have hhi := (inWay_iff_lower_not_passed d S).1 hw
  rw [hi] at hhi
  have hm := mul_le_mul_of_nonneg_left hRS hd.le
  linarith only [hlo,hhi,hm]

theorem residual_displacement (d R S : ℝ) (hd : 0 ≤ d) (hRS : R ≤ S) (hw : InWay d S) :
    (advance d R S : ℝ)-1/8-phase d R<d*(S-R) ∧
      d*(S-R)<(advance d R S : ℝ)+1/8-phase d R := by
  have hi := advance_identity d R S hd hRS
  have hiR : (label (d*S) : ℝ)=(label (d*R) : ℝ)+(advance d R S : ℝ) := by exact_mod_cast hi
  have hh := capture_at_label d S hw
  rw [hiR] at hh
  dsimp [phase]
  constructor <;> nlinarith only [hh.1,hh.2]

theorem residual_speed_face (d g R : ℝ) (hd : 0<d) (hg : 0<g)
    (hwg : InWay g R) (hret : InWay d (labelledOpening g R)) :
    4*g*((advance d R (labelledOpening g R) : ℝ)-1/8-phase d R)<d := by
  have ht := captured_labelled_advance g R hg hwg
  have hRS : R ≤ labelledOpening g R := by linarith only [ht.1]
  have hb := (residual_displacement d R _ hd.le hRS hret).1
  have h1 := mul_lt_mul_of_pos_left hb hg
  have h2 := mul_lt_mul_of_pos_left ht.2 hd
  nlinarith only [h1,h2]

theorem multi_return_speed_gap (d g R : ℝ) (hd : 0<d) (hg : 0<g)
    (hclear : ¬InWay d R) (hwg : InWay g R) (hret : InWay d (labelledOpening g R))
    (hm : 2 ≤ advance d R (labelledOpening g R)) : 4*g<d := by
  have hf := residual_speed_face d g R hd hg hwg hret
  have hp := (clear_phase_bounds d R hclear).2
  have hmR : (2 : ℝ) ≤ (advance d R (labelledOpening g R) : ℝ) := by exact_mod_cast hm
  have hh := mul_nonneg hg.le (show 0 ≤ (advance d R (labelledOpening g R) : ℝ)-1/8-phase d R-1 by linarith only [hp,hmR])
  nlinarith only [hf,hh]

theorem early_phase_compact (d g R : ℝ) (hd : 0<d) (hg : 0<g)
    (hclear : ¬InWay d R) (hwg : InWay g R) (hret : InWay d (labelledOpening g R))
    (hearly : phase d R ≤ 19/24) : g<3*d := by
  have ht := captured_labelled_advance g R hg hwg
  have hm := clear_recapture_positive d R _ hd (by linarith only [ht.1]) hclear hret
  have hmR : (1 : ℝ) ≤ (advance d R (labelledOpening g R) : ℝ) := by exact_mod_cast hm
  have hf := residual_speed_face d g R hd hg hwg hret
  have hh := mul_nonneg hg.le (show 0 ≤ (advance d R (labelledOpening g R) : ℝ)-1/8-phase d R-1/12 by linarith only [hearly,hmR])
  nlinarith only [hf,hh]

theorem inverse_rebound_late_one (d g R : ℝ) (hd : 0<d) (hg : 0<g)
    (hclear : ¬InWay d R) (hwg : InWay g R) (hret : InWay d (labelledOpening g R))
    (hinverse : InWay g (labelledOpening d (labelledOpening g R))) :
    advance d R (labelledOpening g R)=1 ∧ 19/24<phase d R ∧ 3*d<g := by
  have hgap := recapture_forces_three g d (labelledOpening g R)
    (labelledOpening d (labelledOpening g R)) (label (g*R)) (label (d*labelledOpening g R)) hg hd
    (labelled_opening_identity g R hg) hret (labelled_opening_identity d _ hd) rfl hinverse
  have ht := captured_labelled_advance g R hg hwg
  have hm := clear_recapture_positive d R _ hd (by linarith only [ht.1]) hclear hret
  have hone : advance d R (labelledOpening g R)=1 := by
    by_contra hn
    have htwo : 2 ≤ advance d R (labelledOpening g R) := by omega
    have hh := multi_return_speed_gap d g R hd hg hclear hwg hret htwo
    nlinarith only [hh,hgap,hd,hg]
  have hlate : 19/24<phase d R := by
    by_contra hn
    have hh := early_phase_compact d g R hd hg hclear hwg hret (le_of_not_gt hn)
    linarith only [hh,hgap]
  exact ⟨hone,hlate,hgap⟩

theorem residual_first_move (d g R : ℝ) (hd : 0<d) (hg : 0<g)
    (hclear : ¬InWay d R) (hwg : InWay g R) :
    IsMove ({d,g} : Finset ℝ) R (labelledOpening g R) :=
  clear_entry_insert_move (by simpa only [Finset.mem_singleton] using fun x (he : x=g)=>he ▸ hg)
    d R _ hd (singleton_captured_move g R hwg) hclear

theorem residual_pair_resolution (d g R : ℝ) (hd : 0<d) (hg : 0<g)
    (hclear : ¬InWay d R) (hwg : InWay g R) :
    (∃ U,R ≤ U ∧ U<residualEnd d g R ∧ IsMove ({d,g} : Finset ℝ) U (residualEnd d g R)) ∧
      LonelyAt ({d,g} : Finset ℝ) (residualEnd d g R) := by
  have ht := captured_labelled_advance g R hg hwg
  have hRS : R<labelledOpening g R := by linarith only [ht.1]
  by_cases hr : InWay d (labelledOpening g R)
  · have hh := pair_last_move_and_clear g d (labelledOpening g R) (label (g*R)) hg hd
      (labelled_opening_identity g R hg) hr
    obtain ⟨U,hSU,hUE,hm⟩ := hh.1
    rw [Finset.pair_comm] at hm
    rw [residualEnd,if_pos hr]
    refine ⟨⟨U,hRS.le.trans hSU,hUE,hm⟩,?_⟩
    rw [Finset.pair_comm]
    exact hh.2
  · rw [residualEnd,if_neg hr]
    refine ⟨⟨R,le_rfl,hRS,residual_first_move d g R hd hg hclear hwg⟩,?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with he|hx
    · subst x; exact not_lt.mp hr
    · rw [Finset.mem_singleton.mp hx]
      have ho := labelled_opening_identity g R hg
      exact clear_of_window _ ho.ge (by linarith only [ho])

theorem compact_residual_landing (d g R : ℝ) (hd : 0<d) (hg : 0<g)
    (hret : InWay d (labelledOpening g R)) (hcompact : g ≤ 3*d) :
    residualEnd d g R=labelledOpening d (labelledOpening g R) := by
  have hgS := labelled_opening_identity g R hg
  have hdT := labelled_opening_identity d (labelledOpening g R) hd
  have hw := own_opening_retained d g _ _ _ _ hd hg.le hcompact hgS hret hdT rfl
  have hn : ¬InWay g (labelledOpening d (labelledOpening g R)) := not_lt.mpr (clear_of_window _ hw.1 hw.2.le)
  unfold residualEnd partnerEnd
  rw [if_pos hret,if_neg hn]

-- The only inverse branch re-enters the previous fast-anchor triple
-- mechanism with setter/returner roles exchanged.
theorem inverse_three_reader_resolution (d g c R : ℝ) (hd : 0<d) (hg : 0<g) (hc : 0<c)
    (hclear : ¬InWay d R) (hwg : InWay g R) (hret : InWay d (labelledOpening g R))
    (hinverse : InWay g (labelledOpening d (labelledOpening g R)))
    (hthird : InWay c (labelledOpening g (labelledOpening d (labelledOpening g R)))) :
    ∃ (H : Finset ℝ) (U : ℝ), H ⊆ {g,d,c} ∧ labelledOpening d (labelledOpening g R) ≤ U ∧
      U<Fresh.NativeThirdReaderRebound.forcedEnd g d c (labelledOpening d (labelledOpening g R)) ∧
      IsMove H U (Fresh.NativeThirdReaderRebound.forcedEnd g d c (labelledOpening d (labelledOpening g R))) ∧
      LonelyAt ({g,d,c} : Finset ℝ) (Fresh.NativeThirdReaderRebound.forcedEnd g d c (labelledOpening d (labelledOpening g R))) := by
  have hgap := (inverse_rebound_late_one d g R hd hg hclear hwg hret hinverse).2.2
  exact Fresh.NativeThirdReaderRebound.forced_triple_resolution g d c _ _ hg hd hc hgap
    (labelled_opening_identity d _ hd) hinverse hthird

#print axioms inverse_three_reader_resolution

#print axioms clear_phase_bounds
#print axioms clear_recapture_positive
#print axioms residual_displacement
#print axioms residual_speed_face
#print axioms multi_return_speed_gap
#print axioms early_phase_compact
#print axioms inverse_rebound_late_one
#print axioms residual_first_move
#print axioms residual_pair_resolution
#print axioms compact_residual_landing
end Fresh.NativeResidualReturn
