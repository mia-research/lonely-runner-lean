import Fresh.NativeReversalReadingCoalescence

/-! Branch-specific native phase faces. Composed fit forces the direct pair
branch; the rebound uses its existing weighted face. These are local opening
displacements, with no global budget or supplied terminal-clear guard. -/
open Classical
namespace Fresh.NativeReversalBranchFaces
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeOpeningReversal Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeSuppliedOpeningTriple
  Fresh.NativeOutsideGroupDisplacement Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def weight (a b c : ℝ) : ℝ := (a*b+a*c+2*b*c)/(4*a*b)
-- STANDING: DEFINITION
noncomputable def phase (a b c E : ℝ) : ℝ :=
  if InWay b (partnerEnd a c E) then weight a b c else 1/3
-- STANDING: DEFINITION
noncomputable def Face (q c E : ℝ) (J : ℤ) (r : ℝ) : Prop :=
  (J : ℝ)+1/8 ≤ q*E ∧ q*r ≤ c*((J : ℝ)+7/8-q*E)

theorem fit_exit (a b c C E : ℝ) (M L : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ho : b*C=(M : ℝ)+1/8) (hCE : C ≤ E) (hquarter : a*(E-C) ≤ 1/4)
    (hE : a*E=(L : ℝ)+1/8) (hthird : InWay c E) (hfit : a*b+2*b*c ≤ 3*a*c) :
    exitEnd a b c E=partnerEnd a c E ∧ phase a b c E=1/3 := by
  have hh := supplied_old_retained a b c C E M L ha hb hc ho hCE hquarter hE hthird hfit
  have hn : ¬InWay b (partnerEnd a c E) := not_lt.mpr (clear_of_window M hh.1 hh.2.le)
  simp only [exitEnd,phase,if_neg hn,and_self]

theorem simple_fit_exit (a b c C E : ℝ) (M L : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : 3*b < a) (ho : b*C=(M : ℝ)+1/8) (hCE : C ≤ E) (hquarter : a*(E-C) ≤ 1/4)
    (hE : a*E=(L : ℝ)+1/8) (hthird : InWay c E) (hsimple : 3*b ≤ 7*c) :
    exitEnd a b c E=partnerEnd a c E ∧ phase a b c E=1/3 :=
  fit_exit a b c C E M L ha hb hc ho hCE hquarter hE hthird
    (simple_seven_three_fit a b c ha hc hab hsimple)

theorem phase_positive (a b c E : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < phase a b c E := by
  unfold phase
  split
  · unfold weight; positivity
  · norm_num

theorem entry_phase (a b c C E : ℝ) (M L : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : 3*b < a) (ho : b*C=(M : ℝ)+1/8) (hCE : C ≤ E) (hquarter : a*(E-C) ≤ 1/4)
    (hE : a*E=(L : ℝ)+1/8) (hthird : InWay c E) :
    phase a b c E < 3/7 ∧ c*(exitEnd a b c E-E) < phase a b c E := by
  by_cases hr : InWay b (partnerEnd a c E)
  · have hh := Fresh.NativeSuppliedOpeningGroup.rebound_tail_displacement a b c E ha hb hc hab hthird hr
    have hs := supplied_slow_third a b c C E M L ha hb hc hab ho hCE hquarter hE hthird hr
    have hca : 7*c < a := hs.trans hab
    have h1 := mul_lt_mul_of_pos_left hs ha
    have h2 := mul_lt_mul_of_pos_right hca hb
    have hpoly : 7*(a*b+a*c+2*b*c) < 12*a*b := by nlinarith only [h1,h2]
    rw [phase,if_pos hr,exitEnd,if_pos hr]
    constructor
    · unfold weight
      apply (div_lt_iff₀ (show 0 < 4*a*b by positivity)).2
      nlinarith only [hpoly]
    · unfold weight
      apply (lt_div_iff₀ (show 0 < 4*a*b by positivity)).2
      nlinarith only [hh.2]
  · rw [phase,if_neg hr,exitEnd,if_neg hr]
    exact ⟨by norm_num,(direct_tail_displacement a c E L ha hc hE hthird).2⟩

theorem retained_window (q c E F r : ℝ) (J : ℤ) (hq : 0 < q) (hc : 0 < c)
    (hEF : E ≤ F) (hphase : c*(F-E) < r) (hface : Face q c E J r) :
    (J : ℝ)+1/8 ≤ q*F ∧ q*F < (J : ℝ)+7/8 := by
  have hlo := mul_nonneg hq.le (sub_nonneg.mpr hEF)
  have ht := mul_lt_mul_of_pos_left hphase hq
  refine ⟨by nlinarith only [hlo,hface.1],?_⟩
  by_contra hn
  have hu := mul_nonneg hc.le (show 0 ≤ q*F-((J : ℝ)+7/8) by linarith only [hn])
  nlinarith only [ht,hface.2,hu]

theorem captured_window (s c E F r : ℝ) (hs : 0 < s) (hc : 0 < c)
    (hcap : InWay s E) (hphase : c*(F-E) < r)
    (hfirst : labelledOpening c E ≤ F) (horder : labelledOpening s E ≤ labelledOpening c E)
    (hstrip : s*r ≤ 3*c/4) :
    (label (s*E) : ℝ)+1/8 ≤ s*F ∧ s*F < (label (s*E) : ℝ)+7/8 := by
  have hlo := mul_le_mul_of_nonneg_left (horder.trans hfirst) hs.le
  rw [labelled_opening_identity s E hs] at hlo
  have ht := mul_lt_mul_of_pos_left hphase hs
  have hstart := (capture_at_label s E hcap).2
  refine ⟨hlo,?_⟩
  have hprod := mul_pos hc (show 0 < (label (s*E) : ℝ)+1/8-s*E by linarith only [hstart])
  by_contra hn
  have hu := mul_nonneg hc.le (show 0 ≤ s*F-((label (s*E) : ℝ)+7/8) by linarith only [hn])
  nlinarith only [ht,hstrip,hprod,hu]

theorem coarse_face (q c E r : ℝ) (J : ℤ) (hq : 0 ≤ q) (hr : r ≤ 3/7)
    (h : Fresh.NativeSuppliedRetainedWindow.Face q c E J) : Face q c E J r := by
  have hm := mul_le_mul_of_nonneg_left hr hq
  exact ⟨h.1,by nlinarith only [hm,h.2]⟩

theorem coarse_strip (s c r : ℝ) (hs : 0 ≤ s) (hr : r ≤ 3/7) (h : 4*s ≤ 7*c) :
    s*r ≤ 3*c/4 := by
  have hm := mul_le_mul_of_nonneg_left hr hs
  nlinarith only [hm,h]

#print axioms fit_exit
#print axioms simple_fit_exit
#print axioms phase_positive
#print axioms entry_phase
#print axioms retained_window
#print axioms captured_window
#print axioms coarse_face
#print axioms coarse_strip
end Fresh.NativeReversalBranchFaces
