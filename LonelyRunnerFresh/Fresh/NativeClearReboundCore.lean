import Fresh.NativeClearWindowRebound
import Fresh.NativeRelativeCapture

/-! A supplied native core fragment. Its old reader opening order is
explicit; no full-arrangement IsMove premise survives insertion of outsiders.
The core's returned boundary is derived from native capture windows. -/
namespace Fresh.NativeClearReboundCore
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeClearWindowRebound Fresh.NativeTwoSetterPacket
  Fresh.NativeCoalescedCaptureRelay Fresh.FastestCaptureRetention Fresh.NativeOpeningReversal

theorem first_window (g s R : ℝ) (hg : 0 < g) (hs : 0 < s)
    (hr : 3*s ≤ 5*g) (hwg : InWay g R) (hws : InWay s R)
    (horder : labelledOpening s R ≤ labelledOpening g R) :
    (label (s*R) : ℝ)+1/8  ≤  s*labelledOpening g R  ∧ 
      s*labelledOpening g R  <  (label (s*R) : ℝ)+7/8 := by
  have hgown := labelled_opening_identity g R hg
  have hsown := labelled_opening_identity s R hs
  have hc := capture_at_label g R hwg
  have hmul := mul_le_mul_of_nonneg_left horder (mul_pos hg hs).le
  have hcross : g*((label (s*R) : ℝ)+1/8) ≤ s*((label (g*R) : ℝ)+1/8) := by
    have h1 := congrArg (fun z : ℝ=>g*z) hsown
    have h2 := congrArg (fun z : ℝ=>s*z) hgown
    nlinarith only [hmul,h1,h2]
  exact Fresh.NativeRelativeCapture.captured_window g s R _ _ _ hg
    (by linarith only [hr,hg]) hgown hc.1 hc.2 (capture_at_label s R hws).2 hcross

theorem recapture_label_rises (s T U : ℝ) (K : ℤ) (hs : 0 < s) (htu : T ≤ U)
    (hlo : (K : ℝ)+1/8 ≤ s*T) (hw : InWay s U) : K < label (s*U) := by
  have hmono := mul_le_mul_of_nonneg_left htu hs.le
  have hcap := (capture_at_label s U hw).2
  by_contra hn
  have hh : (label (s*U) : ℝ) ≤ (K : ℝ) := by exact_mod_cast le_of_not_gt hn
  linarith only [hlo,hmono,hcap,hh]

theorem recapture_fast (g j s R : ℝ) (hg : 0 < g) (hj : 0 < j) (hs : 0 < s)
    (hsg : 3*s ≤ 5*g) (hgj : 3*g ≤ 5*j) (hjg : 3*j ≤ 5*g)
    (hwg : InWay g R) (hwj : InWay j (labelledOpening g R)) (hws : InWay s R)
    (horder : labelledOpening s R ≤ labelledOpening g R)
    (hret : InWay s (labelledOpening j (labelledOpening g R))) : g < s  ∧  j < s := by
  have hx := captured_labelled_advance g R hg hwg
  have hy := captured_labelled_advance j (labelledOpening g R) hj hwj
  have hwin := first_window g s R hg hs hsg hwg hws horder
  have hlabel := recapture_label_rises s _ _ (label (s*R)) hs (by linarith only [hy.1]) hwin.1 hret
  have hlabelR : (label (s*R) : ℝ)+1 ≤ (label (s*labelledOpening j (labelledOpening g R)) : ℝ) := by
    exact_mod_cast (show label (s*R)+1≤label (s*labelledOpening j (labelledOpening g R)) by omega)
  have hlow := (capture_at_label s _ hret).1
  have hface : ¬s*(g+j) ≤ 3*g*j := by
    intro hf
    have hstep := two_deficits_upper g j s _ _ hg hj hs.le hx.2 hy.2 hf
    have he := (capture_at_label s R hws).2
    nlinarith only [hstep,he,hlow,hlabelR]
  have hn : ¬(s ≤ g ∨ s ≤ j) := fun hle=>hface (below_selected_face s g j hg hj hgj hjg hle)
  exact ⟨lt_of_not_ge (fun hh=>hn (Or.inl hh)),lt_of_not_ge (fun hh=>hn (Or.inr hh))⟩

theorem core_clear (g j s R : ℝ) (hg : 0 < g) (hj : 0 < j) (hs : 0 < s)
    (hsg : 3*s ≤ 5*g) (hgj : 3*g ≤ 5*j) (hjg : 3*j ≤ 5*g)
    (hwg : InWay g R) (hwj : InWay j (labelledOpening g R)) (hws : InWay s R)
    (horder : labelledOpening s R ≤ labelledOpening g R)
    (hret : InWay s (labelledOpening j (labelledOpening g R))) :
    LonelyAt ({g,j,s} : Finset ℝ) (labelledOpening s (labelledOpening j (labelledOpening g R))) := by
  have hfast := recapture_fast g j s R hg hj hs hsg hgj hjg hwg hwj hws horder hret
  have h1 := mul_le_mul_of_nonneg_right hgj hs.le
  have h2 := mul_le_mul_of_nonneg_right hfast.1.le hj.le
  have hprod := mul_pos hj hs
  have hfit : g*(j+s) ≤ 3*j*s := by nlinarith only [h1,h2,hprod]
  have hgclear := own_two_window j s g (labelledOpening g R) (label (g*R)) hj hs hg
    (labelled_opening_identity g R hg) hwj hret hfit
  have hjclear := own_opening_retained s j (labelledOpening j (labelledOpening g R))
    (labelledOpening s (labelledOpening j (labelledOpening g R)))
    (label (s*labelledOpening j (labelledOpening g R))) (label (j*labelledOpening g R))
    hs hj.le (by linarith only [hfast.2,hs]) (labelled_opening_identity j _ hj) hret
    (labelled_opening_identity s _ hs) rfl
  have hsown := labelled_opening_identity s (labelledOpening j (labelledOpening g R)) hs
  intro d hd
  simp only [Finset.mem_insert,Finset.mem_singleton] at hd
  rcases hd with rfl|rfl|rfl
  · exact clear_of_window _ hgclear.1 hgclear.2.le
  · exact clear_of_window _ hjclear.1 hjclear.2.le
  · exact clear_of_window _ hsown.ge (by linarith only [hsown])

#print axioms first_window
#print axioms recapture_label_rises
#print axioms recapture_fast
#print axioms core_clear
end Fresh.NativeClearReboundCore
