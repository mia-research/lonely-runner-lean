import Fresh.NativeResidualReturn

/-! Whole fourth-setter speed bands preserve one returned reader opening.
Compact retention or an independent terminal grid window clears the setter;
the latter permits arbitrary returned/recovered integer labels. -/
open Classical
namespace Fresh.NativeResidualReturnBands
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeOneReaderDeformation Fresh.NativeCoalescedCaptureRelay
  Fresh.NativeThirdReaderRetention Fresh.NativeThirdReaderArrangement Fresh.NativeFixedPrefixTransport
  Fresh.NativeResidualReturn Fresh.NativeOpeningReversal Fresh.FastestCaptureRetention

theorem recaptured_terminal_landing (d g R T : ℝ) (hret : InWay d (labelledOpening g R))
    (hT : labelledOpening d (labelledOpening g R)=T) (hclear : ¬InWay g T) : residualEnd d g R=T := by
  unfold residualEnd partnerEnd
  rw [if_pos hret,hT,if_neg hclear]

theorem interval_return_state (d lo g hi R : ℝ) (M L : ℤ)
    (hd : 0<d) (hlo : 0<lo) (hlg : lo ≤ g) (hgh : g ≤ hi) (hR : 0<R)
    (hloM : label (lo*R)=M) (hhiM : label (hi*R)=M) (hcapHi : InWay hi R)
    (hM : 0 ≤ (M : ℝ)+1/8) (hleft : (L : ℝ)-1/8<d*opening hi M)
    (hright : d*opening lo M<(L : ℝ)+1/8) :
    InWay g R ∧ InWay d (labelledOpening g R) ∧
      labelledOpening d (labelledOpening g R)=opening d L := by
  have hlabel := speed_interval_label lo g hi R hlg hgh hR.le (hloM.trans hhiM.symm)
  rw [hloM] at hlabel
  have hw := speed_interval_capture lo g hi R hlg hgh hR.le (hloM.trans hhiM.symm) hcapHi
  obtain ⟨hown,hdcap,he⟩ := interval_opening_states d lo hi M L hd hlo hM hleft hright g hlg hgh
  have hS : labelledOpening g R=opening g M := by change opening g (label (g*R))=opening g M; rw [hlabel]
  exact ⟨hw,by rw [hS]; exact hdcap,by rw [hS]; exact he⟩

theorem compact_interval_landing (d lo g hi R : ℝ) (M L : ℤ)
    (hd : 0<d) (hlo : 0<lo) (hlg : lo ≤ g) (hgh : g ≤ hi) (hR : 0<R)
    (hclear : ¬InWay d R) (hloM : label (lo*R)=M) (hhiM : label (hi*R)=M)
    (hcapHi : InWay hi R) (hM : 0 ≤ (M : ℝ)+1/8)
    (hleft : (L : ℝ)-1/8<d*opening hi M) (hright : d*opening lo M<(L : ℝ)+1/8)
    (hcompact : hi ≤ 3*d) :
    residualEnd d g R=opening d L ∧ LonelyAt ({d,g} : Finset ℝ) (opening d L) := by
  have hg := hlo.trans_le hlg
  obtain ⟨hw,hret,hT⟩ := interval_return_state d lo g hi R M L hd hlo hlg hgh hR hloM hhiM hcapHi hM hleft hright
  have he := (compact_residual_landing d g R hd hg hret (hgh.trans hcompact)).trans hT
  exact ⟨he,he ▸ (residual_pair_resolution d g R hd hg hclear hw).2⟩

theorem terminal_window_interval_landing (d lo g hi R : ℝ) (M L Q : ℤ)
    (hd : 0<d) (hlo : 0<lo) (hlg : lo ≤ g) (hgh : g ≤ hi) (hR : 0<R)
    (hclear : ¬InWay d R) (hloM : label (lo*R)=M) (hhiM : label (hi*R)=M)
    (hcapHi : InWay hi R) (hM : 0 ≤ (M : ℝ)+1/8)
    (hleft : (L : ℝ)-1/8<d*opening hi M) (hright : d*opening lo M<(L : ℝ)+1/8)
    (hterminalLo : (Q : ℝ)+1/8 ≤ lo*opening d L)
    (hterminalHi : hi*opening d L ≤ (Q : ℝ)+7/8) :
    residualEnd d g R=opening d L ∧ LonelyAt ({d,g} : Finset ℝ) (opening d L) := by
  have hg := hlo.trans_le hlg
  obtain ⟨hw,hret,hT⟩ := interval_return_state d lo g hi R M L hd hlo hlg hgh hR hloM hhiM hcapHi hM hleft hright
  have hRS := (captured_labelled_advance g R hg hw).1
  have hST := (captured_labelled_advance d (labelledOpening g R) hd hret).1
  have hpos : 0<opening d L := by rw [←hT]; linarith only [hR,hRS,hST]
  have hband := interval_band_at_point lo g hi (opening d L) (opening d L) (opening d L) Q
    hlo hlg hgh hpos.le le_rfl le_rfl hterminalLo hterminalHi
  have he := recaptured_terminal_landing d g R (opening d L) hret hT hband.1
  exact ⟨he,he ▸ (residual_pair_resolution d g R hd hg hclear hw).2⟩

#print axioms recaptured_terminal_landing
#print axioms interval_return_state
#print axioms compact_interval_landing
#print axioms terminal_window_interval_landing
end Fresh.NativeResidualReturnBands
