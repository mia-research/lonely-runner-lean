import Fresh.NativeOutsideGroupArrangement

/-! An initially clear reader returns after a captured watcher packet opens.
Its own opening can clear the whole packet, with independent original labels.
The mixed disparity face is local to the two actual captured openings. -/
open Classical
namespace Fresh.NativeWatcherPacketReturn
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeOneReaderDeformation Fresh.NativeOpeningReversal Fresh.NativeThirdReaderRetention Fresh.NativeResidualReturn
  Fresh.NativeCoalescedCaptureRelay Fresh.NativeFixedPrefixTransport

noncomputable def returnOpening (d g R : ℝ) : ℝ := labelledOpening d (labelledOpening g R)

theorem two_opening_displacement (d g R : ℝ) (hd : 0<d) (hg : 0<g)
    (hw : InWay g R) (hret : InWay d (labelledOpening g R)) :
    R<labelledOpening g R ∧ labelledOpening g R<returnOpening d g R ∧
      d*g*(returnOpening d g R-R)<(d+g)/4 := by
  have h1 := captured_labelled_advance g R hg hw
  have h2 := captured_labelled_advance d (labelledOpening g R) hd hret
  have h3 := mul_lt_mul_of_pos_left h1.2 hd
  have h4 := mul_lt_mul_of_pos_left h2.2 hg
  dsimp [returnOpening]
  exact ⟨by linarith only [h1.1],by linarith only [h2.1],by nlinarith only [h3,h4]⟩

theorem selected_mixed_compact (d g : ℝ) (hg : 0<g)
    (h : g*(d+g) ≤ 3*d*g) : g ≤ 2*d := by
  by_contra hn
  have hh := mul_pos hg (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith only [h,hh]

theorem packet_window (d g s R : ℝ) (hd : 0<d) (hg : 0<g) (hs : 0<s)
    (hw : InWay g R) (hret : InWay d (labelledOpening g R)) (hcap : InWay s R)
    (horder : labelledOpening s R ≤ labelledOpening g R)
    (hmixed : s*(d+g) ≤ 3*d*g) :
    (label (s*R) : ℝ)+1/8 ≤ s*returnOpening d g R ∧
      s*returnOpening d g R<(label (s*R) : ℝ)+7/8 := by
  have ht := two_opening_displacement d g R hd hg hw hret
  have hlow := mul_le_mul_of_nonneg_left (horder.trans ht.2.1.le) hs.le
  rw [labelled_opening_identity s R hs] at hlow
  have hscaled := mul_lt_mul_of_pos_left ht.2.2 hs
  have htail : s*(returnOpening d g R-R)<3/4 := by
    by_contra hn
    have hh := mul_le_mul_of_nonneg_left (le_of_not_gt hn) (mul_pos hd hg).le
    nlinarith only [hh,hscaled,hmixed]
  have hstart := (capture_at_label s R hcap).2
  exact ⟨hlow,by nlinarith only [htail,hstart]⟩

theorem packet_segment (d g s R U : ℝ) (hd : 0<d) (hg : 0<g) (hs : 0<s)
    (hw : InWay g R) (hret : InWay d (labelledOpening g R)) (hcap : InWay s R)
    (horder : labelledOpening s R ≤ labelledOpening g R)
    (hmixed : s*(d+g) ≤ 3*d*g)
    (hSU : labelledOpening g R ≤ U) (hUT : U ≤ returnOpening d g R) :
    ¬InWay s U ∧ label (s*U)=label (s*R) := by
  have hh := packet_window d g s R hd hg hs hw hret hcap horder hmixed
  have hlo := mul_le_mul_of_nonneg_left horder hs.le
  rw [labelled_opening_identity s R hs] at hlo
  exact band_at_point s (labelledOpening g R) U (returnOpening d g R)
    (label (s*R)) hs.le hSU hUT hlo hh.2.le

theorem packet_zero (d g s R : ℝ) (hd : 0<d) (hg : 0<g) (hs : 0<s)
    (hw : InWay g R) (hret : InWay d (labelledOpening g R)) (hcap : InWay s R)
    (horder : labelledOpening s R ≤ labelledOpening g R)
    (hmixed : s*(d+g) ≤ 3*d*g) : advance s R (returnOpening d g R)=0 := by
  have hh := packet_window d g s R hd hg hs hw hret hcap horder hmixed
  have hl := (entry_iff_label s (returnOpening d g R) (label (s*R))).1 (Or.inl ⟨hh.1,hh.2.le⟩)
  simp only [advance,hl,sub_self,Int.toNat_zero]

theorem mixed_residual_endpoint (d g R : ℝ) (hd : 0<d) (hg : 0<g)
    (hret : InWay d (labelledOpening g R)) (hmixed : g*(d+g) ≤ 3*d*g) :
    residualEnd d g R=returnOpening d g R := by
  have hh := selected_mixed_compact d g hg hmixed
  exact compact_residual_landing d g R hd hg hret (by nlinarith only [hh,hd])

theorem multi_return_mixed (d g s R : ℝ) (hd : 0<d) (hg : 0<g) (hs : 0 ≤ s)
    (hclear : ¬InWay d R) (hw : InWay g R) (hret : InWay d (labelledOpening g R))
    (hm : 2 ≤ advance d R (labelledOpening g R)) (hstrip : 5*s ≤ 12*g) :
    s*(d+g) ≤ 3*d*g := by
  have hgap := multi_return_speed_gap d g R hd hg hclear hw hret hm
  have h1 := mul_le_mul_of_nonneg_right hstrip (add_pos hd hg).le
  have h2 := mul_pos hg (sub_pos.mpr hgap)
  nlinarith only [h1,h2]

theorem early_phase_mixed (d g s R : ℝ) (hd : 0<d) (hg : 0<g)
    (hclear : ¬InWay d R) (hw : InWay g R) (hret : InWay d (labelledOpening g R))
    (hearly : phase d R ≤ 3/4) (hstrip : s ≤ g) : s*(d+g) ≤ 3*d*g := by
  have ht := captured_labelled_advance g R hg hw
  have hm := clear_recapture_positive d R _ hd (by linarith only [ht.1]) hclear hret
  have hmR : (1 : ℝ) ≤ (advance d R (labelledOpening g R) : ℝ) := by exact_mod_cast hm
  have hf := residual_speed_face d g R hd hg hw hret
  have hh := mul_nonneg hg.le (show 0 ≤ (advance d R (labelledOpening g R) : ℝ)-1/8-phase d R-1/8 by linarith only [hearly,hmR])
  have hgap : g<2*d := by nlinarith only [hf,hh]
  have h1 := mul_le_mul_of_nonneg_right hstrip (add_pos hd hg).le
  have h2 := mul_pos hg (sub_pos.mpr hgap)
  nlinarith only [h1,h2]

theorem packet_interval (d g lo s hi R : ℝ) (K : ℤ)
    (hd : 0<d) (hg : 0<g) (hlo : 0<lo) (hls : lo ≤ s) (hsh : s ≤ hi) (hR : 0<R)
    (hw : InWay g R) (hret : InWay d (labelledOpening g R))
    (hlabels : label (lo*R)=K ∧ label (hi*R)=K) (hcapHi : InWay hi R)
    (hK : 0 ≤ (K : ℝ)+1/8) (hmixed : hi*(d+g) ≤ 3*d*g)
    (horder : Fresh.FastestCaptureRetention.opening lo K ≤ labelledOpening g R) :
    (K : ℝ)+1/8 ≤ s*returnOpening d g R ∧ s*returnOpening d g R<(K : ℝ)+7/8 := by
  have hlabel := speed_interval_label lo s hi R hls hsh hR.le (hlabels.1.trans hlabels.2.symm)
  rw [hlabels.1] at hlabel
  have hcap := speed_interval_capture lo s hi R hls hsh hR.le (hlabels.1.trans hlabels.2.symm) hcapHi
  have hopen := (interval_opening_bounds lo s hi K hlo hls hsh hK).2.trans horder
  have horder' : labelledOpening s R ≤ labelledOpening g R := by
    change Fresh.FastestCaptureRetention.opening s (label (s*R)) ≤ _
    rw [hlabel]
    exact hopen
  have h1 := mul_le_mul_of_nonneg_right hsh (add_pos hd hg).le
  have hh := packet_window d g s R hd hg (hlo.trans_le hls) hw hret hcap horder'
    (h1.trans hmixed)
  simpa only [hlabel] using hh

noncomputable def boundaryFace (d g s R : ℝ) : Prop :=
  s*(d*((label (g*R) : ℝ)+1/8-g*R)+g/4) ≤
    d*g*((label (s*R) : ℝ)+7/8-s*R)

theorem boundary_selected_compact (d g R : ℝ) (hg : 0<g)
    (hface : boundaryFace d g g R) : g ≤ 3*d := by
  dsimp [boundaryFace] at hface
  by_contra hn
  have hh := mul_pos hg (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith only [hface,hh]

theorem boundary_packet_window (d g s R : ℝ) (hd : 0<d) (hg : 0<g) (hs : 0<s)
    (hw : InWay g R) (hret : InWay d (labelledOpening g R))
    (horder : labelledOpening s R ≤ labelledOpening g R) (hface : boundaryFace d g s R) :
    (label (s*R) : ℝ)+1/8 ≤ s*returnOpening d g R ∧
      s*returnOpening d g R<(label (s*R) : ℝ)+7/8 := by
  have ht := two_opening_displacement d g R hd hg hw hret
  have hlow := mul_le_mul_of_nonneg_left (horder.trans ht.2.1.le) hs.le
  rw [labelled_opening_identity s R hs] at hlow
  have hid := congrArg (fun x : ℝ=>d*x) (labelled_opening_identity g R hg)
  have hlast := mul_lt_mul_of_pos_left (captured_labelled_advance d (labelledOpening g R) hd hret).2 hg
  have hweighted : d*g*(returnOpening d g R-R)<
      d*((label (g*R) : ℝ)+1/8-g*R)+g/4 := by
    dsimp [returnOpening]
    nlinarith only [hid,hlast]
  have hscaled := mul_lt_mul_of_pos_left hweighted hs
  dsimp [boundaryFace] at hface
  have hupper : (d*g)*(s*returnOpening d g R)<(d*g)*((label (s*R) : ℝ)+7/8) := by
    nlinarith only [hscaled,hface]
  exact ⟨hlow,lt_of_mul_lt_mul_left hupper (mul_pos hd hg).le⟩

theorem boundary_packet_segment (d g s R U : ℝ) (hd : 0<d) (hg : 0<g) (hs : 0<s)
    (hw : InWay g R) (hret : InWay d (labelledOpening g R))
    (horder : labelledOpening s R ≤ labelledOpening g R) (hface : boundaryFace d g s R)
    (hSU : labelledOpening g R ≤ U) (hUT : U ≤ returnOpening d g R) :
    ¬InWay s U ∧ label (s*U)=label (s*R) := by
  have hh := boundary_packet_window d g s R hd hg hs hw hret horder hface
  have hlo := mul_le_mul_of_nonneg_left horder hs.le
  rw [labelled_opening_identity s R hs] at hlo
  exact band_at_point s (labelledOpening g R) U (returnOpening d g R)
    (label (s*R)) hs.le hSU hUT hlo hh.2.le

theorem mixed_into_boundary (d g s R : ℝ) (hd : 0<d) (hg : 0<g) (hs : 0<s)
    (hw : InWay g R) (hcap : InWay s R) (hmixed : s*(d+g) ≤ 3*d*g) : boundaryFace d g s R := by
  have hstart := capture_at_label g R hw
  have hA : (label (g*R) : ℝ)+1/8-g*R<1/4 := by linarith only [hstart.1]
  have h1 := mul_lt_mul_of_pos_left hA hd
  have h2 := mul_lt_mul_of_pos_left h1 hs
  have h3 := mul_lt_mul_of_pos_left (capture_at_label s R hcap).2 (mul_pos hd hg)
  dsimp [boundaryFace]
  nlinarith only [h2,h3,hmixed]

#print axioms boundary_selected_compact
#print axioms boundary_packet_window
#print axioms boundary_packet_segment
#print axioms mixed_into_boundary

#print axioms two_opening_displacement
#print axioms selected_mixed_compact
#print axioms packet_window
#print axioms packet_segment
#print axioms packet_zero
#print axioms mixed_residual_endpoint
#print axioms multi_return_mixed
#print axioms early_phase_mixed
#print axioms packet_interval
end Fresh.NativeWatcherPacketReturn
