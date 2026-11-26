import Fresh.NativeWatcherReturnArrangement

/-! A clear packet through another native pair tail. The original upper
faces retain the packet; recapture forces the opposite phase/return-level
face. No global descent, time bound or bound on independent labels. -/
open Classical
namespace Fresh.NativePacketTailRetention
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeOpeningReversal Fresh.NativeThirdReaderRetention Fresh.NativeResidualReturn
  Fresh.NativeFixedPrefixTransport

noncomputable def tailFace (a c s E : ℝ) : Prop :=
  s*(a+c) ≤ 4*a*c*((label (s*E) : ℝ)+7/8-s*E)

theorem retained_pair_tail (a c s E : ℝ) (N : ℤ) (ha : 0<a) (hc : 0<c) (hs : 0<s)
    (ho : a*E=(N : ℝ)+1/8) (hw : InWay c E) (hclear : ¬InWay s E)
    (hf : tailFace a c s E) :
    (label (s*E) : ℝ)+1/8 ≤ s*partnerEnd a c E ∧
      s*partnerEnd a c E<(label (s*E) : ℝ)+7/8 := by
  have hEP := pair_end_after a c E ha hc N ho hw
  have hlo := le_of_not_gt (fun hh=>hclear ((inWay_iff_lower_not_passed s E).2 hh))
  have hinc := mul_le_mul_of_nonneg_left hEP.le hs.le
  have hb := mul_lt_mul_of_pos_left (pair_tail_weighted a c E ha hc hw) hs
  dsimp [tailFace] at hf
  have hu : (a*c)*(s*partnerEnd a c E)<(a*c)*((label (s*E) : ℝ)+7/8) := by
    nlinarith only [hb,hf]
  exact ⟨hlo.trans hinc,lt_of_mul_lt_mul_left hu (mul_pos ha hc).le⟩

theorem retained_pair_segment (a c s E U : ℝ) (N : ℤ) (ha : 0<a) (hc : 0<c) (hs : 0<s)
    (ho : a*E=(N : ℝ)+1/8) (hw : InWay c E) (hclear : ¬InWay s E)
    (hf : tailFace a c s E) (hEU : E ≤ U) (hUP : U ≤ partnerEnd a c E) :
    ¬InWay s U ∧ label (s*U)=label (s*E) := by
  have hh := retained_pair_tail a c s E N ha hc hs ho hw hclear hf
  have hlo := le_of_not_gt (fun h=>hclear ((inWay_iff_lower_not_passed s E).2 h))
  exact band_at_point s E U (partnerEnd a c E) (label (s*E)) hs.le hEU hUP hlo hh.2.le

theorem recapture_excludes_face (a c s E : ℝ) (N : ℤ) (ha : 0<a) (hc : 0<c) (hs : 0<s)
    (ho : a*E=(N : ℝ)+1/8) (hw : InWay c E) (hclear : ¬InWay s E)
    (hret : InWay s (partnerEnd a c E)) :
    4*a*c*((label (s*E) : ℝ)+7/8-s*E)<s*(a+c) := by
  apply lt_of_not_ge
  intro hh
  have hx := retained_pair_tail a c s E N ha hc hs ho hw hclear hh
  exact not_lt_of_ge (clear_of_window _ hx.1 hx.2.le) hret

theorem recapture_level_face (a c s E : ℝ) (N : ℤ) (ha : 0<a) (hc : 0<c) (hs : 0<s)
    (ho : a*E=(N : ℝ)+1/8) (hw : InWay c E) (hret : InWay s (partnerEnd a c E)) :
    4*a*c*((advance s E (partnerEnd a c E) : ℝ)-1/8-phase s E)<s*(a+c) := by
  have hEP := pair_end_after a c E ha hc N ho hw
  have h1 := mul_lt_mul_of_pos_left (residual_displacement s E _ hs.le hEP.le hret).1 (mul_pos ha hc)
  have h2 := mul_lt_mul_of_pos_left (pair_tail_weighted a c E ha hc hw) hs
  nlinarith only [h1,h2]

theorem multi_recapture_separation (a c s E : ℝ) (N : ℤ) (ha : 0<a) (hc : 0<c) (hs : 0<s)
    (ho : a*E=(N : ℝ)+1/8) (hw : InWay c E) (hclear : ¬InWay s E)
    (hret : InWay s (partnerEnd a c E)) (hm : 2 ≤ advance s E (partnerEnd a c E)) :
    4*a*c<s*(a+c) := by
  have hf := recapture_level_face a c s E N ha hc hs ho hw hret
  have hp := (clear_phase_bounds s E hclear).2
  have hmR : (2 : ℝ) ≤ (advance s E (partnerEnd a c E) : ℝ) := by exact_mod_cast hm
  have hh := mul_nonneg (mul_pos ha hc).le
    (show 0 ≤ (advance s E (partnerEnd a c E) : ℝ)-1/8-phase s E-1 by linarith only [hmR,hp])
  nlinarith only [hf,hh]

theorem first_opening_before_end (a c E : ℝ) (ha : 0<a) :
    labelledOpening c E ≤ partnerEnd a c E := by
  unfold partnerEnd
  split_ifs with hr
  · have hh := captured_labelled_advance a (labelledOpening c E) ha hr
    linarith only [hh.1]
  · exact le_rfl

theorem captured_pair_packet (a c s E : ℝ) (ha : 0<a) (hc : 0<c) (hs : 0<s)
    (hw : InWay c E) (hcap : InWay s E)
    (horder : labelledOpening s E ≤ labelledOpening c E) (hstrip : s*(a+c) ≤ 3*a*c) :
    (label (s*E) : ℝ)+1/8 ≤ s*partnerEnd a c E ∧
      s*partnerEnd a c E<(label (s*E) : ℝ)+7/8 := by
  have hlow := mul_le_mul_of_nonneg_left (horder.trans (first_opening_before_end a c E ha)) hs.le
  rw [labelled_opening_identity s E hs] at hlow
  have hb := mul_lt_mul_of_pos_left (pair_tail_weighted a c E ha hc hw) hs
  have hdelta : s*(partnerEnd a c E-E)<3/4 := by
    by_contra hn
    have hh := mul_le_mul_of_nonneg_left (le_of_not_gt hn) (mul_pos ha hc).le
    nlinarith only [hh,hb,hstrip]
  have hstart := (capture_at_label s E hcap).2
  exact ⟨hlow,by nlinarith only [hdelta,hstart]⟩

noncomputable def retentionFace (a c s E : ℝ) : Prop :=
  tailFace a c s E ∨ (a ≤ 3*c ∧ labelledOpening c E ≤ closing s E)

theorem retained_by_face (a c s E U : ℝ) (N : ℤ) (ha : 0<a) (hc : 0<c) (hs : 0<s)
    (ho : a*E=(N : ℝ)+1/8) (hw : InWay c E) (hclear : ¬InWay s E)
    (hf : retentionFace a c s E) (hEU : E ≤ U) (hUP : U ≤ partnerEnd a c E) :
    ¬InWay s U ∧ label (s*U)=label (s*E) := by
  rcases hf with hf|hf
  · exact retained_pair_segment a c s E U N ha hc hs ho hw hclear hf hEU hUP
  · have he := Fresh.NativeOutsideGroupDisplacement.own_pair_compact_end c a E N hc ha ho hw hf.1
    have hlo := le_of_not_gt (fun hh=>hclear ((inWay_iff_lower_not_passed s E).2 hh))
    have hu := (le_div_iff₀ hs).1 hf.2
    have hu' : s*partnerEnd a c E ≤ (label (s*E) : ℝ)+7/8 := by
      rw [he]
      simpa only [closing,mul_comm] using hu
    exact band_at_point s E U (partnerEnd a c E) (label (s*E)) hs.le hEU hUP hlo hu'

theorem retained_speed_interval (a c lo s hi E U : ℝ) (N K : ℤ)
    (ha : 0<a) (hc : 0<c) (hlo : 0<lo) (hls : lo ≤ s) (hsh : s ≤ hi) (hE : 0 ≤ E)
    (ho : a*E=(N : ℝ)+1/8) (hw : InWay c E) (hclear : ¬InWay lo E)
    (hlabels : label (lo*E)=K ∧ label (hi*E)=K) (hf : retentionFace a c hi E)
    (hEU : E ≤ U) (hUP : U ≤ partnerEnd a c E) : ¬InWay s U ∧ label (s*U)=K := by
  have hlh := hls.trans hsh
  have hhi := hlo.trans_le hlh
  have hhclear := Fresh.NativeCoalescedCaptureRelay.interval_clearance lo hi hi E hlh le_rfl hE
    (hlabels.1.trans hlabels.2.symm) hclear
  have hEP := pair_end_after a c E ha hc N ho hw
  have hlast := retained_by_face a c hi E (partnerEnd a c E) N ha hc hhi ho hw hhclear hf hEP.le le_rfl
  have hu := ((entry_interval hi (partnerEnd a c E) _).1 (label_entry hi (partnerEnd a c E))).2
  rw [hlast.2,hlabels.2] at hu
  have hloE := le_of_not_gt (fun hh=>hclear ((inWay_iff_lower_not_passed lo E).2 hh))
  rw [hlabels.1] at hloE
  exact interval_band_at_point lo s hi E U (partnerEnd a c E) K hlo hls hsh hE hEU hUP hloE hu

theorem opening_record_until_opening (b S A : ℝ) (hb : 0<b)
    (hSA : S ≤ A) (hAB : A ≤ labelledOpening b S) : labelledOpening b A=labelledOpening b S := by
  have hid := labelled_opening_identity b S hb
  have hlabelB := Fresh.NativeCohortOutsiderRelay.label_at_opening b (labelledOpening b S) (label (b*S)) hid
  have hh := Fresh.NativeCoalescedCaptureRelay.label_between (b*S) (b*A) (b*labelledOpening b S)
    (mul_le_mul_of_nonneg_left hSA hb.le) (mul_le_mul_of_nonneg_left hAB hb.le) hlabelB.symm
  have hlabelA := hh.trans hlabelB
  simp only [labelledOpening,hlabelA]

theorem ordered_return_openings_coalesce (a b S : ℝ) (ha : 0<a) (hb : 0<b)
    (hwa : InWay a S) (hwb : InWay b S)
    (horder : labelledOpening a S<labelledOpening b S) (hcompact : a ≤ 3*b) :
    partnerEnd a b (labelledOpening a S)=labelledOpening b S := by
  have hSA := (captured_labelled_advance a S ha hwa).1
  have hSA' : S ≤ labelledOpening a S := by linarith only [hSA]
  have hcap : InWay b (labelledOpening a S) := by
    apply inWay_until_opening hb hwb hSA'
    rw [captured_opening b S hwb]
    exact horder
  have he := Fresh.NativeOutsideGroupDisplacement.own_pair_compact_end b a (labelledOpening a S)
    (label (a*S)) hb ha (labelled_opening_identity a S ha) hcap hcompact
  exact he.trans (opening_record_until_opening b S (labelledOpening a S) hb hSA' horder.le)

#print axioms opening_record_until_opening
#print axioms ordered_return_openings_coalesce

#print axioms retained_speed_interval

#print axioms retained_by_face

#print axioms first_opening_before_end
#print axioms captured_pair_packet

#print axioms retained_pair_tail
#print axioms retained_pair_segment
#print axioms recapture_excludes_face
#print axioms recapture_level_face
#print axioms multi_recapture_separation
end Fresh.NativePacketTailRetention
