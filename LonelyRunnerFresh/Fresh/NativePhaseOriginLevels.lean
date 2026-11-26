import Fresh.NativeUpperGridPacket
import Fresh.NativeOrderedReturnLevels

/-! Common capture phase at a supplied origin, with independent labels.
The later return levels are unbounded. These ordered-level discharges need
no shared own opening and no single predecessor move from the origin. -/
namespace Fresh.NativePhaseOriginLevels
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeUpperGridPacket
  Fresh.NativeReturnLevelClearance Fresh.FastestCaptureRetention

theorem displacement (s W T t : ℝ) (N : ℤ) (hs : 0 ≤ s) (hWT : W ≤ T)
    (ht : 0<t) (ht' : t<1/4) (ho : s*W=(N : ℝ)-1/8+t) (hw : InWay s T) :
    (advance s W T : ℝ)-t<s*(T-W) ∧ s*(T-W)<(advance s W T : ℝ)+1/4-t := by
  have hl := (phase_capture_label s W t N ht ht' ho).1
  have hi := advance_identity s W T hs hWT
  rw [hl] at hi
  have hiR : (label (s*T) : ℝ)=(N : ℝ)+(advance s W T : ℝ) := by exact_mod_cast hi
  have hc := capture_at_label s T hw
  rw [hiR] at hc
  constructor <;> nlinarith only [ho,hc.1,hc.2]

theorem positive_after_own (s W T : ℝ) (hs : 0<s) (hWT : W ≤ T)
    (hown : labelledOpening s W ≤ T) (hw : InWay s T) : 0<advance s W T := by
  have ho := labelled_opening_identity s W hs
  have hlo := mul_le_mul_of_nonneg_left hown hs.le
  have hc := (capture_at_label s T hw).2
  have hi := advance_identity s W T hs.le hWT
  have ha : label (s*W)<label (s*T) := by
    by_contra hn
    have hr : (label (s*T) : ℝ) ≤ (label (s*W) : ℝ) := by exact_mod_cast le_of_not_gt hn
    nlinarith only [ho,hlo,hc,hr]
  omega

theorem later_opening (s W T t : ℝ) (N : ℤ) (hs : 0<s) (hWT : W ≤ T)
    (ht : 0<t) (ht' : t<1/4) (ho : s*W=(N : ℝ)-1/8+t) :
    labelledOpening s T=W+((advance s W T : ℝ)+1/4-t)/s := by
  have hl := (phase_capture_label s W t N ht ht' ho).1
  have hi := advance_identity s W T hs.le hWT
  rw [hl] at hi
  have hiR : (label (s*T) : ℝ)=(N : ℝ)+(advance s W T : ℝ) := by exact_mod_cast hi
  have hopen := labelled_opening_identity s T hs
  rw [hiR] at hopen
  have hh : labelledOpening s T-W=((advance s W T : ℝ)+1/4-t)/s := by
    apply (eq_div_iff hs.ne').2
    nlinarith only [hopen,ho]
  linarith only [hh]

theorem ordered_four_three (s d X t : ℝ) (m n : ℕ) (hX : 0 ≤ X) (ht : t<1/4)
    (hmn : m ≤ n) (hn : 0<n) (hs : s*X<(m : ℝ)+1/4-t) (hd : (n : ℝ)-t<d*X) :
    3*s<4*d := by
  have hmR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  by_contra hh
  have hx := mul_le_mul_of_nonneg_right (le_of_not_gt hh) hX
  nlinarith only [hs,hd,hx,ht,hmR,hnR]

theorem ordered_sharp (s d X t : ℝ) (m n : ℕ) (hX : 0 ≤ X) (ht : t ≤ 7/64)
    (hmn : m ≤ n) (hn : 0<n) (hs : s*X<(m : ℝ)+1/4-t) (hd : (n : ℝ)-t<d*X) :
    57*s<73*d := by
  have hmR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  by_contra hh
  have hx := mul_le_mul_of_nonneg_right (le_of_not_gt hh) hX
  nlinarith only [hs,hd,hx,ht,hmR,hnR]

theorem ordered_compact (s d W T t : ℝ) (M N : ℤ) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (hWT : W ≤ T) (ht : 0<t) (ht' : t<1/4)
    (hos : s*W=(M : ℝ)-1/8+t) (hod : d*W=(N : ℝ)-1/8+t)
    (hws : InWay s T) (hwd : InWay d T)
    (hle : advance s W T ≤ advance d W T) (hpos : 0<advance d W T) : 3*s<4*d := by
  have h1 := displacement s W T t M hs hWT ht ht' hos hws
  have h2 := displacement d W T t N hd hWT ht ht' hod hwd
  exact ordered_four_three s d (T-W) t _ _ (sub_nonneg.mpr hWT) ht' hle hpos h1.2 h2.1

theorem ordered_zero {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (W T t : ℝ)
    (i g : Fin 8) (M N : ℤ) (hi : i≠k) (hg : g≠k) (hWT : W ≤ T)
    (ht : 0<t) (ht' : t<1/4)
    (hoi : reading v k i*W=(M : ℝ)-1/8+t) (hog : reading v k g*W=(N : ℝ)-1/8+t)
    (hwi : InWay (reading v k i) T) (hwg : InWay (reading v k g) T)
    (hle : advance (reading v k i) W T ≤ advance (reading v k g) W T)
    (hpos : 0<advance (reading v k g) W T)
    (hm : IsMove (disparitySet v k) T (handoffOpening v k T g)) :
    advance (reading v k i) T (handoffOpening v k T g)=0 := by
  have hr := ordered_compact (reading v k i) (reading v k g) W T t M N
    (show 0 ≤ reading v k i from abs_nonneg _) (show 0 ≤ reading v k g from abs_nonneg _)
    hWT ht ht' hoi hog hwi hwg hle hpos
  have hd : 0<reading v k g := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨g,hg,rfl⟩)
  exact captured_ratio_zero hv k T i g hi hg hwi hwg (by linarith only [hr,hd]) hm

theorem next_capture_source {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (W T t : ℝ)
    (i g : Fin 8) (M N : ℤ) (hi : i≠k) (hg : g≠k) (hWT : W ≤ T)
    (ht : 0<t) (ht' : t<1/4)
    (hoi : reading v k i*W=(M : ℝ)-1/8+t) (hog : reading v k g*W=(N : ℝ)-1/8+t)
    (hwg : InWay (reading v k g) T) (hpos : 0<advance (reading v k g) W T)
    (hm : IsMove (disparitySet v k) T (handoffOpening v k T g))
    (hafter : InWay (reading v k i) (handoffOpening v k T g)) :
    ¬InWay (reading v k i) T ∨ advance (reading v k g) W T<advance (reading v k i) W T := by
  by_cases hwi : InWay (reading v k i) T
  · apply Or.inr
    apply lt_of_not_ge
    intro hle
    have hz := ordered_zero hv k W T t i g M N hi hg hWT ht ht' hoi hog hwi hwg hle hpos hm
    exact not_lt_of_ge (nonreturning_clear hv k T _ hm i hi hz) hafter
  · exact Or.inl hwi

theorem triple_level_compact (s d W T t : ℝ) (M N : ℤ) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (hWT : W ≤ T) (ht : 0<t) (ht' : t<1/4)
    (hos : s*W=(M : ℝ)-1/8+t) (hod : d*W=(N : ℝ)-1/8+t)
    (hws : InWay s T) (hwd : InWay d T)
    (hle : advance s W T<3*advance d W T) : s<3*d := by
  have hls := (phase_capture_label s W t M ht ht' hos).1
  have hld := (phase_capture_label d W t N ht ht' hod).1
  have hnat : advance s W T+1 ≤ 3*advance d W T := by omega
  have hr : (advance s W T : ℝ)+1 ≤ 3*(advance d W T : ℝ) := by exact_mod_cast hnat
  apply Fresh.NativeOrderedReturnLevels.general_phase_compact s d W T hs hd hWT hws hwd
  rw [hls,hld]
  linarith only [hos,hod,hr,ht']

theorem triple_level_zero {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (W T t : ℝ)
    (i g : Fin 8) (M N : ℤ) (hi : i≠k) (hg : g≠k) (hWT : W ≤ T)
    (ht : 0<t) (ht' : t<1/4)
    (hoi : reading v k i*W=(M : ℝ)-1/8+t) (hog : reading v k g*W=(N : ℝ)-1/8+t)
    (hwi : InWay (reading v k i) T) (hwg : InWay (reading v k g) T)
    (hle : advance (reading v k i) W T<3*advance (reading v k g) W T)
    (hm : IsMove (disparitySet v k) T (handoffOpening v k T g)) :
    advance (reading v k i) T (handoffOpening v k T g)=0 := by
  have hr := triple_level_compact (reading v k i) (reading v k g) W T t M N
    (show 0 ≤ reading v k i from abs_nonneg _) (show 0 ≤ reading v k g from abs_nonneg _)
    hWT ht ht' hoi hog hwi hwg hle
  exact captured_ratio_zero hv k T i g hi hg hwi hwg hr.le hm

theorem next_capture_triple_source {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (W T t : ℝ)
    (i g : Fin 8) (M N : ℤ) (hi : i≠k) (hg : g≠k) (hWT : W ≤ T)
    (ht : 0<t) (ht' : t<1/4)
    (hoi : reading v k i*W=(M : ℝ)-1/8+t) (hog : reading v k g*W=(N : ℝ)-1/8+t)
    (hwg : InWay (reading v k g) T) (hm : IsMove (disparitySet v k) T (handoffOpening v k T g))
    (hafter : InWay (reading v k i) (handoffOpening v k T g)) :
    ¬InWay (reading v k i) T ∨ 3*advance (reading v k g) W T ≤ advance (reading v k i) W T := by
  by_cases hwi : InWay (reading v k i) T
  · apply Or.inr
    apply le_of_not_gt
    intro hle
    have hz := triple_level_zero hv k W T t i g M N hi hg hWT ht ht' hoi hog hwi hwg hle hm
    exact not_lt_of_ge (nonreturning_clear hv k T _ hm i hi hz) hafter
  · exact Or.inl hwi

theorem sharp_compact (s d W T t : ℝ) (M N : ℤ) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (hWT : W ≤ T) (ht : 0<t) (ht' : t ≤ 7/64)
    (hos : s*W=(M : ℝ)-1/8+t) (hod : d*W=(N : ℝ)-1/8+t)
    (hws : InWay s T) (hwd : InWay d T)
    (hle : advance s W T ≤ advance d W T) (hpos : 0<advance d W T) : 57*s<73*d := by
  have hu : t<1/4 := by linarith only [ht']
  have h1 := displacement s W T t M hs hWT ht hu hos hws
  have h2 := displacement d W T t N hd hWT ht hu hod hwd
  exact ordered_sharp s d (T-W) t _ _ (sub_nonneg.mpr hWT) ht' hle hpos h1.2 h2.1

#print axioms sharp_compact

#print axioms triple_level_compact
#print axioms triple_level_zero
#print axioms next_capture_triple_source

#print axioms displacement
#print axioms positive_after_own
#print axioms later_opening
#print axioms ordered_four_three
#print axioms ordered_sharp
#print axioms ordered_compact
#print axioms ordered_zero
#print axioms next_capture_source
end Fresh.NativePhaseOriginLevels
