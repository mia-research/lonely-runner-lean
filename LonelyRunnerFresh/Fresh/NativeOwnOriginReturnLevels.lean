import Fresh.NativeUniformOpeningCells
import Fresh.NativePhaseOriginLevels

/-! Return levels from an explicitly supplied own-clear origin. Labels are
independent; no prior shared-future-opening Cohort or single predecessor
move is assumed. These are local capture-source laws, not termination.
Outside V83 audit/root, pending the next boundary-return integration. -/
namespace Fresh.NativeOwnOriginReturnLevels
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeReturnSurvivors Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeCohortOutsiderRelay
  Fresh.NativeReturnLevelClearance Fresh.FastestCaptureRetention

theorem displacement (s Z T : ℝ) (N : ℤ) (hs : 0 ≤ s) (hZT : Z ≤ T)
    (ho : s*Z=(N : ℝ)+1/8) (hc : InWay s T) :
    (advance s Z T : ℝ)-1/4<s*(T-Z) ∧ s*(T-Z)<(advance s Z T : ℝ) :=
  (capture_from_opening_iff s Z T N hs hZT ho).1 hc

theorem positive_level (s Z T : ℝ) (N : ℤ) (hs : 0 ≤ s) (hZT : Z ≤ T)
    (ho : s*Z=(N : ℝ)+1/8) (hc : InWay s T) : 0<advance s Z T := by
  have hh := displacement s Z T N hs hZT ho hc
  have hlo := mul_nonneg hs (sub_nonneg.mpr hZT)
  have hp : (0 : ℝ)<(advance s Z T : ℝ) := lt_of_le_of_lt hlo hh.2
  exact_mod_cast hp

theorem later_opening (s Z T : ℝ) (N : ℤ) (hs : 0<s) (hZT : Z ≤ T)
    (ho : s*Z=(N : ℝ)+1/8) :
    labelledOpening s T=Z+(advance s Z T : ℝ)/s := by
  have hl := advance_identity s Z T hs.le hZT
  rw [label_at_opening s Z N ho] at hl
  have hlR : (label (s*T) : ℝ)=(N : ℝ)+(advance s Z T : ℝ) := by exact_mod_cast hl
  have hopen := labelled_opening_identity s T hs
  rw [hlR] at hopen
  have hh : labelledOpening s T-Z=(advance s Z T : ℝ)/s := by
    apply (eq_div_iff hs.ne').2
    nlinarith only [hopen,ho]
  linarith only [hh]

theorem ordered_compact (s d Z T : ℝ) (M N : ℤ) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (hZT : Z ≤ T) (hos : s*Z=(M : ℝ)+1/8) (hod : d*Z=(N : ℝ)+1/8)
    (hcs : InWay s T) (hcd : InWay d T)
    (hle : advance s Z T ≤ advance d Z T) : 3*s<4*d := by
  have h1 := displacement s Z T M hs hZT hos hcs
  have h2 := displacement d Z T N hd hZT hod hcd
  have hp := positive_level d Z T N hd hZT hod hcd
  have hAr : (advance s Z T : ℝ) ≤ (advance d Z T : ℝ) := by exact_mod_cast hle
  have hDr : (1 : ℝ) ≤ (advance d Z T : ℝ) := by exact_mod_cast (show 1 ≤ advance d Z T by omega)
  by_contra hn
  have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hn) (sub_nonneg.mpr hZT)
  nlinarith only [h1.2,h2.1,hAr,hDr,hm]

theorem triple_compact (s d Z T : ℝ) (M N : ℤ) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (hZT : Z ≤ T) (hos : s*Z=(M : ℝ)+1/8) (hod : d*Z=(N : ℝ)+1/8)
    (hcs : InWay s T) (hcd : InWay d T)
    (hle : advance s Z T<3*advance d Z T) : s<3*d := by
  have hr : (advance s Z T : ℝ)+1 ≤ 3*(advance d Z T : ℝ) := by
    exact_mod_cast (show advance s Z T+1 ≤ 3*advance d Z T by omega)
  apply Fresh.NativeOrderedReturnLevels.general_phase_compact s d Z T hs hd hZT hcs hcd
  rw [label_at_opening s Z M hos,label_at_opening d Z N hod]
  nlinarith only [hos,hod,hr]

theorem triple_zero {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Z T : ℝ)
    (i g : Fin 8) (M N : ℤ) (hi : i≠k) (hg : g≠k) (hZT : Z ≤ T)
    (hoi : reading v k i*Z=(M : ℝ)+1/8) (hog : reading v k g*Z=(N : ℝ)+1/8)
    (hci : InWay (reading v k i) T) (hcg : InWay (reading v k g) T)
    (hle : advance (reading v k i) Z T<3*advance (reading v k g) Z T)
    (hm : IsMove (disparitySet v k) T (handoffOpening v k T g)) :
    advance (reading v k i) T (handoffOpening v k T g)=0 := by
  have hr := triple_compact (reading v k i) (reading v k g) Z T M N
    (abs_nonneg _) (abs_nonneg _) hZT hoi hog hci hcg hle
  exact captured_ratio_zero hv k T i g hi hg hci hcg hr.le hm

theorem next_capture_source {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) (Z T : ℝ)
    (i g : Fin 8) (M N : ℤ) (hi : i≠k) (hg : g≠k) (hZT : Z ≤ T)
    (hoi : reading v k i*Z=(M : ℝ)+1/8) (hog : reading v k g*Z=(N : ℝ)+1/8)
    (hcg : InWay (reading v k g) T)
    (hm : IsMove (disparitySet v k) T (handoffOpening v k T g))
    (hafter : InWay (reading v k i) (handoffOpening v k T g)) :
    ¬InWay (reading v k i) T ∨ 3*advance (reading v k g) Z T ≤ advance (reading v k i) Z T := by
  by_cases hci : InWay (reading v k i) T
  · apply Or.inr
    apply le_of_not_gt
    intro hle
    have hz := triple_zero hv k Z T i g M N hi hg hZT hoi hog hci hcg hle hm
    exact not_lt_of_ge (nonreturning_clear hv k T _ hm i hi hz) hafter
  · exact Or.inl hci

theorem clear_displacement (s Z T : ℝ) (N : ℤ) (hs : 0 ≤ s) (hZT : Z ≤ T)
    (ho : s*Z=(N : ℝ)+1/8) (hc : ¬InWay s T) :
    (advance s Z T : ℝ) ≤ s*(T-Z) ∧ s*(T-Z) ≤ (advance s Z T : ℝ)+3/4 := by
  have hlo := (clear_from_opening_iff s Z T N hs hZT ho).1 hc
  have hl := advance_identity s Z T hs hZT
  rw [label_at_opening s Z N ho] at hl
  have hlR : (label (s*T) : ℝ)=(N : ℝ)+(advance s Z T : ℝ) := by exact_mod_cast hl
  have hhi := ((entry_interval s T _).1 (label_entry s T)).2
  rw [hlR] at hhi
  exact ⟨hlo,by nlinarith only [ho,hhi]⟩

theorem clear_level_order (s d Z T : ℝ) (M N : ℤ) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (hZT : Z ≤ T) (hos : s*Z=(M : ℝ)+1/8) (hod : d*Z=(N : ℝ)+1/8)
    (hcs : ¬InWay s T) (hcd : InWay d T) :
    advance s Z T<advance d Z T ↔ s<d := by
  have h1 := clear_displacement s Z T M hs hZT hos hcs
  have h2 := displacement d Z T N hd hZT hod hcd
  constructor
  · intro hlt
    have hn : advance s Z T+1 ≤ advance d Z T := by omega
    have hR : (advance s Z T : ℝ)+1 ≤ (advance d Z T : ℝ) := by exact_mod_cast hn
    by_contra hn'
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hn') (sub_nonneg.mpr hZT)
    nlinarith only [h1.2,h2.1,hR,hm]
  · intro hsd
    by_contra hn
    have hle : advance d Z T ≤ advance s Z T := by omega
    have hR : (advance d Z T : ℝ) ≤ (advance s Z T : ℝ) := by exact_mod_cast hle
    have hm := mul_le_mul_of_nonneg_right hsd.le (sub_nonneg.mpr hZT)
    nlinarith only [h1.1,h2.2,hR,hm]

#print axioms clear_displacement
#print axioms clear_level_order

#print axioms displacement
#print axioms positive_level
#print axioms later_opening
#print axioms ordered_compact
#print axioms triple_compact
#print axioms triple_zero
#print axioms next_capture_source
end Fresh.NativeOwnOriginReturnLevels
