import Fresh.NativePacketRestartExchange

/-! A return immediately following a reader's own opening forces an exact
speed separation. A two-reader reversal then clears both readers at the
next own opening. This is a local boundary family, not a global move bound.
Physical outsider recovery/closing guards remain explicit. -/
open Classical
namespace Fresh.NativeOpeningReversal
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeCohortOutsiderRelay Fresh.NativeReturnClosingOrder
  Fresh.NativeOneReaderDeformation Fresh.NativeCoalescedCaptureRelay
  Fresh.NativeGroupEndpointRecovery Fresh.NativeFixedPrefixArrangement
  Fresh.FastestCaptureRetention

-- Starting exactly at an own opening, positive returns cross its upper face.
theorem opening_recapture_positive (d B C : ℝ) (N : ℤ) (hd : 0<d)
    (hBC : B ≤ C) (ho : d*B=(N : ℝ)+1/8) (hw : InWay d C) : 0<advance d B C := by
  have hb := (capture_from_opening_iff d B C N hd.le hBC ho).1 hw
  have hn := mul_nonneg hd.le (sub_nonneg.mpr hBC)
  have ha : (0 : ℝ)<(advance d B C : ℝ) := lt_of_le_of_lt hn hb.2
  exact_mod_cast ha

theorem recapture_forces_separation (d s B C : ℝ) (N M : ℤ) (hd : 0<d) (hs : 0<s)
    (ho : d*B=(N : ℝ)+1/8) (hw : InWay s B)
    (hc : s*C=(M : ℝ)+1/8) (hM : M=label (s*B)) (hret : InWay d C) :
    (4*(advance d B C : ℝ)-1)*s<d := by
  have hsB := capture_at_label s B hw
  rw [←hM] at hsB
  have ht := Fresh.NativeOpeningRetention.capture_advance s B C M hs hc hsB.1 hsB.2
  have ha := opening_recapture_positive d B C N hd (by linarith only [ht.1]) ho hret
  have haR : (1 : ℝ) ≤ (advance d B C : ℝ) := by exact_mod_cast ha
  have hb := (capture_from_opening_iff d B C N hd.le (by linarith only [ht.1]) ho).1 hret
  have hp : 0<4*(advance d B C : ℝ)-1 := by linarith only [haR]
  have hh := mul_lt_mul_of_pos_left ht.2 hp
  by_contra hn
  have he := mul_le_mul_of_nonneg_right (le_of_not_gt hn) ht.1.le
  nlinarith only [hh,he,hb.1]

theorem recapture_forces_three (d s B C : ℝ) (N M : ℤ) (hd : 0<d) (hs : 0<s)
    (ho : d*B=(N : ℝ)+1/8) (hw : InWay s B)
    (hc : s*C=(M : ℝ)+1/8) (hM : M=label (s*B)) (hret : InWay d C) : 3*s<d := by
  have hh := recapture_forces_separation d s B C N M hd hs ho hw hc hM hret
  have hsB := capture_at_label s B hw
  rw [←hM] at hsB
  have ht := Fresh.NativeOpeningRetention.capture_advance s B C M hs hc hsB.1 hsB.2
  have ha := opening_recapture_positive d B C N hd (by linarith only [ht.1]) ho hret
  have haR : (1 : ℝ) ≤ (advance d B C : ℝ) := by exact_mod_cast ha
  nlinarith only [hh,mul_nonneg (sub_nonneg.mpr haR) hs.le]

theorem own_opening_retained (d s U V : ℝ) (N K : ℤ) (hd : 0<d) (hs : 0  ≤  s)
    (hr : s ≤ 3*d) (hprior : s*U=(K : ℝ)+1/8) (hw : InWay d U)
    (hV : d*V=(N : ℝ)+1/8) (hN : N=label (d*U)) :
    (K : ℝ)+1/8 ≤ s*V ∧ s*V<(K : ℝ)+7/8 := by
  have hb := capture_at_label d U hw
  rw [←hN] at hb
  have ht := Fresh.NativeOpeningRetention.capture_advance d U V N hd hV hb.1 hb.2
  have hlow := mul_nonneg hs ht.1.le
  have hbound := mul_le_mul_of_nonneg_right hr ht.1.le
  constructor <;> nlinarith only [hprior,ht.2,hlow,hbound]

theorem reversal_clears_pair (d s B C D : ℝ) (N M L : ℤ) (hd : 0<d) (hs : 0<s)
    (hB : d*B=(N : ℝ)+1/8) (hw : InWay s B)
    (hC : s*C=(M : ℝ)+1/8) (hM : M=label (s*B)) (hret : InWay d C)
    (hD : d*D=(L : ℝ)+1/8) (hL : L=label (d*C)) :
    ¬InWay d D ∧ ¬InWay s D := by
  have hr := recapture_forces_three d s B C N M hd hs hB hw hC hM hret
  have hsratio : s ≤ 3*d := by nlinarith only [hr,hs]
  have hsc := own_opening_retained d s C D L M hd hs.le hsratio hC hret hD hL
  constructor
  · exact not_lt.mpr (clear_of_window L hD.ge (by linarith only [hD]))
  · exact not_lt.mpr (clear_of_window M hsc.1 hsc.2.le)

noncomputable def partnerEnd (d s B : ℝ) : ℝ :=
  if InWay d (labelledOpening s B) then labelledOpening d (labelledOpening s B) else labelledOpening s B

theorem labelled_opening_identity (s U : ℝ) (hs : 0<s) :
    s*labelledOpening s U=(label (s*U) : ℝ)+1/8 := by
  dsimp [labelledOpening,opening]
  field_simp

theorem singleton_captured_move (s U : ℝ) (hw : InWay s U) :
    IsMove ({s} : Finset ℝ) U (labelledOpening s U) := by
  refine Or.inr ⟨s,Finset.mem_singleton_self _,hw,?_,?_⟩
  · exact (captured_opening s U hw).symm
  · intro d hd hwd
    rw [Finset.mem_singleton.mp hd,captured_opening s U hw]

theorem pair_first_move (d s B : ℝ) (N : ℤ) (hd : 0<d) (hs : 0<s)
    (hB : d*B=(N : ℝ)+1/8) (hw : InWay s B) :
    IsMove ({d,s} : Finset ℝ) B (labelledOpening s B) := by
  exact own_opening_next_move (by simpa only [Finset.mem_singleton] using fun x (he : x=s)=>he ▸ hs)
    d B _ N hd hB (singleton_captured_move s B hw)

theorem pair_last_move_and_clear (d s B : ℝ) (N : ℤ) (hd : 0<d) (hs : 0<s)
    (hB : d*B=(N : ℝ)+1/8) (hw : InWay s B) :
    (∃ U, B ≤ U ∧ U<partnerEnd d s B ∧ IsMove ({d,s} : Finset ℝ) U (partnerEnd d s B)) ∧
    LonelyAt ({d,s} : Finset ℝ) (partnerEnd d s B) := by
  let C := labelledOpening s B
  have hC : s*C=(label (s*B) : ℝ)+1/8 := labelled_opening_identity s B hs
  have hBC : B<C := by simpa only [C,captured_opening s B hw] using lt_nextOpening hs hw
  by_cases hr : InWay d C
  · have hD := labelled_opening_identity d C hd
    have hCD : C<labelledOpening d C := by simpa only [captured_opening d C hr] using lt_nextOpening hd hr
    have hclear := reversal_clears_pair d s B C (labelledOpening d C) N (label (s*B)) (label (d*C)) hd hs hB hw hC rfl hr hD rfl
    have hm : IsMove ({s,d} : Finset ℝ) C (labelledOpening d C) :=
      pair_first_move s d C (label (s*B)) hs hd hC hr
    rw [Finset.pair_comm] at hm
    have he : partnerEnd d s B=labelledOpening d C := by change (if InWay d C then labelledOpening d C else C)=labelledOpening d C; rw [if_pos hr]
    rw [he]
    refine ⟨⟨C,hBC.le,hCD,hm⟩,?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with he|hx
    · subst x; exact not_lt.mp hclear.1
    · exact (Finset.mem_singleton.mp hx) ▸ not_lt.mp hclear.2
  · have he : partnerEnd d s B=C := by change (if InWay d C then labelledOpening d C else C)=C; rw [if_neg hr]
    rw [he]
    refine ⟨⟨B,le_rfl,hBC,pair_first_move d s B N hd hs hB hw⟩,?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with he|hx
    · subst x; exact not_lt.mp hr
    · rw [Finset.mem_singleton.mp hx]
      exact clear_of_window (label (s*B)) hC.ge (by linarith only [hC])

#print axioms opening_recapture_positive
#print axioms recapture_forces_separation
#print axioms recapture_forces_three
#print axioms own_opening_retained
#print axioms reversal_clears_pair
#print axioms labelled_opening_identity
#print axioms singleton_captured_move
#print axioms pair_first_move
#print axioms pair_last_move_and_clear
end Fresh.NativeOpeningReversal
