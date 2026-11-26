import Fresh.FourBlockOuterLapPhase

/-! All five original AP readings clear independently of the return lap.
Two explicit original cut windows complete the native outer exit. -/
namespace Fresh.FourBlockOuterLapClear
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockOuterLapPhase

theorem packet_clear (c g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e r : ℤ)
    (hlo : 11*(g+h+j)+16*remainder g h j m a b e ≤ 16*(r : ℝ)-42)
    (hhi : 8*(r : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e)
    (i : Fin 8) (hi : 3 ≤ (i : ℕ)) :
    (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 0)*outerLapOpening g h j m a b e r) := by
  obtain ⟨hPlo,hPhi⟩ := opening_bounds g h j hg hh hj m a b e r hlo hhi
  have hf3 := packet_phase c g h j hg hh hj m a b e r (3 : Fin 8) (by norm_num)
  norm_num at hf3
  have hc3 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 3-speeds c g h j 1 1 1 0)*outerLapOpening g h j m a b e r) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 3-wholeLap m a b e 1 1 1 0+r-4)
    all_goals push_cast at hf3 ⊢; linarith
  have hf4 := packet_phase c g h j hg hh hj m a b e r (4 : Fin 8) (by norm_num)
  norm_num at hf4
  have hc4 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 4-speeds c g h j 1 1 1 0)*outerLapOpening g h j m a b e r) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 4-wholeLap m a b e 1 1 1 0+r-3)
    all_goals push_cast at hf4 ⊢; linarith
  have hf5 := packet_phase c g h j hg hh hj m a b e r (5 : Fin 8) (by norm_num)
  norm_num at hf5
  have hc5 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 5-speeds c g h j 1 1 1 0)*outerLapOpening g h j m a b e r) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 5-wholeLap m a b e 1 1 1 0+r-2)
    all_goals push_cast at hf5 ⊢; linarith
  have hf6 := packet_phase c g h j hg hh hj m a b e r (6 : Fin 8) (by norm_num)
  norm_num at hf6
  have hc6 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 6-speeds c g h j 1 1 1 0)*outerLapOpening g h j m a b e r) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 6-wholeLap m a b e 1 1 1 0+r-1)
    all_goals push_cast at hf6 ⊢; linarith
  have hf7 := packet_phase c g h j hg hh hj m a b e r (7 : Fin 8) (by norm_num)
  norm_num at hf7
  have hc7 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 7-speeds c g h j 1 1 1 0)*outerLapOpening g h j m a b e r) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 7-wholeLap m a b e 1 1 1 0+r-0)
    all_goals push_cast at hf7 ⊢; linarith
  fin_cases i
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi
  · exact hc3
  · exact hc4
  · exact hc5
  · exact hc6
  · exact hc7

theorem cut_phase (c g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e r : ℤ) :
    (speeds c g h j 1 1 1 2-speeds c g h j 1 1 1 0)*outerLapOpening g h j m a b e r-
      ((wholeLap m a b e 1 1 1 2-wholeLap m a b e 1 1 1 0 : ℤ) : ℝ)=
      (r : ℝ)+1/8-4*(outerLapOpening g h j m a b e r-(m : ℝ))-
        (j*outerLapOpening g h j m a b e r-(e : ℝ)) := by
  have hid := opening_identity g h j hg hh hj m a b e r
  norm_num [speeds,wholeLap,spanLap] at *
  nlinarith only [hid]

theorem outer_clear (c g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e r ell kappa : ℤ)
    (hlo : 11*(g+h+j)+16*remainder g h j m a b e ≤ 16*(r : ℝ)-42)
    (hhi : 8*(r : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e)
    (hslo : (ell : ℝ)+1/8 ≤ g*outerLapOpening g h j m a b e r-(a : ℝ))
    (hshi : g*outerLapOpening g h j m a b e r-(a : ℝ) ≤ (ell : ℝ)+7/8)
    (hclo : (r : ℝ)-(kappa : ℝ)-3/4 ≤ j*outerLapOpening g h j m a b e r-(e : ℝ)+
      4*(outerLapOpening g h j m a b e r-(m : ℝ)))
    (hchi : j*outerLapOpening g h j m a b e r-(e : ℝ)+
      4*(outerLapOpening g h j m a b e r-(m : ℝ)) ≤ (r : ℝ)-(kappa : ℝ)) :
    LonelyAt (disparitySet (speeds c g h j 1 1 1) 0) (outerLapOpening g h j m a b e r) := by
  have hc1 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 1-speeds c g h j 1 1 1 0)*outerLapOpening g h j m a b e r) := by
    apply clear_of_window (a+ell)
    all_goals norm_num [speeds]; push_cast; linarith
  have hf2 := cut_phase c g h j hg hh hj m a b e r
  have hc2 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 2-speeds c g h j 1 1 1 0)*outerLapOpening g h j m a b e r) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 2-wholeLap m a b e 1 1 1 0+kappa)
    all_goals push_cast at hf2 ⊢; linarith
  intro d hd
  obtain ⟨i,hi0,rfl⟩ := mem_disparitySet.mp hd
  rw [Fresh.Localisation.distInt_abs_mul]
  by_cases hi1 : i=1
  · subst i; exact hc1
  by_cases hi2 : i=2
  · subst i; exact hc2
  have hiv := i.isLt
  have h0 := Fin.val_ne_of_ne hi0
  have h1 := Fin.val_ne_of_ne hi1
  have h2 := Fin.val_ne_of_ne hi2
  exact packet_clear c g h j hg hh hj m a b e r hlo hhi i (by omega)

#print axioms packet_clear
#print axioms cut_phase
#print axioms outer_clear
end Fresh.FourBlockOuterLapClear
