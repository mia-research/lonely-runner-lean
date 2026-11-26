import Fresh.FourBlockInnerExit

/-! Strict side of the original cut face: only reading 2 is captured. -/
namespace Fresh.FourBlockInnerCutMove
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailBounds Fresh.FourBlockLongTailPhase
  Fresh.FourBlockInnerExit

noncomputable def cutOpening (g h : ℝ) (a b : ℤ) : ℝ :=
  (((a+b : ℤ) : ℝ)+9/8)/(g+h)

theorem cut_move (c g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hlo : 5*(g+h+j)+24*remainder g h j m a b e ≤ 39)
    (hhi : 13 ≤ 2*(g+h+j)+8*remainder g h j m a b e)
    (hgate : j*innerOpening g h j a b e-(e : ℝ) < 1/4) :
    IsMove (disparitySet (speeds c g h j 1 1 1) 0) (innerOpening g h j a b e)
      (cutOpening g h a b) := by
  obtain ⟨hPlo,hPhi⟩ := inner_bounds g h j hgpos hhpos hjpos m a b e hlo hhi
  have hf3 := inner_phase c g h j hgpos hhpos hjpos m a b e (3 : Fin 8) (by norm_num)
  have hf4 := inner_phase c g h j hgpos hhpos hjpos m a b e (4 : Fin 8) (by norm_num)
  have hf5 := inner_phase c g h j hgpos hhpos hjpos m a b e (5 : Fin 8) (by norm_num)
  have hf6 := inner_phase c g h j hgpos hhpos hjpos m a b e (6 : Fin 8) (by norm_num)
  have hf7 := inner_phase c g h j hgpos hhpos hjpos m a b e (7 : Fin 8) (by norm_num)
  norm_num at hf3 hf4 hf5 hf6 hf7
  have hf2 : (speeds c g h j 1 1 1 2-speeds c g h j 1 1 1 0)*innerOpening g h j a b e-
      ((wholeLap m a b e 1 1 1 2-wholeLap m a b e 1 1 1 0 : ℤ) : ℝ)=
      9/8-(j*innerOpening g h j a b e-(e : ℝ)) := by
    have hid := inner_identity g h j hgpos hhpos hjpos a b e
    norm_num [speeds,wholeLap]
    push_cast at hid
    nlinarith only [hid]
  have hmono := FourBlockEndpoints.speeds_monotone c g h j 1 1 1 (by norm_num) (by norm_num) hgpos hhpos hjpos
  have hgap := native_phase_gaps c g h j 1 1 1 (by norm_num) (by norm_num) m a b e hg hh hj
  have hl2 := Fresh.PhaseNeighbour.phase_separation _ hgap (0 : Fin 8) 2 (by decide)
  have hDi2 : 0 ≤ speeds c g h j 1 1 1 2-speeds c g h j 1 1 1 0 :=
    sub_nonneg.mpr (hmono (by decide))
  have hshift := mul_nonneg hDi2 (by linarith : 0 ≤ innerOpening g h j a b e-((m : ℝ)+1/8))
  have hi2 := phase_identity c g h j 1 1 1 m a b e 2
  have hi0 := phase_identity c g h j 1 1 1 m a b e 0
  have hgateLo : (1/8 : ℝ) ≤ j*innerOpening g h j a b e-(e : ℝ) := by
    have hshiftj := mul_nonneg hjpos.le
      (by linarith : 0 ≤ innerOpening g h j a b e-((m : ℝ)+1/8))
    nlinarith only [hj,hshiftj]
  have hc3 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 3-speeds c g h j 1 1 1 0)*innerOpening g h j a b e) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 3-wholeLap m a b e 1 1 1 0+1)
    all_goals push_cast at hf3 ⊢; linarith
  have hc4 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 4-speeds c g h j 1 1 1 0)*innerOpening g h j a b e) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 4-wholeLap m a b e 1 1 1 0+1)
    all_goals push_cast at hf4 ⊢; linarith
  have hc5 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 5-speeds c g h j 1 1 1 0)*innerOpening g h j a b e) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 5-wholeLap m a b e 1 1 1 0+1)
    all_goals push_cast at hf5 ⊢; linarith
  have hc6 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 6-speeds c g h j 1 1 1 0)*innerOpening g h j a b e) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 6-wholeLap m a b e 1 1 1 0+2)
    all_goals push_cast at hf6 ⊢; linarith
  have hc7 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 7-speeds c g h j 1 1 1 0)*innerOpening g h j a b e) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 7-wholeLap m a b e 1 1 1 0+2)
    all_goals push_cast at hf7 ⊢; linarith
  have hpartner : (speeds c g h j 1 1 1 2-speeds c g h j 1 1 1 0)*innerOpening g h j a b e-
      ((wholeLap m a b e 1 1 1 2-wholeLap m a b e 1 1 1 0 : ℤ) : ℝ) ≤ 1 := by
    push_cast at hf2 ⊢
    linarith
  have hc1 := Fresh.EndpointRetainedSegment.earlier_readings_clear _ _ _ _ _
    (phase_identity c g h j 1 1 1 m a b e) hgap hmono (by linarith : (m : ℝ)+1/8 ≤ innerOpening g h j a b e)
    2 hpartner (1 : Fin 8) (by norm_num) (by decide)
  have hD2 : speeds c g h j 1 1 1 2-speeds c g h j 1 1 1 0=g+h := by
    norm_num [speeds]
    ring
  have hpos2 : 0 < speeds c g h j 1 1 1 2-speeds c g h j 1 1 1 0 := by rw [hD2]; positivity
  have hN2 : wholeLap m a b e 1 1 1 2-wholeLap m a b e 1 1 1 0=a+b := by
    norm_num [wholeLap]
    ring
  have hnear : |(speeds c g h j 1 1 1 2-speeds c g h j 1 1 1 0)*innerOpening g h j a b e-
      ((wholeLap m a b e 1 1 1 2-wholeLap m a b e 1 1 1 0+1 : ℤ) : ℝ)| < 1/8 := by
    rw [abs_lt]
    push_cast at hf2 ⊢
    constructor <;> linarith
  have hw2 : InWay |speeds c g h j 1 1 1 2-speeds c g h j 1 1 1 0| (innerOpening g h j a b e) := by
    rw [abs_of_pos hpos2]
    exact lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (wholeLap m a b e 1 1 1 2-wholeLap m a b e 1 1 1 0+1)) hnear
  have hop2 : nextOpening |speeds c g h j 1 1 1 2-speeds c g h j 1 1 1 0| (innerOpening g h j a b e)=
      cutOpening g h a b := by
    rw [abs_of_pos hpos2,nextOpening_eq hnear,hD2,hN2]
    dsimp [cutOpening]
    push_cast
    congr 1
    ring
  have hothers : ∀ i : Fin 8, i≠0 → i≠2 →
      (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 0)*innerOpening g h j a b e) := by
    intro i hi0 hi2
    fin_cases i
    · exact (hi0 rfl).elim
    · exact hc1
    · exact (hi2 rfl).elim
    · exact hc3
    · exact hc4
    · exact hc5
    · exact hc6
    · exact hc7
  refine Or.inr ⟨|speeds c g h j 1 1 1 2-speeds c g h j 1 1 1 0|,
    mem_disparitySet.mpr ⟨2,by decide,rfl⟩,hw2,hop2.symm,?_⟩
  intro d hd hwD
  obtain ⟨i,hi0,rfl⟩ := mem_disparitySet.mp hd
  by_cases hi2 : i=2
  · subst i; exact hop2.le
  · change distInt (|speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 0| * innerOpening g h j a b e) < 1/8 at hwD
    rw [Fresh.Localisation.distInt_abs_mul] at hwD
    exact False.elim ((not_lt_of_ge (hothers i hi0 hi2)) hwD)

#print axioms cut_move
end Fresh.FourBlockInnerCutMove
