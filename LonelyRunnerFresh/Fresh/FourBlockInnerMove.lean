import Fresh.FourBlockInnerCaptureBounds

namespace Fresh.FourBlockInnerMove
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailBounds Fresh.FourBlockLongTailPhase
  Fresh.FourBlockOuterReturnBounds Fresh.FourBlockInnerExit Fresh.FourBlockInnerCaptureBounds

theorem inner_move (c g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hsmall : g+h+j ≤ 3)
    (hhi : 13 ≤ 2*(g+h+j)+8*remainder g h j m a b e) :
    IsMove (disparitySet (speeds c g h j 1 1 1) 0)
      (returnOpening g h j m a b e) (innerOpening g h j a b e) := by
  obtain ⟨hRlo,hRhi⟩ := native_remainder_band g h j m a b e hg hh hj hsum
  obtain ⟨hPlo,hPhi⟩ := inner_capture_bounds g h j hgpos hhpos hjpos m a b e hsmall hRhi hhi
  have hf3 := return_phase c g h j hgpos hhpos hjpos m a b e (3 : Fin 8) (by norm_num)
  have hf4 := return_phase c g h j hgpos hhpos hjpos m a b e (4 : Fin 8) (by norm_num)
  have hf5 := return_phase c g h j hgpos hhpos hjpos m a b e (5 : Fin 8) (by norm_num)
  have hf6 := return_phase c g h j hgpos hhpos hjpos m a b e (6 : Fin 8) (by norm_num)
  have hf7 := return_phase c g h j hgpos hhpos hjpos m a b e (7 : Fin 8) (by norm_num)
  norm_num at hf3 hf4 hf5 hf6 hf7
  have hc4 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 4-speeds c g h j 1 1 1 0)*returnOpening g h j m a b e) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 4-wholeLap m a b e 1 1 1 0+1)
    all_goals push_cast at hf4 ⊢; linarith
  have hc5 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 5-speeds c g h j 1 1 1 0)*returnOpening g h j m a b e) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 5-wholeLap m a b e 1 1 1 0+1)
    all_goals push_cast at hf5 ⊢; linarith
  have hc6 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 6-speeds c g h j 1 1 1 0)*returnOpening g h j m a b e) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 6-wholeLap m a b e 1 1 1 0+1)
    all_goals push_cast at hf6 ⊢; linarith
  have hc7 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 7-speeds c g h j 1 1 1 0)*returnOpening g h j m a b e) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 7-wholeLap m a b e 1 1 1 0+2)
    all_goals push_cast at hf7 ⊢; linarith
  have hpartner : (speeds c g h j 1 1 1 3-speeds c g h j 1 1 1 0)*returnOpening g h j m a b e-
      ((wholeLap m a b e 1 1 1 3-wholeLap m a b e 1 1 1 0 : ℤ) : ℝ) ≤ 1 := by push_cast; linarith
  have hmono := FourBlockEndpoints.speeds_monotone c g h j 1 1 1 (by norm_num) (by norm_num) hgpos hhpos hjpos
  have hgap := native_phase_gaps c g h j 1 1 1 (by norm_num) (by norm_num) m a b e hg hh hj
  have hprefix : ∀ i : Fin 8, 0 < (i : ℕ) → i < (3 : Fin 8) →
      (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 0)*returnOpening g h j m a b e) := by
    intro i hi0 hi3
    exact Fresh.EndpointRetainedSegment.earlier_readings_clear _ _ _ _ _
      (phase_identity c g h j 1 1 1 m a b e) hgap hmono (by linarith) 3 hpartner i hi0 hi3
  have hD3 : speeds c g h j 1 1 1 3-speeds c g h j 1 1 1 0=g+h+j := by
    norm_num [speeds]
    ring
  have hpos3 : 0 < speeds c g h j 1 1 1 3-speeds c g h j 1 1 1 0 := by rw [hD3]; positivity
  have hN3 : wholeLap m a b e 1 1 1 3-wholeLap m a b e 1 1 1 0=a+b+e := by
    norm_num [wholeLap]
    ring
  have hnear : |(speeds c g h j 1 1 1 3-speeds c g h j 1 1 1 0)*returnOpening g h j m a b e-
      ((wholeLap m a b e 1 1 1 3-wholeLap m a b e 1 1 1 0+1 : ℤ) : ℝ)| < 1/8 := by
    rw [abs_lt]
    push_cast at hf3 ⊢
    constructor <;> linarith
  have hw3 : InWay |speeds c g h j 1 1 1 3-speeds c g h j 1 1 1 0| (returnOpening g h j m a b e) := by
    rw [abs_of_pos hpos3]
    exact lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (wholeLap m a b e 1 1 1 3-wholeLap m a b e 1 1 1 0+1)) hnear
  have hop3 : nextOpening |speeds c g h j 1 1 1 3-speeds c g h j 1 1 1 0| (returnOpening g h j m a b e)=
      innerOpening g h j a b e := by
    rw [abs_of_pos hpos3,nextOpening_eq hnear,hD3,hN3]
    dsimp [innerOpening]
    push_cast
    congr 1
    ring
  have hothers : ∀ i : Fin 8, i≠0 → i≠3 →
      (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 0)*returnOpening g h j m a b e) := by
    intro i hi0 hi3
    fin_cases i
    · exact (hi0 rfl).elim
    · exact hprefix 1 (by norm_num) (by decide)
    · exact hprefix 2 (by norm_num) (by decide)
    · exact (hi3 rfl).elim
    · exact hc4
    · exact hc5
    · exact hc6
    · exact hc7
  refine Or.inr ⟨|speeds c g h j 1 1 1 3-speeds c g h j 1 1 1 0|,
    mem_disparitySet.mpr ⟨3,by decide,rfl⟩,hw3,hop3.symm,?_⟩
  intro d hd hwD
  obtain ⟨i,hi0,rfl⟩ := mem_disparitySet.mp hd
  by_cases hi3 : i=3
  · subst i; exact hop3.le
  · change distInt (|speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 0| * returnOpening g h j m a b e) < 1/8 at hwD
    rw [Fresh.Localisation.distInt_abs_mul] at hwD
    exact False.elim ((not_lt_of_ge (hothers i hi0 hi3)) hwD)

#print axioms inner_move
end Fresh.FourBlockInnerMove
