import Fresh.FourBlockOuterReturnBounds

/-! Exact clearance at the original endpoint's return opening. Earlier
readings are carried by the same native retained-phase mechanism. -/
namespace Fresh.FourBlockOuterReturnClear
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailBounds Fresh.FourBlockLongTailPhase
  Fresh.FourBlockOuterReturnBounds

theorem return_clear (c g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hlo : 3*(g+h+j)+16*remainder g h j m a b e ≤ 22)
    (hhi : 31 ≤ 5*(g+h+j)+24*remainder g h j m a b e) :
    LonelyAt (disparitySet (speeds c g h j 1 1 1) 0) (returnOpening g h j m a b e) := by
  obtain ⟨hPlo,hPhi⟩ := return_bounds g h j hgpos hhpos hjpos m a b e hlo hhi
  have hf3 := return_phase c g h j hgpos hhpos hjpos m a b e (3 : Fin 8) (by norm_num)
  have hf4 := return_phase c g h j hgpos hhpos hjpos m a b e (4 : Fin 8) (by norm_num)
  have hf5 := return_phase c g h j hgpos hhpos hjpos m a b e (5 : Fin 8) (by norm_num)
  have hf6 := return_phase c g h j hgpos hhpos hjpos m a b e (6 : Fin 8) (by norm_num)
  have hf7 := return_phase c g h j hgpos hhpos hjpos m a b e (7 : Fin 8) (by norm_num)
  norm_num at hf3 hf4 hf5 hf6 hf7
  have hc3 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 3-speeds c g h j 1 1 1 0)*returnOpening g h j m a b e) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 3-wholeLap m a b e 1 1 1 0)
    all_goals push_cast at hf3 ⊢; linarith
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
      ((wholeLap m a b e 1 1 1 3-wholeLap m a b e 1 1 1 0 : ℤ) : ℝ) ≤ 1 := by
    push_cast
    linarith
  have hmono := FourBlockEndpoints.speeds_monotone c g h j 1 1 1 (by norm_num) (by norm_num) hgpos hhpos hjpos
  have hgap := native_phase_gaps c g h j 1 1 1 (by norm_num) (by norm_num) m a b e hg hh hj
  have hprefix : ∀i : Fin 8,0 < (i : ℕ) → i < (3 : Fin 8) →
      (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 0)*returnOpening g h j m a b e) := by
    intro i hi0 hi3
    exact Fresh.EndpointRetainedSegment.earlier_readings_clear _ _ _ _ _
      (phase_identity c g h j 1 1 1 m a b e) hgap hmono (by linarith) 3 hpartner i hi0 hi3
  intro d hd
  obtain ⟨i,hi0,rfl⟩ := mem_disparitySet.mp hd
  rw [Fresh.Localisation.distInt_abs_mul]
  fin_cases i
  · exact (hi0 rfl).elim
  · exact hprefix 1 (by norm_num) (by decide)
  · exact hprefix 2 (by norm_num) (by decide)
  · exact hc3
  · exact hc4
  · exact hc5
  · exact hc6
  · exact hc7

#print axioms return_clear
end Fresh.FourBlockOuterReturnClear
