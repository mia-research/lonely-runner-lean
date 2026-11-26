import Fresh.FourBlockOuterReturnClear

/-! The fourth opening forces an actual return by the original outer
endpoint. All six other readings are retained clear at that same entry. -/
namespace Fresh.FourBlockOuterReturnMove
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailBounds Fresh.FourBlockLongTailPhase
  Fresh.FourBlockOuterReturnBounds

theorem return_move (c g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hlo : 3*(g+h+j)+16*remainder g h j m a b e ≤ 22)
    (hhi : 31 < 5*(g+h+j)+24*remainder g h j m a b e) :
    IsMove (disparitySet (speeds c g h j 1 1 1) 0)
      (packetOpening g h j m a b e 3) (returnOpening g h j m a b e) := by
  obtain ⟨hRlo,hRhi⟩ := native_remainder_band g h j m a b e hg hh hj hsum
  obtain ⟨hPlo,hPhi⟩ := capture_bounds g h j hgpos hhpos hjpos m a b e hRhi hlo hhi
  have hf3 := Fresh.FourBlockFourthExit.phase_three c g h j hgpos hhpos hjpos m a b e
  have hf4 := packet_phase c g h j 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hgpos hhpos hjpos m a b e 3 (by norm_num) (4 : Fin 8) (by norm_num)
  have hf5 := packet_phase c g h j 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hgpos hhpos hjpos m a b e 3 (by norm_num) (5 : Fin 8) (by norm_num)
  have hf6 := packet_phase c g h j 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hgpos hhpos hjpos m a b e 3 (by norm_num) (6 : Fin 8) (by norm_num)
  have hf7 := packet_phase c g h j 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hgpos hhpos hjpos m a b e 3 (by norm_num) (7 : Fin 8) (by norm_num)
  norm_num at hf3 hf4 hf5 hf6 hf7
  have hc3 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 3-speeds c g h j 1 1 1 0)*packetOpening g h j m a b e 3) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 3-wholeLap m a b e 1 1 1 0)
    all_goals push_cast at hf3 ⊢; linarith
  have hc4 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 4-speeds c g h j 1 1 1 0)*packetOpening g h j m a b e 3) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 4-wholeLap m a b e 1 1 1 0+1)
    all_goals push_cast at hf4 ⊢; linarith
  have hc5 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 5-speeds c g h j 1 1 1 0)*packetOpening g h j m a b e 3) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 5-wholeLap m a b e 1 1 1 0+1)
    all_goals push_cast at hf5 ⊢; linarith
  have hc6 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 6-speeds c g h j 1 1 1 0)*packetOpening g h j m a b e 3) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 6-wholeLap m a b e 1 1 1 0+1)
    all_goals push_cast at hf6 ⊢; linarith
  have hpartner : (speeds c g h j 1 1 1 3-speeds c g h j 1 1 1 0)*packetOpening g h j m a b e 3-
      ((wholeLap m a b e 1 1 1 3-wholeLap m a b e 1 1 1 0 : ℤ) : ℝ) ≤ 1 := by push_cast; linarith
  have hmono := FourBlockEndpoints.speeds_monotone c g h j 1 1 1 (by norm_num) (by norm_num) hgpos hhpos hjpos
  have hgap := native_phase_gaps c g h j 1 1 1 (by norm_num) (by norm_num) m a b e hg hh hj
  have hprefix : ∀i : Fin 8,0 < (i : ℕ) → i < (3 : Fin 8) →
      (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 0)*packetOpening g h j m a b e 3) := by
    intro i hi0 hi3
    exact Fresh.EndpointRetainedSegment.earlier_readings_clear _ _ _ _ _
      (phase_identity c g h j 1 1 1 m a b e) hgap hmono (by linarith) 3 hpartner i hi0 hi3
  have hD7 : speeds c g h j 1 1 1 7-speeds c g h j 1 1 1 0=4+g+h+j := by
    have hd := tail_reading c g h j 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (7 : Fin 8) (by norm_num)
    norm_num at hd
    exact hd
  have hpos7 : 0 < speeds c g h j 1 1 1 7-speeds c g h j 1 1 1 0 := by rw [hD7]; positivity
  have hN7 : wholeLap m a b e 1 1 1 7-wholeLap m a b e 1 1 1 0=spanLap m a b e := by
    rw [tail_lap 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) m a b e (7 : Fin 8) (by norm_num)]
    norm_num [spanLap]
  have hnear : |(speeds c g h j 1 1 1 7-speeds c g h j 1 1 1 0)*packetOpening g h j m a b e 3-
      ((wholeLap m a b e 1 1 1 7-wholeLap m a b e 1 1 1 0+2 : ℤ) : ℝ)| < 1/8 := by
    rw [abs_lt]
    push_cast at hf7 ⊢
    constructor <;> linarith
  have hw7 : InWay |speeds c g h j 1 1 1 7-speeds c g h j 1 1 1 0| (packetOpening g h j m a b e 3) := by
    rw [abs_of_pos hpos7]
    exact lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (wholeLap m a b e 1 1 1 7-wholeLap m a b e 1 1 1 0+2)) hnear
  have hop7 : nextOpening |speeds c g h j 1 1 1 7-speeds c g h j 1 1 1 0| (packetOpening g h j m a b e 3)=
      returnOpening g h j m a b e := by
    rw [abs_of_pos hpos7,nextOpening_eq hnear,hD7,hN7]
    dsimp [returnOpening]
    push_cast
    congr 1
    ring
  have hothers : ∀i : Fin 8,i≠0 → i≠7 →
      (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 0)*packetOpening g h j m a b e 3) := by
    intro i hi0 hi7
    fin_cases i
    · exact (hi0 rfl).elim
    · exact hprefix 1 (by norm_num) (by decide)
    · exact hprefix 2 (by norm_num) (by decide)
    · exact hc3
    · exact hc4
    · exact hc5
    · exact hc6
    · exact (hi7 rfl).elim
  refine Or.inr ⟨|speeds c g h j 1 1 1 7-speeds c g h j 1 1 1 0|,
    mem_disparitySet.mpr ⟨7,by decide,rfl⟩,hw7,hop7.symm,?_⟩
  intro d hd hwD
  obtain ⟨i,hi0,rfl⟩ := mem_disparitySet.mp hd
  by_cases hi7 : i=7
  · subst i; exact hop7.le
  · change distInt (|speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 0| * packetOpening g h j m a b e 3) < 1/8 at hwD
    rw [Fresh.Localisation.distInt_abs_mul] at hwD
    exact False.elim ((not_lt_of_ge (hothers i hi0 hi7)) hwD)

#print axioms return_move
end Fresh.FourBlockOuterReturnMove
