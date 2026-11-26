import Fresh.FourBlockLongTailEpisode

/-! Native fourth-opening escape for1+1+1+5. The outer endpoint has passed
its return opening while its partner has not re-entered. Both closed faces
are retained; no covering or move-budget premise is used. -/
namespace Fresh.FourBlockFourthExit
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailBounds Fresh.FourBlockLongTailPhase

theorem fourth_bounds (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e : ℤ)
    (hlo : 5*(g+h+j)+24*remainder g h j m a b e ≤ 31)
    (hhi : 5 ≤ g+h+j+4*remainder g h j m a b e) :
    (m : ℝ)+1/3 ≤ packetOpening g h j m a b e 3 ∧
    packetOpening g h j m a b e 3 ≤ (m : ℝ)+3/8 := by
  have hd := packet_delta g h j hg hh hj m a b e 3 (by norm_num)
  have hp : 0 < 4+g+h+j-(3 : ℝ) := by linarith
  norm_num at hd
  constructor <;> nlinarith

theorem phase_three (c g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e : ℤ) :
    (speeds c g h j 1 1 1 3-speeds c g h j 1 1 1 0)*packetOpening g h j m a b e 3-
      ((wholeLap m a b e 1 1 1 3-wholeLap m a b e 1 1 1 0 : ℤ) : ℝ)=
      9/8-(packetOpening g h j m a b e 3-(m : ℝ)) := by
  have hid := packet_identity g h j hg hh hj m a b e 3 (by norm_num)
  have hD : speeds c g h j 1 1 1 3-speeds c g h j 1 1 1 0=g+h+j := by
    norm_num [speeds]
    ring
  have hN : wholeLap m a b e 1 1 1 3-wholeLap m a b e 1 1 1 0=a+b+e := by
    norm_num [wholeLap]
    ring
  rw [hD,hN]
  dsimp [spanLap] at hid
  push_cast at hid ⊢
  nlinarith only [hid]

theorem fourth_clear (c g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hlo : 5*(g+h+j)+24*remainder g h j m a b e ≤ 31)
    (hhi : 5 ≤ g+h+j+4*remainder g h j m a b e) :
    LonelyAt (disparitySet (speeds c g h j 1 1 1) 0) (packetOpening g h j m a b e 3) := by
  obtain ⟨hPlo,hPhi⟩ := fourth_bounds g h j hgpos hhpos hjpos m a b e hlo hhi
  have hf3 := phase_three c g h j hgpos hhpos hjpos m a b e
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
  have hc7 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 7-speeds c g h j 1 1 1 0)*packetOpening g h j m a b e 3) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 7-wholeLap m a b e 1 1 1 0+2)
    all_goals push_cast at hf7 ⊢; linarith
  have hpartner : (speeds c g h j 1 1 1 3-speeds c g h j 1 1 1 0)*packetOpening g h j m a b e 3-
      ((wholeLap m a b e 1 1 1 3-wholeLap m a b e 1 1 1 0 : ℤ) : ℝ) ≤ 1 := by
    push_cast
    linarith
  have hmono := FourBlockEndpoints.speeds_monotone c g h j 1 1 1 (by norm_num) (by norm_num) hgpos hhpos hjpos
  have hgap := native_phase_gaps c g h j 1 1 1 (by norm_num) (by norm_num) m a b e hg hh hj
  have hprefix : ∀i : Fin 8,0 < (i : ℕ) → i < (3 : Fin 8) →
      (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 0)*packetOpening g h j m a b e 3) := by
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

#print axioms fourth_bounds
#print axioms phase_three
#print axioms fourth_clear
end Fresh.FourBlockFourthExit
