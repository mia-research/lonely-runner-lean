import Fresh.FourBlockOuterReturnArrangement
import Fresh.UnitAPPacketPhase

/-! Native exit at the inner AP anchor after the endpoint-return branch.
The cut face is explicit jL-e≥1/4, and the other six readings are proved
clear from their original integer laps. No complete isolation is assumed. -/
namespace Fresh.FourBlockInnerExit
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailBounds Fresh.FourBlockLongTailPhase

noncomputable def innerOpening (g h j : ℝ) (a b e : ℤ) : ℝ :=
  (((a+b+e : ℤ) : ℝ)+9/8)/(g+h+j)

theorem inner_identity (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (a b e : ℤ) : (g+h+j)*innerOpening g h j a b e=((a+b+e : ℤ) : ℝ)+9/8 := by
  have hp : 0 < g+h+j := by positivity
  dsimp [innerOpening]
  field_simp [ne_of_gt hp]

theorem inner_bounds (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e : ℤ)
    (hlo : 5*(g+h+j)+24*remainder g h j m a b e ≤ 39)
    (hhi : 13 ≤ 2*(g+h+j)+8*remainder g h j m a b e) :
    (m : ℝ)+1/3 ≤ innerOpening g h j a b e ∧
    innerOpening g h j a b e ≤ (m : ℝ)+3/8 := by
  have hid := inner_identity g h j hg hh hj a b e
  have hp : 0 < g+h+j := by positivity
  have hd : (g+h+j)*(innerOpening g h j a b e-((m : ℝ)+1/8))=
      13/8-remainder g h j m a b e := by
    dsimp [remainder]
    push_cast at hid
    nlinarith only [hid]
  constructor <;> nlinarith

theorem inner_phase (c g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e : ℤ) (i : Fin 8) (hi : 3 ≤ (i : ℕ)) :
    (speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 0)*innerOpening g h j a b e-
      ((wholeLap m a b e 1 1 1 i-wholeLap m a b e 1 1 1 0 : ℤ) : ℝ)=
      9/8+((i : ℝ)-3)*(innerOpening g h j a b e-(m : ℝ)) := by
  let N : Fin 8 → ℤ := fun u=>wholeLap m a b e 1 1 1 u-wholeLap m a b e 1 1 1 0
  have h1 : (1 : ℕ) ≤ (i : ℕ) := by omega
  have h2 : (2 : ℕ) ≤ (i : ℕ) := by omega
  have hs : speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 3=((i : ℝ)-3)*1 := by
    norm_num [speeds,h1,h2,hi]
  have hn : N i-N 3=(((i : ℕ) : ℤ)-((3 : Fin 8) : ℕ))*m := by
    dsimp [N]
    norm_num [wholeLap,h1,h2,hi]
    ring
  have ha : (speeds c g h j 1 1 1 3-speeds c g h j 1 1 1 0)*innerOpening g h j a b e=
      (N 3 : ℝ)+(1 : ℝ)+1/8 := by
    have hid := inner_identity g h j hg hh hj a b e
    norm_num [N,wholeLap,speeds] at *
    nlinarith only [hid]
  have hp := Fresh.UnitAPPacketPhase.phase_at_anchor (speeds c g h j 1 1 1) N 0 3 i 1
    (innerOpening g h j a b e) m 1 hs hn (by simpa only [Int.cast_one] using ha)
  norm_num at hp
  exact hp

theorem earlier_faces (g h j : ℝ) (m a b e : ℤ) (hsmall : g+h+j ≤ 3)
    (hhi : 13 ≤ 2*(g+h+j)+8*remainder g h j m a b e) :
    31 < 5*(g+h+j)+24*remainder g h j m a b e ∧
    22 < 3*(g+h+j)+16*remainder g h j m a b e := by
  constructor <;> linarith

theorem inner_clear (c g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hlo : 5*(g+h+j)+24*remainder g h j m a b e ≤ 39)
    (hhi : 13 ≤ 2*(g+h+j)+8*remainder g h j m a b e)
    (hgate : (1/4 : ℝ) ≤ j*innerOpening g h j a b e-(e : ℝ)) :
    LonelyAt (disparitySet (speeds c g h j 1 1 1) 0) (innerOpening g h j a b e) := by
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
  have hc2 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 2-speeds c g h j 1 1 1 0)*innerOpening g h j a b e) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 2-wholeLap m a b e 1 1 1 0)
    all_goals push_cast at hf2 ⊢
    · push_cast at hi2 hi0
      nlinarith only [hi2,hi0,hshift,hl2]
    · linarith
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
  intro d hd
  obtain ⟨i,hi0',rfl⟩ := mem_disparitySet.mp hd
  rw [Fresh.Localisation.distInt_abs_mul]
  fin_cases i
  · exact (hi0' rfl).elim
  · exact hc1
  · exact hc2
  · exact hc3
  · exact hc4
  · exact hc5
  · exact hc6
  · exact hc7

#print axioms inner_identity
#print axioms inner_bounds
#print axioms inner_phase
#print axioms earlier_faces
#print axioms inner_clear
end Fresh.FourBlockInnerExit
