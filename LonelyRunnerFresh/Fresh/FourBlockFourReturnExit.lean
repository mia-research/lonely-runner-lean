import Fresh.FourBlockInnerEpisode

/-! The original runner4 returns at its next lap. These are native
opening and cut faces; no complete isolation is supplied as an input. -/
namespace Fresh.FourBlockFourReturnExit
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailPhase

noncomputable def fourOpening (g h j : ℝ) (m a b e : ℤ) : ℝ :=
  (((m+a+b+e : ℤ) : ℝ)+17/8)/(1+g+h+j)

theorem four_identity (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e : ℤ) :
    (1+g+h+j)*fourOpening g h j m a b e=((m+a+b+e : ℤ) : ℝ)+17/8 := by
  have hp : 0 < 1+g+h+j := by linarith
  dsimp [fourOpening]
  field_simp [ne_of_gt hp]

theorem four_bounds (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e : ℤ)
    (hlo : 3*(g+h+j)+8*remainder g h j m a b e ≤ 17)
    (hhi : 49 ≤ 11*(g+h+j)+24*remainder g h j m a b e) :
    (m : ℝ)+1/2 ≤ fourOpening g h j m a b e ∧
    fourOpening g h j m a b e ≤ (m : ℝ)+7/12 := by
  have hid := four_identity g h j hg hh hj m a b e
  have hd : (1+g+h+j)*(fourOpening g h j m a b e-((m : ℝ)+1/8))=
      5/2-remainder g h j m a b e := by
    dsimp [remainder]
    push_cast at hid
    nlinarith only [hid]
  have hp : 0 < 1+g+h+j := by linarith
  constructor <;> nlinarith

theorem packet_phase (c g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e : ℤ) (i : Fin 8) (hi : 3 ≤ (i : ℕ)) :
    (speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 0)*fourOpening g h j m a b e-
      ((wholeLap m a b e 1 1 1 i-wholeLap m a b e 1 1 1 0 : ℤ) : ℝ)=
      17/8+((i : ℝ)-4)*(fourOpening g h j m a b e-(m : ℝ)) := by
  let N : Fin 8 → ℤ := fun u=>wholeLap m a b e 1 1 1 u-wholeLap m a b e 1 1 1 0
  have h1 : (1 : ℕ) ≤ (i : ℕ) := by omega
  have h2 : (2 : ℕ) ≤ (i : ℕ) := by omega
  have hs : speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 4=((i : ℝ)-4)*1 := by
    norm_num [speeds,h1,h2,hi]
  have hn : N i-N 4=(((i : ℕ) : ℤ)-((4 : Fin 8) : ℕ))*m := by
    dsimp [N]
    norm_num [wholeLap,h1,h2,hi]
    ring
  have ha : (speeds c g h j 1 1 1 4-speeds c g h j 1 1 1 0)*fourOpening g h j m a b e=
      (N 4 : ℝ)+(2 : ℝ)+1/8 := by
    have hid := four_identity g h j hg hh hj m a b e
    norm_num [N,wholeLap,speeds] at *
    nlinarith only [hid]
  have hp := Fresh.UnitAPPacketPhase.phase_at_anchor (speeds c g h j 1 1 1) N 0 4 i 1
    (fourOpening g h j m a b e) m 2 hs hn (by simpa only [Int.cast_ofNat] using ha)
  norm_num at hp
  exact hp

theorem four_clear (c g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hlo : 3*(g+h+j)+8*remainder g h j m a b e ≤ 17)
    (hhi : 49 ≤ 11*(g+h+j)+24*remainder g h j m a b e)
    (hcut : j*fourOpening g h j m a b e-(e : ℝ)+
      (fourOpening g h j m a b e-(m : ℝ)) ≤ 1)
    (hsingle : g*fourOpening g h j m a b e-(a : ℝ) ≤ 7/8 ∨
      (9/8 : ℝ) ≤ g*fourOpening g h j m a b e-(a : ℝ)) :
    LonelyAt (disparitySet (speeds c g h j 1 1 1) 0) (fourOpening g h j m a b e) := by
  obtain ⟨hPlo,hPhi⟩ := four_bounds g h j hgpos hhpos hjpos m a b e hlo hhi
  have hT : 0 ≤ fourOpening g h j m a b e-((m : ℝ)+1/8) := by linarith
  have hgshift := mul_nonneg hgpos.le hT
  have hhshift := mul_nonneg hhpos.le hT
  have hjshift := mul_nonneg hjpos.le hT
  have hgl : (1/8 : ℝ) ≤ g*fourOpening g h j m a b e-(a : ℝ) := by nlinarith only [hg,hgshift]
  have hhl : (1/8 : ℝ) ≤ h*fourOpening g h j m a b e-(b : ℝ) := by nlinarith only [hh,hhshift]
  have hjl : (1/8 : ℝ) ≤ j*fourOpening g h j m a b e-(e : ℝ) := by nlinarith only [hj,hjshift]
  have hf2 : (speeds c g h j 1 1 1 2-speeds c g h j 1 1 1 0)*fourOpening g h j m a b e-
      ((wholeLap m a b e 1 1 1 2-wholeLap m a b e 1 1 1 0 : ℤ) : ℝ)=
      17/8-(fourOpening g h j m a b e-(m : ℝ))-(j*fourOpening g h j m a b e-(e : ℝ)) := by
    have hid := four_identity g h j hgpos hhpos hjpos m a b e
    norm_num [speeds,wholeLap]
    push_cast at hid
    nlinarith only [hid]
  have hupper1 : g*fourOpening g h j m a b e-(a : ℝ) ≤ 15/8 := by
    have hid := four_identity g h j hgpos hhpos hjpos m a b e
    push_cast at hid
    nlinarith only [hid,hPlo,hhl,hjl]
  have hc1 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 1-speeds c g h j 1 1 1 0)*fourOpening g h j m a b e) := by
    rcases hsingle with hs|hs
    · apply clear_of_window a
      all_goals norm_num [speeds]; linarith
    · apply clear_of_window (a+1)
      all_goals norm_num [speeds]; push_cast; linarith
  have hc2 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 2-speeds c g h j 1 1 1 0)*fourOpening g h j m a b e) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 2-wholeLap m a b e 1 1 1 0+1)
    all_goals push_cast at hf2 ⊢; linarith
  have hf3 := packet_phase c g h j hgpos hhpos hjpos m a b e (3 : Fin 8) (by norm_num)
  have hf4 := packet_phase c g h j hgpos hhpos hjpos m a b e (4 : Fin 8) (by norm_num)
  have hf5 := packet_phase c g h j hgpos hhpos hjpos m a b e (5 : Fin 8) (by norm_num)
  have hf6 := packet_phase c g h j hgpos hhpos hjpos m a b e (6 : Fin 8) (by norm_num)
  have hf7 := packet_phase c g h j hgpos hhpos hjpos m a b e (7 : Fin 8) (by norm_num)
  norm_num at hf3 hf4 hf5 hf6 hf7
  have hc3 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 3-speeds c g h j 1 1 1 0)*fourOpening g h j m a b e) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 3-wholeLap m a b e 1 1 1 0+1)
    all_goals push_cast at hf3 ⊢; linarith
  have hc4 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 4-speeds c g h j 1 1 1 0)*fourOpening g h j m a b e) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 4-wholeLap m a b e 1 1 1 0+2)
    all_goals push_cast at hf4 ⊢; linarith
  have hc5 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 5-speeds c g h j 1 1 1 0)*fourOpening g h j m a b e) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 5-wholeLap m a b e 1 1 1 0+2)
    all_goals push_cast at hf5 ⊢; linarith
  have hc6 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 6-speeds c g h j 1 1 1 0)*fourOpening g h j m a b e) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 6-wholeLap m a b e 1 1 1 0+3)
    all_goals push_cast at hf6 ⊢; linarith
  have hc7 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 7-speeds c g h j 1 1 1 0)*fourOpening g h j m a b e) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 7-wholeLap m a b e 1 1 1 0+3)
    all_goals push_cast at hf7 ⊢; linarith
  intro d hd
  obtain ⟨i,hi0,rfl⟩ := mem_disparitySet.mp hd
  rw [Fresh.Localisation.distInt_abs_mul]
  fin_cases i
  · exact (hi0 rfl).elim
  · exact hc1
  · exact hc2
  · exact hc3
  · exact hc4
  · exact hc5
  · exact hc6
  · exact hc7

#print axioms four_identity
#print axioms four_bounds
#print axioms packet_phase
#print axioms four_clear
end Fresh.FourBlockFourReturnExit
