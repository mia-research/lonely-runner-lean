import Fresh.FourBlockFiveReturnMove

/-! Strict singleton strip at the later original runner4 opening:
only runner1 is captured, even when its opening is not an exit. -/
namespace Fresh.FourBlockLateSingletonMove
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailPhase
  Fresh.FourBlockFourReturnExit Fresh.FourBlockSingletonReturnExit

theorem singleton_move (c g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hlo : 3*(g+h+j)+8*remainder g h j m a b e ≤ 17)
    (hhi : 49 ≤ 11*(g+h+j)+24*remainder g h j m a b e)
    (hcut : j*fourOpening g h j m a b e-(e : ℝ)+
      (fourOpening g h j m a b e-(m : ℝ)) ≤ 1)
    (hcaplo : (7/8 : ℝ) < g*fourOpening g h j m a b e-(a : ℝ))
    (hcaphi : g*fourOpening g h j m a b e-(a : ℝ) < 9/8) :
    IsMove (disparitySet (speeds c g h j 1 1 1) 0)
      (fourOpening g h j m a b e) (singletonOpening g a) := by
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
  have hD1 : speeds c g h j 1 1 1 1-speeds c g h j 1 1 1 0=g := by norm_num [speeds]
  have hnear : |g*fourOpening g h j m a b e-((a+1 : ℤ) : ℝ)| < 1/8 := by
    rw [abs_lt]
    push_cast
    constructor <;> linarith
  have hw1 : InWay |speeds c g h j 1 1 1 1-speeds c g h j 1 1 1 0| (fourOpening g h j m a b e) := by
    rw [hD1,abs_of_pos hgpos]
    exact lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (a+1)) hnear
  have hop1 : nextOpening |speeds c g h j 1 1 1 1-speeds c g h j 1 1 1 0| (fourOpening g h j m a b e)=
      singletonOpening g a := by
    rw [hD1,abs_of_pos hgpos,nextOpening_eq hnear]
    dsimp [singletonOpening]
    push_cast
    congr 1
    ring
  have hothers : ∀ i : Fin 8, i≠0 → i≠1 →
      (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 0)*fourOpening g h j m a b e) := by
    intro i hi0 hi1
    fin_cases i
    · exact (hi0 rfl).elim
    · exact (hi1 rfl).elim
    · exact hc2
    · exact hc3
    · exact hc4
    · exact hc5
    · exact hc6
    · exact hc7
  refine Or.inr ⟨|speeds c g h j 1 1 1 1-speeds c g h j 1 1 1 0|,
    mem_disparitySet.mpr ⟨1,by decide,rfl⟩,hw1,hop1.symm,?_⟩
  intro d hd hwD
  obtain ⟨i,hi0,rfl⟩ := mem_disparitySet.mp hd
  by_cases hi1 : i=1
  · subst i; exact hop1.le
  · change distInt (|speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 0| * fourOpening g h j m a b e) < 1/8 at hwD
    rw [Fresh.Localisation.distInt_abs_mul] at hwD
    exact False.elim ((not_lt_of_ge (hothers i hi0 hi1)) hwD)

#print axioms singleton_move
end Fresh.FourBlockLateSingletonMove
