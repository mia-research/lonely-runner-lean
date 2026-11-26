import Fresh.FourBlockFourReturnMove

/-! Native singleton return: three packet faces retain every original
reading at the opening of runner1, including both closed packet ends. -/
namespace Fresh.FourBlockSingletonReturnExit
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailPhase

noncomputable def singletonOpening (g : ℝ) (a : ℤ) : ℝ := ((a : ℝ)+9/8)/g
noncomputable def tailCut (g h j : ℝ) (a b e : ℤ) : ℝ :=
  (h+j)*singletonOpening g a-(b : ℝ)-(e : ℝ)

theorem singleton_identity (g : ℝ) (hg : 0 < g) (a : ℤ) :
    g*singletonOpening g a=(a : ℝ)+9/8 := by
  dsimp [singletonOpening]
  field_simp [ne_of_gt hg]

theorem packet_phase (c g h j : ℝ) (hg : 0 < g) (m a b e : ℤ)
    (i : Fin 8) (hi : 3 ≤ (i : ℕ)) :
    (speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 0)*singletonOpening g a-
      ((wholeLap m a b e 1 1 1 i-wholeLap m a b e 1 1 1 0 : ℤ) : ℝ)=
      9/8+tailCut g h j a b e+((i : ℝ)-3)*(singletonOpening g a-(m : ℝ)) := by
  have h1 : (1 : ℕ) ≤ (i : ℕ) := by omega
  have h2 : (2 : ℕ) ≤ (i : ℕ) := by omega
  have hid := singleton_identity g hg a
  norm_num [speeds,wholeLap,h1,h2,hi,tailCut]
  push_cast
  nlinarith only [hid]

theorem singleton_clear (c g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e : ℤ)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (htau : (m : ℝ)+1/2 ≤ singletonOpening g a)
    (hinner : 1 ≤ tailCut g h j a b e+(singletonOpening g a-(m : ℝ)))
    (houter : tailCut g h j a b e+4*(singletonOpening g a-(m : ℝ)) ≤ 11/4) :
    LonelyAt (disparitySet (speeds c g h j 1 1 1) 0) (singletonOpening g a) := by
  have hid := singleton_identity g hgpos a
  have hT : 0 ≤ singletonOpening g a-((m : ℝ)+1/8) := by linarith
  have hhshift := mul_nonneg hhpos.le hT
  have hjshift := mul_nonneg hjpos.le hT
  have hhl : (1/8 : ℝ) ≤ h*singletonOpening g a-(b : ℝ) := by nlinarith only [hh,hhshift]
  have hjl : (1/8 : ℝ) ≤ j*singletonOpening g a-(e : ℝ) := by nlinarith only [hj,hjshift]
  have hwlo : (1/4 : ℝ) ≤ tailCut g h j a b e := by dsimp [tailCut]; nlinarith only [hhl,hjl]
  have hwhi : tailCut g h j a b e ≤ 3/4 := by linarith
  have hhu : h*singletonOpening g a-(b : ℝ) ≤ 3/4 := by
    dsimp [tailCut] at hwhi
    nlinarith only [hwhi,hjl]
  have hc1 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 1-speeds c g h j 1 1 1 0)*singletonOpening g a) := by
    apply clear_of_window (a+1)
    all_goals norm_num [speeds]; linarith
  have hc2 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 2-speeds c g h j 1 1 1 0)*singletonOpening g a) := by
    apply clear_of_window (a+b+1)
    all_goals norm_num [speeds]; push_cast; nlinarith only [hid,hhl,hhu]
  have hf3 := packet_phase c g h j hgpos m a b e (3 : Fin 8) (by norm_num)
  have hf4 := packet_phase c g h j hgpos m a b e (4 : Fin 8) (by norm_num)
  have hf5 := packet_phase c g h j hgpos m a b e (5 : Fin 8) (by norm_num)
  have hf6 := packet_phase c g h j hgpos m a b e (6 : Fin 8) (by norm_num)
  have hf7 := packet_phase c g h j hgpos m a b e (7 : Fin 8) (by norm_num)
  norm_num at hf3 hf4 hf5 hf6 hf7
  have hc3 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 3-speeds c g h j 1 1 1 0)*singletonOpening g a) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 3-wholeLap m a b e 1 1 1 0+1)
    all_goals push_cast at hf3 ⊢; linarith
  have hc4 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 4-speeds c g h j 1 1 1 0)*singletonOpening g a) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 4-wholeLap m a b e 1 1 1 0+2)
    all_goals push_cast at hf4 ⊢; linarith
  have hc5 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 5-speeds c g h j 1 1 1 0)*singletonOpening g a) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 5-wholeLap m a b e 1 1 1 0+2)
    all_goals push_cast at hf5 ⊢; linarith
  have hc6 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 6-speeds c g h j 1 1 1 0)*singletonOpening g a) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 6-wholeLap m a b e 1 1 1 0+3)
    all_goals push_cast at hf6 ⊢; linarith
  have hc7 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 7-speeds c g h j 1 1 1 0)*singletonOpening g a) := by
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

#print axioms singleton_identity
#print axioms packet_phase
#print axioms singleton_clear
end Fresh.FourBlockSingletonReturnExit
