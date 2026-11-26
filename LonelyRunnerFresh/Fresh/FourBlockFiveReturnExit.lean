import Fresh.FourBlockInnerEpisode

/-! The original runner5 returns at its next lap. These are native
opening and cut faces; no complete isolation is supplied as an input. -/
namespace Fresh.FourBlockFiveReturnExit
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailPhase

noncomputable def fiveOpening (g h j : ℝ) (m a b e : ℤ) : ℝ :=
  (((2*m+a+b+e : ℤ) : ℝ)+25/8)/(2+g+h+j)

theorem five_identity (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e : ℤ) :
    (2+g+h+j)*fiveOpening g h j m a b e=((2*m+a+b+e : ℤ) : ℝ)+25/8 := by
  have hp : 0 < 2+g+h+j := by linarith
  dsimp [fiveOpening]
  field_simp [ne_of_gt hp]

theorem five_bounds (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e : ℤ)
    (hlo : g+h+j+2*remainder g h j m a b e ≤ 19/4)
    (hhi : 17 ≤ 5*(g+h+j)+8*remainder g h j m a b e) :
    (m : ℝ)+5/8 ≤ fiveOpening g h j m a b e ∧
    fiveOpening g h j m a b e ≤ (m : ℝ)+3/4 := by
  have hid := five_identity g h j hg hh hj m a b e
  have hd : (2+g+h+j)*(fiveOpening g h j m a b e-((m : ℝ)+1/8))=
      27/8-remainder g h j m a b e := by
    dsimp [remainder]
    push_cast at hid
    nlinarith only [hid]
  have hp : 0 < 2+g+h+j := by linarith
  constructor <;> nlinarith

theorem packet_phase (c g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e : ℤ) (i : Fin 8) (hi : 3 ≤ (i : ℕ)) :
    (speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 0)*fiveOpening g h j m a b e-
      ((wholeLap m a b e 1 1 1 i-wholeLap m a b e 1 1 1 0 : ℤ) : ℝ)=
      25/8+((i : ℝ)-5)*(fiveOpening g h j m a b e-(m : ℝ)) := by
  let N : Fin 8 → ℤ := fun u=>wholeLap m a b e 1 1 1 u-wholeLap m a b e 1 1 1 0
  have h1 : (1 : ℕ) ≤ (i : ℕ) := by omega
  have h2 : (2 : ℕ) ≤ (i : ℕ) := by omega
  have hs : speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 5=((i : ℝ)-5)*1 := by
    norm_num [speeds,h1,h2,hi]
  have hn : N i-N 5=(((i : ℕ) : ℤ)-((5 : Fin 8) : ℕ))*m := by
    dsimp [N]
    norm_num [wholeLap,h1,h2,hi]
    ring
  have ha : (speeds c g h j 1 1 1 5-speeds c g h j 1 1 1 0)*fiveOpening g h j m a b e=
      (N 5 : ℝ)+(3 : ℝ)+1/8 := by
    have hid := five_identity g h j hg hh hj m a b e
    norm_num [N,wholeLap,speeds] at *
    nlinarith only [hid]
  have hp := Fresh.UnitAPPacketPhase.phase_at_anchor (speeds c g h j 1 1 1) N 0 5 i 1
    (fiveOpening g h j m a b e) m 3 hs hn (by simpa only [Int.cast_ofNat] using ha)
  norm_num at hp
  exact hp

theorem five_clear (c g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hlo : g+h+j+2*remainder g h j m a b e ≤ 19/4)
    (hhi : 17 ≤ 5*(g+h+j)+8*remainder g h j m a b e)
    (hcut : j*fiveOpening g h j m a b e-(e : ℝ)+
      2*(fiveOpening g h j m a b e-(m : ℝ)) ≤ 2)
    (hsingle : g*fiveOpening g h j m a b e-(a : ℝ) ≤ 7/8 ∨
      (9/8 : ℝ) ≤ g*fiveOpening g h j m a b e-(a : ℝ)) :
    LonelyAt (disparitySet (speeds c g h j 1 1 1) 0) (fiveOpening g h j m a b e) := by
  obtain ⟨hPlo,hPhi⟩ := five_bounds g h j hgpos hhpos hjpos m a b e hlo hhi
  have hT : 0 ≤ fiveOpening g h j m a b e-((m : ℝ)+1/8) := by linarith
  have hgshift := mul_nonneg hgpos.le hT
  have hhshift := mul_nonneg hhpos.le hT
  have hjshift := mul_nonneg hjpos.le hT
  have hgl : (1/8 : ℝ) ≤ g*fiveOpening g h j m a b e-(a : ℝ) := by nlinarith only [hg,hgshift]
  have hhl : (1/8 : ℝ) ≤ h*fiveOpening g h j m a b e-(b : ℝ) := by nlinarith only [hh,hhshift]
  have hjl : (1/8 : ℝ) ≤ j*fiveOpening g h j m a b e-(e : ℝ) := by nlinarith only [hj,hjshift]
  have hf2 : (speeds c g h j 1 1 1 2-speeds c g h j 1 1 1 0)*fiveOpening g h j m a b e-
      ((wholeLap m a b e 1 1 1 2-wholeLap m a b e 1 1 1 0 : ℤ) : ℝ)=
      25/8-2*(fiveOpening g h j m a b e-(m : ℝ))-(j*fiveOpening g h j m a b e-(e : ℝ)) := by
    have hid := five_identity g h j hgpos hhpos hjpos m a b e
    norm_num [speeds,wholeLap]
    push_cast at hid
    nlinarith only [hid]
  have hupper1 : g*fiveOpening g h j m a b e-(a : ℝ) ≤ 15/8 := by
    have hid := five_identity g h j hgpos hhpos hjpos m a b e
    push_cast at hid
    nlinarith only [hid,hPlo,hhl,hjl]
  have hc1 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 1-speeds c g h j 1 1 1 0)*fiveOpening g h j m a b e) := by
    rcases hsingle with hs|hs
    · apply clear_of_window a
      all_goals norm_num [speeds]; linarith
    · apply clear_of_window (a+1)
      all_goals norm_num [speeds]; push_cast; linarith
  have hc2 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 2-speeds c g h j 1 1 1 0)*fiveOpening g h j m a b e) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 2-wholeLap m a b e 1 1 1 0+1)
    all_goals push_cast at hf2 ⊢; linarith
  have hf3 := packet_phase c g h j hgpos hhpos hjpos m a b e (3 : Fin 8) (by norm_num)
  have hf4 := packet_phase c g h j hgpos hhpos hjpos m a b e (4 : Fin 8) (by norm_num)
  have hf5 := packet_phase c g h j hgpos hhpos hjpos m a b e (5 : Fin 8) (by norm_num)
  have hf6 := packet_phase c g h j hgpos hhpos hjpos m a b e (6 : Fin 8) (by norm_num)
  have hf7 := packet_phase c g h j hgpos hhpos hjpos m a b e (7 : Fin 8) (by norm_num)
  norm_num at hf3 hf4 hf5 hf6 hf7
  have hc3 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 3-speeds c g h j 1 1 1 0)*fiveOpening g h j m a b e) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 3-wholeLap m a b e 1 1 1 0+1)
    all_goals push_cast at hf3 ⊢; linarith
  have hc4 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 4-speeds c g h j 1 1 1 0)*fiveOpening g h j m a b e) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 4-wholeLap m a b e 1 1 1 0+2)
    all_goals push_cast at hf4 ⊢; linarith
  have hc5 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 5-speeds c g h j 1 1 1 0)*fiveOpening g h j m a b e) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 5-wholeLap m a b e 1 1 1 0+3)
    all_goals push_cast at hf5 ⊢; linarith
  have hc6 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 6-speeds c g h j 1 1 1 0)*fiveOpening g h j m a b e) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 6-wholeLap m a b e 1 1 1 0+3)
    all_goals push_cast at hf6 ⊢; linarith
  have hc7 : (1/8 : ℝ) ≤ distInt ((speeds c g h j 1 1 1 7-speeds c g h j 1 1 1 0)*fiveOpening g h j m a b e) := by
    apply clear_of_window (wholeLap m a b e 1 1 1 7-wholeLap m a b e 1 1 1 0+4)
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

#print axioms five_identity
#print axioms five_bounds
#print axioms packet_phase
#print axioms five_clear
end Fresh.FourBlockFiveReturnExit
