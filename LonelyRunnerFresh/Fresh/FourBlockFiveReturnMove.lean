import Fresh.FourBlockFiveReturnArrangement
import Fresh.FourBlockSingletonReturnExit

/-! A return by runner5 can win even when another original reading is
captured: the native returned-opening exit bounds every competing opening. -/
namespace Fresh.FourBlockFiveReturnMove
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailPhase
  Fresh.FourBlockFiveReturnExit Fresh.FourBlockSingletonReturnExit

theorem return_move (c g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hlo : g+h+j+2*remainder g h j m a b e ≤ 19/4)
    (hhi : 17 ≤ 5*(g+h+j)+8*remainder g h j m a b e)
    (hcut : j*fiveOpening g h j m a b e-(e : ℝ)+
      2*(fiveOpening g h j m a b e-(m : ℝ)) ≤ 2)
    (hsingle : g*fiveOpening g h j m a b e-(a : ℝ) ≤ 7/8 ∨
      (9/8 : ℝ) ≤ g*fiveOpening g h j m a b e-(a : ℝ))
    (hcaplo : (7/4 : ℝ) < tailCut g h j a b e+2*(singletonOpening g a-(m : ℝ)))
    (hcaphi : tailCut g h j a b e+2*(singletonOpening g a-(m : ℝ)) < 2) :
    IsMove (disparitySet (speeds c g h j 1 1 1) 0)
      (singletonOpening g a) (fiveOpening g h j m a b e) := by
  have hf5 := Fresh.FourBlockSingletonReturnExit.packet_phase c g h j hgpos m a b e (5 : Fin 8) (by norm_num)
  norm_num at hf5
  have hD5 : speeds c g h j 1 1 1 5-speeds c g h j 1 1 1 0=2+g+h+j := by
    norm_num [speeds]
    ring
  have hpos5 : 0 < speeds c g h j 1 1 1 5-speeds c g h j 1 1 1 0 := by rw [hD5]; positivity
  have hN5 : wholeLap m a b e 1 1 1 5-wholeLap m a b e 1 1 1 0=2*m+a+b+e := by
    norm_num [wholeLap]
    ring
  have hnear : |(speeds c g h j 1 1 1 5-speeds c g h j 1 1 1 0)*singletonOpening g a-
      ((wholeLap m a b e 1 1 1 5-wholeLap m a b e 1 1 1 0+3 : ℤ) : ℝ)| < 1/8 := by
    rw [abs_lt]
    push_cast at hf5 ⊢
    constructor <;> linarith
  have hw5 : InWay |speeds c g h j 1 1 1 5-speeds c g h j 1 1 1 0| (singletonOpening g a) := by
    rw [abs_of_pos hpos5]
    exact lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (wholeLap m a b e 1 1 1 5-wholeLap m a b e 1 1 1 0+3)) hnear
  have hop5 : nextOpening |speeds c g h j 1 1 1 5-speeds c g h j 1 1 1 0| (singletonOpening g a)=
      fiveOpening g h j m a b e := by
    rw [abs_of_pos hpos5,nextOpening_eq hnear,hD5,hN5]
    dsimp [fiveOpening]
    push_cast
    congr 1
    ring
  have hmem : |speeds c g h j 1 1 1 5-speeds c g h j 1 1 1 0| ∈
      disparitySet (speeds c g h j 1 1 1) 0 := mem_disparitySet.mpr ⟨5,by decide,rfl⟩
  have hmono := FourBlockEndpoints.speeds_monotone c g h j 1 1 1 (by norm_num) (by norm_num) hgpos hhpos hjpos
  have hpos : ∀ d ∈ disparitySet (speeds c g h j 1 1 1) 0, 0 < d := by
    intro d hd
    obtain ⟨i,hi0,rfl⟩ := mem_disparitySet.mp hd
    apply abs_pos.mpr
    have hstrict : StrictMono (speeds c g h j 1 1 1) := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro u
      have hd := FourBlockEndpoints.adjacent_speed_gap c g h j 1 1 1 (by norm_num) (by norm_num) u
      split_ifs at hd <;> linarith
    exact sub_ne_zero.mpr (fun heq => hi0 (hstrict.injective heq))
  have htime : singletonOpening g a ≤ fiveOpening g h j m a b e := by
    rw [←hop5]
    exact (lt_nextOpening (by rw [abs_of_pos hpos5]; exact hpos5) hw5).le
  have hclear := five_clear c g h j hgpos hhpos hjpos m a b e hg hh hj hlo hhi hcut hsingle
  refine Or.inr ⟨_,hmem,hw5,hop5.symm,?_⟩
  intro d hd hwD
  exact nextOpening_le_of_lonely hpos hclear htime hd hwD

#print axioms return_move
end Fresh.FourBlockFiveReturnMove
