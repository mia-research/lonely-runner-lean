import Fresh.FourBlockFourReturnArrangement

/-! A return by runner4 can win even when another original reading is
captured: the native returned-opening exit bounds every competing opening. -/
namespace Fresh.FourBlockFourReturnMove
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailPhase
  Fresh.FourBlockInnerExit Fresh.FourBlockInnerCutMove Fresh.FourBlockFourReturnExit

theorem cut_identity (g h : ℝ) (hg : 0 < g) (hh : 0 < h) (a b : ℤ) :
    (g+h)*cutOpening g h a b=((a+b : ℤ) : ℝ)+9/8 := by
  have hp : 0 < g+h := by positivity
  dsimp [cutOpening]
  field_simp [ne_of_gt hp]

theorem return_move (c g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hlo : 3*(g+h+j)+8*remainder g h j m a b e ≤ 17)
    (hhi : 49 ≤ 11*(g+h+j)+24*remainder g h j m a b e)
    (hcut : j*fourOpening g h j m a b e-(e : ℝ)+
      (fourOpening g h j m a b e-(m : ℝ)) ≤ 1)
    (hsingle : g*fourOpening g h j m a b e-(a : ℝ) ≤ 7/8 ∨
      (9/8 : ℝ) ≤ g*fourOpening g h j m a b e-(a : ℝ))
    (hcaplo : (3/4 : ℝ) < j*cutOpening g h a b-(e : ℝ)+(cutOpening g h a b-(m : ℝ)))
    (hcaphi : j*cutOpening g h a b-(e : ℝ)+(cutOpening g h a b-(m : ℝ)) < 1) :
    IsMove (disparitySet (speeds c g h j 1 1 1) 0)
      (cutOpening g h a b) (fourOpening g h j m a b e) := by
  have hf4 : (speeds c g h j 1 1 1 4-speeds c g h j 1 1 1 0)*cutOpening g h a b-
      ((wholeLap m a b e 1 1 1 4-wholeLap m a b e 1 1 1 0 : ℤ) : ℝ)=
      9/8+(j*cutOpening g h a b-(e : ℝ))+(cutOpening g h a b-(m : ℝ)) := by
    have hid := cut_identity g h hgpos hhpos a b
    norm_num [speeds,wholeLap]
    push_cast at hid
    nlinarith only [hid]
  have hD4 : speeds c g h j 1 1 1 4-speeds c g h j 1 1 1 0=1+g+h+j := by
    norm_num [speeds]
    ring
  have hpos4 : 0 < speeds c g h j 1 1 1 4-speeds c g h j 1 1 1 0 := by rw [hD4]; positivity
  have hN4 : wholeLap m a b e 1 1 1 4-wholeLap m a b e 1 1 1 0=m+a+b+e := by
    norm_num [wholeLap]
    ring
  have hnear : |(speeds c g h j 1 1 1 4-speeds c g h j 1 1 1 0)*cutOpening g h a b-
      ((wholeLap m a b e 1 1 1 4-wholeLap m a b e 1 1 1 0+2 : ℤ) : ℝ)| < 1/8 := by
    rw [abs_lt]
    push_cast at hf4 ⊢
    constructor <;> linarith
  have hw4 : InWay |speeds c g h j 1 1 1 4-speeds c g h j 1 1 1 0| (cutOpening g h a b) := by
    rw [abs_of_pos hpos4]
    exact lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (wholeLap m a b e 1 1 1 4-wholeLap m a b e 1 1 1 0+2)) hnear
  have hop4 : nextOpening |speeds c g h j 1 1 1 4-speeds c g h j 1 1 1 0| (cutOpening g h a b)=
      fourOpening g h j m a b e := by
    rw [abs_of_pos hpos4,nextOpening_eq hnear,hD4,hN4]
    dsimp [fourOpening]
    push_cast
    congr 1
    ring
  have hmem : |speeds c g h j 1 1 1 4-speeds c g h j 1 1 1 0| ∈
      disparitySet (speeds c g h j 1 1 1) 0 := mem_disparitySet.mpr ⟨4,by decide,rfl⟩
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
  have htime : cutOpening g h a b ≤ fourOpening g h j m a b e := by
    rw [←hop4]
    exact (lt_nextOpening (by rw [abs_of_pos hpos4]; exact hpos4) hw4).le
  have hclear := four_clear c g h j hgpos hhpos hjpos m a b e hg hh hj hlo hhi hcut hsingle
  refine Or.inr ⟨_,hmem,hw4,hop4.symm,?_⟩
  intro d hd hwD
  exact nextOpening_le_of_lonely hpos hclear htime hd hwD

#print axioms cut_identity
#print axioms return_move
end Fresh.FourBlockFourReturnMove
