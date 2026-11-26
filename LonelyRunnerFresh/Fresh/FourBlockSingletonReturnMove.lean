import Fresh.FourBlockSingletonReturnArrangement

/-! The singleton can win from an actual captured entry, including a
competition with runner4. All other openings are retained by the native exit. -/
namespace Fresh.FourBlockSingletonReturnMove
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailPhase Fresh.FourBlockSingletonReturnExit

theorem singleton_move_from (c g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e : ℤ) (t : ℝ)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (htau : (m : ℝ)+1/2 ≤ singletonOpening g a)
    (hinner : 1 ≤ tailCut g h j a b e+(singletonOpening g a-(m : ℝ)))
    (houter : tailCut g h j a b e+4*(singletonOpening g a-(m : ℝ)) ≤ 11/4)
    (hcaplo : (7/8 : ℝ) < g*t-(a : ℝ))
    (hcaphi : g*t-(a : ℝ) < 9/8) :
    IsMove (disparitySet (speeds c g h j 1 1 1) 0)
      t (singletonOpening g a) := by
  have hD1 : speeds c g h j 1 1 1 1-speeds c g h j 1 1 1 0=g := by norm_num [speeds]
  have hpos1 : 0 < speeds c g h j 1 1 1 1-speeds c g h j 1 1 1 0 := by rw [hD1]; exact hgpos
  have hnear : |(speeds c g h j 1 1 1 1-speeds c g h j 1 1 1 0)*t-
      ((a+1 : ℤ) : ℝ)| < 1/8 := by
    rw [abs_lt]
    rw [hD1]
    push_cast
    constructor <;> linarith
  have hw1 : InWay |speeds c g h j 1 1 1 1-speeds c g h j 1 1 1 0| t := by
    rw [abs_of_pos hpos1]
    exact lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (a+1)) hnear
  have hop1 : nextOpening |speeds c g h j 1 1 1 1-speeds c g h j 1 1 1 0| t=
      singletonOpening g a := by
    rw [abs_of_pos hpos1,nextOpening_eq hnear,hD1]
    dsimp [singletonOpening]
    push_cast
    congr 1
    ring
  have hmem : |speeds c g h j 1 1 1 1-speeds c g h j 1 1 1 0| ∈
      disparitySet (speeds c g h j 1 1 1) 0 := mem_disparitySet.mpr ⟨1,by decide,rfl⟩
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
  have htime : t ≤ singletonOpening g a := by
    rw [←hop1]
    exact (lt_nextOpening (by rw [abs_of_pos hpos1]; exact hpos1) hw1).le
  have hclear := singleton_clear c g h j hgpos hhpos hjpos m a b e hh hj htau hinner houter
  refine Or.inr ⟨_,hmem,hw1,hop1.symm,?_⟩
  intro d hd hwD
  exact nextOpening_le_of_lonely hpos hclear htime hd hwD

#print axioms singleton_move_from
end Fresh.FourBlockSingletonReturnMove
