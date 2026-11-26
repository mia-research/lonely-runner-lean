import Fresh.FourBlockFourReturnMove

/-! Eight forced native setters, including two actual endpoint returns.
All seven original readings participate in every move. -/
namespace Fresh.FourBlockFourReturnEpisode
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailBounds Fresh.FourBlockLongTailPhase
  Fresh.FourBlockOuterReturnBounds Fresh.FourBlockInnerExit
  Fresh.FourBlockInnerCutMove Fresh.FourBlockFourReturnExit

theorem native_four_return_episode (c g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hsmall : g+h+j ≤ 3)
    (hlo : 5*(g+h+j)+24*remainder g h j m a b e ≤ 39)
    (hinner : 13 ≤ 2*(g+h+j)+8*remainder g h j m a b e)
    (hgate : j*innerOpening g h j a b e-(e : ℝ) < 1/4)
    (hfourlo : 3*(g+h+j)+8*remainder g h j m a b e ≤ 17)
    (hfourhi : 49 ≤ 11*(g+h+j)+24*remainder g h j m a b e)
    (hcut : j*fourOpening g h j m a b e-(e : ℝ)+(fourOpening g h j m a b e-(m : ℝ)) ≤ 1)
    (hsingle : g*fourOpening g h j m a b e-(a : ℝ) ≤ 7/8 ∨
      (9/8 : ℝ) ≤ g*fourOpening g h j m a b e-(a : ℝ))
    (hcaplo : (3/4 : ℝ) < j*cutOpening g h a b-(e : ℝ)+(cutOpening g h a b-(m : ℝ)))
    (hcaphi : j*cutOpening g h a b-(e : ℝ)+(cutOpening g h a b-(m : ℝ)) < 1)
    (hcap : (7/8 : ℝ) < remainder g h j m a b e) :
    let E := disparitySet (speeds c g h j 1 1 1) 0
    IsMove E ((m : ℝ)+1/8) (outerOpening g h j m a b e) ∧
    IsMove E (outerOpening g h j m a b e) (packetOpening g h j m a b e 1) ∧
    IsMove E (packetOpening g h j m a b e 1) (packetOpening g h j m a b e 2) ∧
    IsMove E (packetOpening g h j m a b e 2) (packetOpening g h j m a b e 3) ∧
    IsMove E (packetOpening g h j m a b e 3) (returnOpening g h j m a b e) ∧
    IsMove E (returnOpening g h j m a b e) (innerOpening g h j a b e) ∧
    IsMove E (innerOpening g h j a b e) (cutOpening g h a b) ∧
    IsMove E (cutOpening g h a b) (fourOpening g h j m a b e) ∧
    LonelyAt E (fourOpening g h j m a b e) := by
  dsimp only
  obtain ⟨hfirst,hsecond,hthird,hfourth,hreturn,hinnerMove⟩ :=
    Fresh.FourBlockInnerEpisode.inner_prefix c g h j hgpos hhpos hjpos m a b e
      hg hh hj hsum hsmall hinner hcap
  exact ⟨hfirst,hsecond,hthird,hfourth,hreturn,hinnerMove,
    cut_move c g h j hgpos hhpos hjpos m a b e hg hh hj hlo hinner hgate,
    Fresh.FourBlockFourReturnMove.return_move c g h j hgpos hhpos hjpos m a b e
      hg hh hj hfourlo hfourhi hcut hsingle hcaplo hcaphi,
    four_clear c g h j hgpos hhpos hjpos m a b e hg hh hj hfourlo hfourhi hcut hsingle⟩

#print axioms native_four_return_episode
end Fresh.FourBlockFourReturnEpisode
