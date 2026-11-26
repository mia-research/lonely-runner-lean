import Fresh.FourBlockSingletonReturnMove

/-! Eight forced native setters, including the competing singleton return.
All seven original readings participate in every move. -/
namespace Fresh.FourBlockSingletonReturnEpisode
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailBounds Fresh.FourBlockLongTailPhase
  Fresh.FourBlockOuterReturnBounds Fresh.FourBlockInnerExit
  Fresh.FourBlockInnerCutMove Fresh.FourBlockSingletonReturnExit

theorem native_singleton_return_episode (c g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hsmall : g+h+j ≤ 3)
    (hlo : 5*(g+h+j)+24*remainder g h j m a b e ≤ 39)
    (hinner : 13 ≤ 2*(g+h+j)+8*remainder g h j m a b e)
    (hgate : j*innerOpening g h j a b e-(e : ℝ) < 1/4)
    (htau : (m : ℝ)+1/2 ≤ singletonOpening g a)
    (hpacketInner : 1 ≤ tailCut g h j a b e+(singletonOpening g a-(m : ℝ)))
    (hpacketOuter : tailCut g h j a b e+4*(singletonOpening g a-(m : ℝ)) ≤ 11/4)
    (hcaplo : (7/8 : ℝ) < g*cutOpening g h a b-(a : ℝ))
    (hcaphi : g*cutOpening g h a b-(a : ℝ) < 9/8)
    (hcap : (7/8 : ℝ) < remainder g h j m a b e) :
    let E := disparitySet (speeds c g h j 1 1 1) 0
    IsMove E ((m : ℝ)+1/8) (outerOpening g h j m a b e) ∧
    IsMove E (outerOpening g h j m a b e) (packetOpening g h j m a b e 1) ∧
    IsMove E (packetOpening g h j m a b e 1) (packetOpening g h j m a b e 2) ∧
    IsMove E (packetOpening g h j m a b e 2) (packetOpening g h j m a b e 3) ∧
    IsMove E (packetOpening g h j m a b e 3) (returnOpening g h j m a b e) ∧
    IsMove E (returnOpening g h j m a b e) (innerOpening g h j a b e) ∧
    IsMove E (innerOpening g h j a b e) (cutOpening g h a b) ∧
    IsMove E (cutOpening g h a b) (singletonOpening g a) ∧
    LonelyAt E (singletonOpening g a) := by
  dsimp only
  obtain ⟨hfirst,hsecond,hthird,hfourth,hreturn,hinnerMove⟩ :=
    Fresh.FourBlockInnerEpisode.inner_prefix c g h j hgpos hhpos hjpos m a b e
      hg hh hj hsum hsmall hinner hcap
  exact ⟨hfirst,hsecond,hthird,hfourth,hreturn,hinnerMove,
    cut_move c g h j hgpos hhpos hjpos m a b e hg hh hj hlo hinner hgate,
    Fresh.FourBlockSingletonReturnMove.singleton_move_from c g h j hgpos hhpos hjpos m a b e
      (cutOpening g h a b) hh hj htau hpacketInner hpacketOuter hcaplo hcaphi,
    singleton_clear c g h j hgpos hhpos hjpos m a b e hh hj htau hpacketInner hpacketOuter⟩

#print axioms native_singleton_return_episode
end Fresh.FourBlockSingletonReturnEpisode
