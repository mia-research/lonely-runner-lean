import Fresh.FourBlockInnerMove
import Fresh.FourBlockInnerCutMove

/-! The complete six-setter reference episode into the inner-anchor exit.
The reference time is supplied; no visit by a separately started path is asserted. -/
namespace Fresh.FourBlockInnerEpisode
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailBounds Fresh.FourBlockLongTailPhase
  Fresh.FourBlockOuterReturnBounds Fresh.FourBlockInnerExit
  Fresh.FourBlockInnerCaptureBounds Fresh.FourBlockInnerMove

theorem inner_prefix (c g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hsmall : g+h+j ≤ 3)
    (hinner : 13 ≤ 2*(g+h+j)+8*remainder g h j m a b e)
    (hcap : (7/8 : ℝ) < remainder g h j m a b e) :
    let E := disparitySet (speeds c g h j 1 1 1) 0
    IsMove E ((m : ℝ)+1/8) (outerOpening g h j m a b e) ∧
    IsMove E (outerOpening g h j m a b e) (packetOpening g h j m a b e 1) ∧
    IsMove E (packetOpening g h j m a b e 1) (packetOpening g h j m a b e 2) ∧
    IsMove E (packetOpening g h j m a b e 2) (packetOpening g h j m a b e 3) ∧
    IsMove E (packetOpening g h j m a b e 3) (returnOpening g h j m a b e) ∧
    IsMove E (returnOpening g h j m a b e) (innerOpening g h j a b e) := by
  dsimp only
  obtain ⟨hRlo,hRhi⟩ := native_remainder_band g h j m a b e hg hh hj hsum
  have hhi := (earlier_faces g h j m a b e hsmall hinner).1
  have hactual := strict_capture_face g h j m a b e hsmall hRhi
  have hcontinue : 9 < g+h+j+8*remainder g h j m a b e := by linarith
  rcases Fresh.FourBlockLongTailEpisode.native_episode c g h j 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hgpos hhpos hjpos m a b e hg hh hj hsum with
    ⟨hedge,hclear⟩|⟨hcap',hfirst,hsecond,hthird,hexit,hcont⟩
  · exfalso
    linarith
  · exact ⟨hfirst,hsecond,hthird,hcont (not_le_of_gt hcontinue),
      Fresh.FourBlockInnerReturnMove.return_move c g h j hgpos hhpos hjpos m a b e hg hh hj hsum hactual hhi,
      inner_move c g h j hgpos hhpos hjpos m a b e hg hh hj hsum hsmall hinner⟩

theorem native_inner_episode (c g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hsmall : g+h+j ≤ 3)
    (hlo : 5*(g+h+j)+24*remainder g h j m a b e ≤ 39)
    (hinner : 13 ≤ 2*(g+h+j)+8*remainder g h j m a b e)
    (hgate : (1/4 : ℝ) ≤ j*innerOpening g h j a b e-(e : ℝ))
    (hcap : (7/8 : ℝ) < remainder g h j m a b e) :
    let E := disparitySet (speeds c g h j 1 1 1) 0
    IsMove E ((m : ℝ)+1/8) (outerOpening g h j m a b e) ∧
    IsMove E (outerOpening g h j m a b e) (packetOpening g h j m a b e 1) ∧
    IsMove E (packetOpening g h j m a b e 1) (packetOpening g h j m a b e 2) ∧
    IsMove E (packetOpening g h j m a b e 2) (packetOpening g h j m a b e 3) ∧
    IsMove E (packetOpening g h j m a b e 3) (returnOpening g h j m a b e) ∧
    IsMove E (returnOpening g h j m a b e) (innerOpening g h j a b e) ∧
    LonelyAt E (innerOpening g h j a b e) := by
  dsimp only
  obtain ⟨hRlo,hRhi⟩ := native_remainder_band g h j m a b e hg hh hj hsum
  have hhi := (earlier_faces g h j m a b e hsmall hinner).1
  have hactual := strict_capture_face g h j m a b e hsmall hRhi
  have hcontinue : 9 < g+h+j+8*remainder g h j m a b e := by linarith
  rcases Fresh.FourBlockLongTailEpisode.native_episode c g h j 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hgpos hhpos hjpos m a b e hg hh hj hsum with
    ⟨hedge,hclear⟩|⟨hcap',hfirst,hsecond,hthird,hexit,hcont⟩
  · exfalso
    linarith
  · exact ⟨hfirst,hsecond,hthird,hcont (not_le_of_gt hcontinue),
      Fresh.FourBlockInnerReturnMove.return_move c g h j hgpos hhpos hjpos m a b e hg hh hj hsum hactual hhi,
      inner_move c g h j hgpos hhpos hjpos m a b e hg hh hj hsum hsmall hinner,
      inner_clear c g h j hgpos hhpos hjpos m a b e hg hh hj hlo hinner hgate⟩

#print axioms inner_prefix
#print axioms native_inner_episode
end Fresh.FourBlockInnerEpisode
