import Fresh.FourBlockInnerExit
import Fresh.FourBlockInnerReturnMove

namespace Fresh.FourBlockInnerCaptureBounds
open Fresh Fresh.FourBlockNeighbour Fresh.FourBlockEndpointCapture
  Fresh.FourBlockLongTailPhase Fresh.FourBlockOuterReturnBounds

theorem strict_capture_face (g h j : ℝ) (m a b e : ℤ)
    (hsmall : g+h+j ≤ 3) (hRhi : remainder g h j m a b e ≤ 1) :
    g+h+j+8*remainder g h j m a b e < 11 := by
  have hle : g+h+j+8*remainder g h j m a b e ≤ 11 := by linarith
  by_contra hn
  have hs : g+h+j=3 := by linarith
  have hr : remainder g h j m a b e=1 := by linarith
  have heq : (8 : ℝ)*(3*(m : ℝ)-(a : ℝ)-(b : ℝ)-(e : ℝ))=1 := by
    dsimp [remainder] at hr
    rw [hs] at hr
    linarith
  have heq' : (8 : ℤ)*(3*m-a-b-e)=1 := by exact_mod_cast heq
  omega

theorem inner_capture_bounds (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e : ℤ) (hsmall : g+h+j ≤ 3)
    (hRhi : remainder g h j m a b e ≤ 1)
    (hhi : 13 ≤ 2*(g+h+j)+8*remainder g h j m a b e) :
    (m : ℝ)+9/32 < returnOpening g h j m a b e ∧
    returnOpening g h j m a b e < (m : ℝ)+5/16 := by
  have hd := return_delta g h j hg hh hj m a b e
  have hp : 0 < 4+g+h+j := by linarith
  have hf := (Fresh.FourBlockInnerExit.earlier_faces g h j m a b e hsmall hhi).2
  constructor
  · have hprod := mul_nonneg (by linarith : 0 ≤ 3-(g+h+j))
      (by nlinarith [hd] : 0 ≤ returnOpening g h j m a b e-((m : ℝ)+1/8))
    nlinarith
  · nlinarith

#print axioms strict_capture_face
#print axioms inner_capture_bounds
end Fresh.FourBlockInnerCaptureBounds
