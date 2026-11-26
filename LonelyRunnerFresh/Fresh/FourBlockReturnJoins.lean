import Fresh.FourBlockSingletonReturnEpisode
import Fresh.FourBlockFourReturnEpisode

/-! Exact opening coincidence and packet-role exchange at the shared face. -/
namespace Fresh.FourBlockReturnJoins
open Fresh Fresh.FourBlockNeighbour Fresh.FourBlockEndpointCapture
  Fresh.FourBlockFourReturnExit Fresh.FourBlockSingletonReturnExit

theorem opening_join (g h j : ℝ) (hg : 0 < g) (m a b e : ℤ)
    (hface : g*fourOpening g h j m a b e-(a : ℝ)=9/8) :
    singletonOpening g a=fourOpening g h j m a b e := by
  have hid := singleton_identity g hg a
  nlinarith

theorem packet_faces_at_join (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e : ℤ)
    (hlo : 3*(g+h+j)+8*remainder g h j m a b e ≤ 17)
    (hhi : 49 ≤ 11*(g+h+j)+24*remainder g h j m a b e)
    (hface : g*fourOpening g h j m a b e-(a : ℝ)=9/8) :
    (m : ℝ)+1/2 ≤ singletonOpening g a ∧
    tailCut g h j a b e+(singletonOpening g a-(m : ℝ))=1 ∧
    tailCut g h j a b e+4*(singletonOpening g a-(m : ℝ)) ≤ 11/4 := by
  have hjoin := opening_join g h j hg m a b e hface
  obtain ⟨hPlo,hPhi⟩ := four_bounds g h j hg hh hj m a b e hlo hhi
  have hid := four_identity g h j hg hh hj m a b e
  have heq : tailCut g h j a b e+(singletonOpening g a-(m : ℝ))=1 := by
    dsimp [tailCut]
    rw [hjoin]
    push_cast at hid
    nlinarith only [hid,hface]
  refine ⟨by simpa only [hjoin] using hPlo,heq,?_⟩
  rw [hjoin] at heq ⊢
  linarith

#print axioms opening_join
#print axioms packet_faces_at_join
end Fresh.FourBlockReturnJoins
