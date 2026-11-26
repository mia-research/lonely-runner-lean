import Fresh.FourBlockShortAnchorArrangement

/-! Actual native moves to any of the seven original short-packet opening
roles. Captured competitors are retained through derived target clearance. -/
namespace Fresh.FourBlockShortOpeningMoves
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour Fresh.FourBlockShortTail
  Fresh.FourBlockShortOpening

theorem capture_opening (c g h j : ℝ) (p q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e : ℤ) (u : Fin 7) (z : ℤ) (Q : ℝ)
    (hlo : (z : ℝ)-1/8 < reading c g h j p q r u*Q-(lap m a b e p q r u : ℝ))
    (hhi : reading c g h j p q r u*Q-(lap m a b e p q r u : ℝ) < (z : ℝ)+1/8) :
    InWay |reading c g h j p q r u| Q ∧
    nextOpening |reading c g h j p q r u| Q=opening c g h j p q r m a b e z u ∧
    Q < opening c g h j p q r m a b e z u := by
  have hp := reading_pos c g h j p q r hq hr hg hh hj u
  have hnear : |reading c g h j p q r u*Q-((lap m a b e p q r u+z : ℤ) : ℝ)| < 1/8 := by
    rw [abs_lt]
    push_cast
    constructor <;> linarith
  have hw : InWay |reading c g h j p q r u| Q := by
    rw [abs_of_pos hp]
    exact lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (lap m a b e p q r u+z)) hnear
  have hop : nextOpening |reading c g h j p q r u| Q=opening c g h j p q r m a b e z u := by
    rw [abs_of_pos hp,nextOpening_eq hnear]
    rfl
  refine ⟨hw,hop,?_⟩
  rw [←hop]
  exact lt_nextOpening (abs_pos.mpr (ne_of_gt hp)) hw

theorem opening_move (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 5)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e rho unitLap window : ℤ)
    (u : Fin 7) (role : Fin 6) (L : Fin 4 → ℤ)
    (hc : PacketBands c g h j p q r m a b e unitLap window role (opening c g h j p q r m a b e rho u))
    (hb : RemainingCutBands c g h j p q r m a b e (opening c g h j p q r m a b e rho u) L u) (Q : ℝ)
    (hlo : (rho : ℝ)-1/8 < reading c g h j p q r u*Q-(lap m a b e p q r u : ℝ))
    (hhi : reading c g h j p q r u*Q-(lap m a b e p q r u : ℝ) < (rho : ℝ)+1/8) :
    IsMove (disparitySet (speeds c g h j p q r) 0) Q (opening c g h j p q r m a b e rho u) := by
  obtain ⟨hw,hop,ht⟩ := capture_opening c g h j p q r hq hr hg hh hj m a b e u rho Q hlo hhi
  have hmem : |reading c g h j p q r u| ∈ disparitySet (speeds c g h j p q r) 0 := by
    refine mem_disparitySet.mpr ⟨openingIndex u,?_,rfl⟩
    intro he
    have hh := congrArg Fin.val he
    dsimp [openingIndex] at hh
    omega
  exact Fresh.FourBlockPacketFrameMoves.move_at_supplied_opening
    (Fresh.FourBlockPacketFrameMoves.native_readings_positive c g h j p q r hq hr hg hh hj) hmem hw hop
    (opening_clear c g h j p q r hp hq hr hs hg hh hj m a b e rho unitLap window u role L hc hb)

#print axioms capture_opening
#print axioms opening_move
end Fresh.FourBlockShortOpeningMoves
