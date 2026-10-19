import LonelyRunner.LRC.Spec.RealSevenGridN
import LonelyRunner.LRC.Spec.OrderSevenP1FinalN
import LonelyRunner.LRC.Spec.OrderSevenP2FinalN

/-!
# Order seven: the unconditional native framework interface

The three abstract finite obligations are discharged by the certificate proofs
`O7U5.absU5`, `O7U5.absP1`, and `O7P2.absP2`. The certificates use kernel
reduction and the proved checker soundness theorems. The integer argument is
the framework's grid, fold, and digit-extension argument. The real-speed
transfer uses the native order-six result through `RealSevenGridN`.

This module assembles those proofs without assuming the finite obligations.
-/

namespace LRC.OrderSevenNative

open MomentIterationN LRC.SpecN

/-- Every set of at most six positive natural disparities has a lonely time. -/
theorem lonely_seven_nat (S : Finset ℕ) (hpos : ∀ d ∈ S, 0 < d)
    (hcard : S.card ≤ 6) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (7 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) :=
  O7All.lonely_seven_nat_grid O7U5.absU5 O7U5.absP1 O7P2.absP2 S hpos hcard

/-- Every set of at most six positive real disparities has a lonely time. -/
theorem existenceAtN_seven : ExistenceAtN 7 :=
  OrderSevenGridR.existenceAtN_seven_grid O7U5.absU5 O7U5.absP1 O7P2.absP2

/-- The Lonely Runner Conjecture for seven runners with arbitrary real speeds. -/
theorem lonelyRunnerAtN_seven : LonelyRunnerAtN 7 :=
  OrderSevenGridR.lonelyRunnerAtN_seven_grid O7U5.absU5 O7U5.absP1 O7P2.absP2

end LRC.OrderSevenNative
