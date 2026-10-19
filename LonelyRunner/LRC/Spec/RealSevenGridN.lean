import LonelyRunner.LRC.Spec.MergeSixN
import LonelyRunner.LRC.Spec.RealSixN
import LonelyRunner.LRC.Spec.OrderSevenAllN

/-!
Order seven for real speeds from the native grid route and the shared integer-to-real transfer.
The three finite statements remain explicit hypotheses here; `OrderSevenNativeN` supplies their
kernel-checked certificates. The classical `OrderSevenN` integer theorem is not imported.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.OrderSevenGridR

open MomentIterationN LRC.SpecN ConstructionN LRC.Stepping LRC.OrderFiveN LRC.OrderSixN LRC.OrderSevenN

instance fact_two_le_seven_grid : Fact (2 ≤ 7) := ⟨by norm_num⟩

/-- Order seven for real speeds from any whole-number order-seven statement via the shared transfer theorem. -/
theorem existenceAtN_seven_of_nat
    (hnat : ∀ S : Finset ℕ, (∀ d ∈ S, 0 < d) → S.card ≤ 6 →
      ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (7 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t)) : ExistenceAtN 7 :=
  LRC.RealTransferN.existenceAtN_of_nat (n := 4) hnat existenceAtN_six

/-- **Order seven, real speeds, on the framework's own route** (given the three finite statements). -/
theorem existenceAtN_seven_grid (hU5 : LRC.O7Abs.AbsU5) (hP1 : LRC.O7Abs.AbsP1) (hP2 : LRC.O7Abs.AbsP2) :
    ExistenceAtN 7 :=
  existenceAtN_seven_of_nat (LRC.O7All.lonely_seven_nat_grid hU5 hP1 hP2)

/-- **The Lonely Runner Conjecture at seven runners**, on the framework's own route (given the three finite
statements). -/
theorem lonelyRunnerAtN_seven_grid (hU5 : LRC.O7Abs.AbsU5) (hP1 : LRC.O7Abs.AbsP1) (hP2 : LRC.O7Abs.AbsP2) :
    LonelyRunnerAtN 7 :=
  lonelyRunnerAtN_of_existence (existenceAtN_seven_grid hU5 hP1 hP2)

end LRC.OrderSevenGridR
