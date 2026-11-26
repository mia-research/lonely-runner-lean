-- PORTED 2026-10-25 (imports renamed only) from LonelyRunner/LonelyRunner/LRC/Spec/RealSevenN.lean
import Fresh.Nv_MergeSixN
import Fresh.Nv_OrderSevenN
import Fresh.Nv_RealSixN

/-! Order seven for real speeds, transferring the classical integer theorem. -/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.OrderSevenN

open MomentIterationN LRC.SpecN ConstructionN LRC.Stepping LRC.OrderFiveN LRC.OrderSixN

/-- **Order seven, real speeds.**  Every set of at most six positive real disparities is lonely at
`1/7`. -/
theorem existenceAtN_seven : ExistenceAtN 7 :=
  LRC.RealTransferN.existenceAtN_of_nat (n := 4) lonely_seven_nat existenceAtN_six

/-- **The Lonely Runner Conjecture at seven runners**, for every injective arrangement of real
speeds, proved inside the framework. -/
theorem lonelyRunnerAtN_seven : LonelyRunnerAtN 7 :=
  lonelyRunnerAtN_of_existence existenceAtN_seven

end LRC.OrderSevenN
