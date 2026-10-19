import LonelyRunner.LRC.Spec.MergeFiveN
import LonelyRunner.LRC.Spec.OrderSixWholeN

/-! Order six for real speeds, by the shared integer-to-real transfer. -/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.OrderSixN

open MomentIterationN LRC.SpecN ConstructionN LRC.Stepping LRC.OrderFiveN

/-- **Order six, real speeds.**  Every set of at most five positive real disparities is lonely at
`1/6`. -/
theorem existenceAtN_six : ExistenceAtN 6 :=
  LRC.RealTransferN.existenceAtN_of_nat (n := 3) lonely_six_nat existenceAtN_five

/-- **The Lonely Runner Conjecture at six runners**, for every injective arrangement of real
speeds, proved inside the framework. -/
theorem lonelyRunnerAtN_six : LonelyRunnerAtN 6 :=
  lonelyRunnerAtN_of_existence existenceAtN_six

end LRC.OrderSixN
