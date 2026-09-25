import LonelyRunner.LRC.Spec.OrderSixSecFiveN
import LonelyRunner.LRC.Spec.OrderSixPropElevenEN

/-!
# BHK §5 at named instants

`OrderSixSecFiveN` ports BHK §5 in BHK's form: Case 5.1 and Proposition 11 are
argued by assuming every time is covered and deriving `False`. This file is the
same proof with the covering removed, as in `OrderSixPropElevenEN`: each lemma
that read the covering at an instant `τ` now reads `τ` (`found_or_blocked`),
and either `τ` is the lonely instant or BHK's argument continues. `lonely_5`
is then proved with no covering anywhere.

The lemmas that do not read the covering are used from `OrderSixSecFiveN`.
-/

open MeasureTheory Set

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.show false
set_option linter.style.multiGoal false
set_option linter.style.setOption false
set_option linter.flexible false

namespace LRC.OrderSixN.S7.Named

open LRC.OrderSixN

