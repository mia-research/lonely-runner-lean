import LonelyRunner.LRC.Spec.PeriodReflectionN
import LonelyRunner.LRC.Spec.MaximalWindowTransportN

#print axioms LRC.PeriodReflection.next_return_data
#print axioms LRC.PeriodReflection.replacement_with_period_labels
#print axioms LRC.MaximalWindowTransport.rational_first_loss
#print axioms LRC.MaximalWindowTransport.replacement_at_first_loss

-- Audit proof dependencies, not merely imported modules or standard axioms.
-- Print all reachable project constants for human review.
open Lean in
run_cmd do
  let env ← getEnv
  let mut pending := #[``LRC.PeriodReflection.replacement_with_period_labels,
    ``LRC.MaximalWindowTransport.replacement_at_first_loss]
  let mut seen : NameSet := {}
  let mut project : Array Name := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    if n.toString.startsWith "LRC." then
      project := project.push n
    if let some ci := env.find? n then
      pending := pending ++ ci.type.getUsedConstants
      if let some val := ci.value? then
        pending := pending ++ val.getUsedConstants
  for n in project do
    logInfo m!"PROJECT_DEP {n}"
  logInfo m!"AUDITED_PROJECT_CONSTANTS {project.size}"
