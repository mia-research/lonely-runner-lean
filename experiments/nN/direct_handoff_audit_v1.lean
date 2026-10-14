import LonelyRunner.LRC.Spec.DirectHandoffN

#print axioms LRC.DirectHandoff.successor_bands
#print axioms LRC.DirectHandoff.successor_clear
#print axioms LRC.DirectHandoff.recapture_requires_drop
#print axioms LRC.DirectHandoff.return_exit_clears_pair
#print axioms LRC.DirectHandoff.nextOpening_bands
#print axioms LRC.DirectHandoff.move_preserves_setter
#print axioms LRC.DirectHandoff.move_recapture_requires_small_setter

-- Exact regression: the ratio restriction cannot simply be discarded.
-- b=13/4 opens at r=49/26, c=1 is captured there about J=2.
-- At c's opening 17/8, b reads 221/32, past its 6+7/8 closing.
example : (13 / 4 : ℝ) * (49 / 26) = 6 + 1 / 8 ∧
    (2 - 1 / 8 : ℝ) < 49 / 26 ∧ (49 / 26 : ℝ) < 2 + 1 / 8 ∧
    (13 / 4 : ℝ) * (17 / 8) = 221 / 32 ∧
    (6 + 7 / 8 : ℝ) < 221 / 32 ∧ (221 / 32 : ℝ) < 7 := by
  norm_num

open Lean in
run_cmd do
  let env ← getEnv
  let mut pending := #[``LRC.DirectHandoff.return_exit_clears_pair,
    ``LRC.DirectHandoff.move_preserves_setter,
    ``LRC.DirectHandoff.move_recapture_requires_small_setter]
  let mut seen : NameSet := {}
  let mut project : Array Name := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    if n.toString.startsWith "LRC." || n.toString.startsWith "MomentIterationN." ||
        n.toString.startsWith "ConstructionN." then
      project := project.push n
    if let some ci := env.find? n then
      pending := pending ++ ci.type.getUsedConstants
      if let some val := ci.value? then
        pending := pending ++ val.getUsedConstants
  for n in project do
    logInfo m!"PROJECT_DEP {n}"
  logInfo m!"AUDITED_PROJECT_CONSTANTS {project.size}"
