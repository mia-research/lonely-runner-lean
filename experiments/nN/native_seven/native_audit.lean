import LonelyRunner.LRC.Spec.OrderSevenNativeN

/-! Exact signatures and transitive axiom reports for the native completion. -/

example : LRC.O7Abs.AbsU5 := LRC.O7U5.absU5
example : LRC.O7Abs.AbsP1 := LRC.O7U5.absP1
example : LRC.O7Abs.AbsP2 := LRC.O7P2.absP2
example : LRC.SpecN.ExistenceAtN 7 := LRC.OrderSevenNative.existenceAtN_seven
example : LRC.SpecN.LonelyRunnerAtN 7 := LRC.OrderSevenNative.lonelyRunnerAtN_seven

#print axioms LRC.O7U5.absU5
#print axioms LRC.O7U5.absP1
#print axioms LRC.O7P2.absP2
#print axioms LRC.OrderSevenNative.lonely_seven_nat
#print axioms LRC.OrderSevenNative.existenceAtN_seven
#print axioms LRC.OrderSevenNative.lonelyRunnerAtN_seven

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let (_, deps) := ((CollectAxioms.collect
    ``LRC.OrderSevenNative.lonelyRunnerAtN_seven).run env).run {}
  let forbidden := deps.visited.toArray.filter fun n =>
    let s := n.toString
    s.startsWith "LRC.SmallN." || s.startsWith "LRC.IntLRC" ||
      s.startsWith "IntLRC7BS." || s.startsWith "BHK." ||
      s == "LRC.OrderSevenN.lonely_seven_nat" ||
      s == "LRC.OrderSevenN.existenceAtN_seven" ||
      s == "LRC.OrderSevenN.lonelyRunnerAtN_seven"
  unless forbidden.isEmpty do
    throwError "Classical proof dependency: {forbidden}"
  logInfo m!"Native dependency audit: {deps.visited.size} declarations; no listed classical endpoints"
