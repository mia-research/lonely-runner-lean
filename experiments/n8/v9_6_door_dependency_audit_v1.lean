/-
DOES THE ARRANGEMENT PATH DEPEND ON `ExistenceAt8`?

The question this answers: the arrangement rebuild could have relabelled the difference-set form
rather than replaced it.  A doc comment cannot settle that.  This walks the FULL transitive constant
dependency of each arrangement-level result and reports whether any difference-set-form constant is
reachable from it.  `[]` means that constant is not used, anywhere, at any depth.
-/
import LonelyRunner.LRC.Spec.Doors

open Lean Elab Command

def transitiveDeps (env : Environment) (start : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack : List Name := [start]
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for c in ci.type.getUsedConstants do stack := c :: stack
      if let some val := ci.value? then
        for c in val.getUsedConstants do stack := c :: stack
  return seen

/-- The difference-set form and everything stated on it. -/
def suspects : List Name :=
  [`LRC.Spec.ExistenceAt8, `LRC.Spec.ExistenceAt8_cascade, `LRC.Spec.ExistenceAt8_flank,
   `LRC.Spec.ExistenceAt8_congruence, `LRC.Spec.CascadeCapped, `LRC.Spec.FiniteActiveMembership,
   `LRC.Spec.ThreeLargestFlanks, `LRC.Spec.target_forms_agree, `LRC.Spec.target_flank_agrees,
   `LRC.Spec.existence_of_capped, `LRC.Spec.capped_of_existence, `LRC.Spec.cascade_of_FAM,
   `LRC.Spec.FAM_of_existence, `LRC.Spec.FAM_iff_existence,
   `LRC.Spec.lonelyRunnerAt8_of_existence, `LRC.Spec.exists_lonely_of_card_le_three]

def audited : List Name :=
  [`LRC.Spec.LonelyRunnerAt8, `LRC.Spec.ExistenceOnArrangements,
   `LRC.Spec.lonelyRunnerAt8_iff_existenceOnArrangements,
   `LRC.Spec.lonelyRunnerAt8_iff_arrangement,
   `Arrangement.LonelyAt, `Arrangement.InWay, `Arrangement.lonelyAt_iff_neighbours,
   `Arrangement.inWay_comm, `Arrangement.lonelyAt_add_const, `Arrangement.lonelyAt_const_mul,
   `Arrangement.lonelyAt_iff_lonely_diffSet, `Arrangement.exists_lonelyAt_iff_flank,
   `Arrangement.exists_lonelyAt_iff_bounded, `Arrangement.lonelyAt_named_instant,
   `LRC.Spec.DoorFlank, `LRC.Spec.DoorArrives, `LRC.Spec.DoorCapped, `LRC.Spec.DoorFAM,
   `LRC.Spec.doorFlank_iff, `LRC.Spec.doorArrives_iff, `LRC.Spec.doorCapped_iff,
   `LRC.Spec.doorFAM_iff, `LRC.Spec.doors_agree,
   `LRC.Spec.lonelyRunnerAt8_of_doorFlank, `LRC.Spec.lonelyRunnerAt8_of_doorArrives,
   `LRC.Spec.lonelyRunnerAt8_of_doorCapped, `LRC.Spec.lonelyRunnerAt8_of_doorFAM,
   `LRC.Spec.blockDegree, `LRC.Spec.lonelyAt_iff_blockDegree_zero, `LRC.Spec.sum_blockDegree,
   `LRC.Spec.existenceOnArrangements_iff_isolated]

run_cmd do
  let env ← getEnv
  let mut anyBad := false
  for t in audited do
    if (env.find? t).isNone then
      logError m!"MISSING: {t}"
      anyBad := true
    else
      let deps := transitiveDeps env t
      let bad := suspects.filter (fun s => deps.contains s)
      if bad.isEmpty then
        logInfo m!"clean  {t}"
      else
        anyBad := true
        logError m!"USES   {t} -> {bad}"
  if anyBad then logError m!"AUDIT FAIL" else logInfo m!"AUDIT PASS: no audited declaration reaches the difference-set form."

/-
The audit above is MECHANICAL: it proves no audited declaration reaches the difference-set form by
name, at any depth.  It cannot tell whether the generalisation was moved somewhere else under
another name -- that is a question about the STATEMENTS, so the statements are printed verbatim
below.  What to look for: a `∀ ds : Finset ℝ` binder, or a `card ≤ 7` hypothesis.  Neither belongs
in a statement about an arrangement.
-/
#print LRC.Spec.LonelyRunnerAt8
#print LRC.Spec.ExistenceOnArrangements
#print Arrangement.LonelyAt
#print LRC.Spec.LonelyForSubject
#print LRC.Spec.DoorFlank
#print LRC.Spec.DoorArrives
#print LRC.Spec.DoorCapped
#print LRC.Spec.DoorFAM
#print LRC.Spec.DoorThreeLargest
#print Arrangement.diffSet
#print LRC.Spec.blockDegree

/-
THE FULL DEFINITION CHAIN.

Printing a door statement that contains `firstReading`, `diffSet` or `move` and calling it a frame
check is no check at all: the reader cannot see through the opaque term.  Every definition a door
statement names is printed below, down to `circDist`, so nothing in a door is taken on trust.
-/
#print Arrangement.sep
#print Arrangement.InWay
#print circDist
#print Flanks.flankOpening
#print LRC.Spec.leastDisp
#print LRC.Spec.firstReading
#print MomentIterationN.inWay
#print MomentIterationN.nextOpening
#print MomentIterationN.move
