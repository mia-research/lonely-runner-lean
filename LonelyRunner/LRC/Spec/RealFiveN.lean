import LonelyRunner.LRC.Spec.RealTransferN

/-! Order five: specializations of the shared merge and real-speed transfer. -/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.OrderFiveN

open MomentIterationN LRC.SpecN ConstructionN LRC.Stepping

variable {m : ℕ}

/-- **The exact merge, general.**  Four non-zero rows, not all parallel, have a whole-number
direction whose readings are all non-zero, with two of them equal up to sign. -/
theorem exists_merge_model_gen (a : Fin 4 → Fin m → ℤ) (hnz : ∀ i, a i ≠ 0)
    (hnp : ∃ i j, ¬ Parallel (a i) (a j)) :
    ∃ y : Fin m → ℤ, (∀ i, dotZ y (a i) ≠ 0) ∧
      ∃ i j, i ≠ j ∧ (dotZ y (a i)).natAbs = (dotZ y (a j)).natAbs :=
  LRC.OrderSevenN.exists_merge_model_all a hnz hnp

/-- **Order five, real speeds.**  Every set of at most four positive real disparities is lonely at
`1/5`. -/
theorem existenceAtN_five : ExistenceAtN 5 :=
  LRC.RealTransferN.existenceAtN_of_nat (n := 2) lonely_five_nat existenceAtN_four

/-- **The Lonely Runner Conjecture at five runners**, for every injective arrangement of real
speeds, proved inside the framework. -/
theorem lonelyRunnerAtN_five : LonelyRunnerAtN 5 :=
  lonelyRunnerAtN_of_existence existenceAtN_five

end LRC.OrderFiveN
