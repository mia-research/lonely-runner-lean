import LonelyRunner.LRC.Spec.OrderSevenNativeN
import LonelyRunner.LRC.Spec.RealSevenN

/-! Regression statements and axiom reports for the shared merge/transfer refactor. -/

example : LRC.SpecN.ExistenceAtN 3 := LRC.SpecN.existenceAtN_three
example : LRC.SpecN.LonelyRunnerAtN 3 := LRC.SpecN.lonelyRunnerAtN_three
example : LRC.SpecN.ExistenceAtN 4 := LRC.SpecN.existenceAtN_four
example : LRC.SpecN.LonelyRunnerAtN 4 := LRC.SpecN.lonelyRunnerAtN_four
example : LRC.SpecN.ExistenceAtN 5 := LRC.OrderFiveN.existenceAtN_five
example : LRC.SpecN.LonelyRunnerAtN 5 := LRC.OrderFiveN.lonelyRunnerAtN_five
example : LRC.SpecN.ExistenceAtN 6 := LRC.OrderSixN.existenceAtN_six
example : LRC.SpecN.LonelyRunnerAtN 6 := LRC.OrderSixN.lonelyRunnerAtN_six
example : LRC.SpecN.ExistenceAtN 7 := LRC.OrderSevenNative.existenceAtN_seven
example : LRC.SpecN.LonelyRunnerAtN 7 := LRC.OrderSevenNative.lonelyRunnerAtN_seven
example : LRC.SpecN.ExistenceAtN 7 := LRC.OrderSevenN.existenceAtN_seven
example : LRC.SpecN.LonelyRunnerAtN 7 := LRC.OrderSevenN.lonelyRunnerAtN_seven

example {m : ℕ} (a : Fin 4 → Fin m → ℤ) (hnz : ∀ i, a i ≠ 0)
    (hnp : ∃ i j, ¬ LRC.OrderFiveN.Parallel (a i) (a j)) :
    ∃ y : Fin m → ℤ, (∀ i, LRC.OrderFiveN.dotZ y (a i) ≠ 0) ∧
      ∃ i j, i ≠ j ∧ (LRC.OrderFiveN.dotZ y (a i)).natAbs =
        (LRC.OrderFiveN.dotZ y (a j)).natAbs := LRC.OrderFiveN.exists_merge_model_gen a hnz hnp

example {m : ℕ} (a : Fin 5 → Fin m → ℤ) (hnz : ∀ i, a i ≠ 0)
    (hnp : ∃ i j, ¬ LRC.OrderFiveN.Parallel (a i) (a j)) :
    ∃ y : Fin m → ℤ, (∀ i, LRC.OrderFiveN.dotZ y (a i) ≠ 0) ∧
      ∃ i j, i ≠ j ∧ (LRC.OrderFiveN.dotZ y (a i)).natAbs =
        (LRC.OrderFiveN.dotZ y (a j)).natAbs := LRC.OrderSixN.exists_merge_model_five a hnz hnp

example {m : ℕ} (a : Fin 6 → Fin m → ℤ) (hnz : ∀ i, a i ≠ 0)
    (hnp : ∃ i j, ¬ LRC.OrderFiveN.Parallel (a i) (a j)) :
    ∃ y : Fin m → ℤ, (∀ i, LRC.OrderFiveN.dotZ y (a i) ≠ 0) ∧
      ∃ i j, i ≠ j ∧ (LRC.OrderFiveN.dotZ y (a i)).natAbs =
        (LRC.OrderFiveN.dotZ y (a j)).natAbs := LRC.OrderSevenN.exists_merge_model_six a hnz hnp

#print axioms LRC.RealTransferN.existenceAtN_of_nat
#print axioms LRC.OrderSevenN.exists_merge_model_all
#print axioms LRC.OrderFiveN.exists_merge_model_gen
#print axioms LRC.OrderSixN.exists_merge_model_five
#print axioms LRC.OrderSevenN.exists_merge_model_six
#print axioms LRC.SpecN.existenceAtN_three
#print axioms LRC.SpecN.lonelyRunnerAtN_three
#print axioms LRC.SpecN.existenceAtN_four
#print axioms LRC.SpecN.lonelyRunnerAtN_four
#print axioms LRC.OrderFiveN.existenceAtN_five
#print axioms LRC.OrderFiveN.lonelyRunnerAtN_five
#print axioms LRC.OrderSixN.existenceAtN_six
#print axioms LRC.OrderSixN.lonelyRunnerAtN_six
#print axioms LRC.OrderSevenNative.existenceAtN_seven
#print axioms LRC.OrderSevenNative.lonelyRunnerAtN_seven
#print axioms LRC.OrderSevenN.existenceAtN_seven
#print axioms LRC.OrderSevenN.lonelyRunnerAtN_seven
