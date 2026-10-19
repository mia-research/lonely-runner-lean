import LonelyRunner.LRC.Spec.RealFiveN

/-! Five-row specialization of the shared exact merge. -/

namespace LRC.OrderSixN
open LRC.OrderFiveN
variable {m : ℕ}

/-- **The exact merge, five rows.**  Five non-zero rows, not all parallel, have a whole-number
direction whose readings are all non-zero, with two of them equal up to sign. -/
theorem exists_merge_model_five (a : Fin 5 → Fin m → ℤ) (hnz : ∀ i, a i ≠ 0)
    (hnp : ∃ i j, ¬ Parallel (a i) (a j)) :
    ∃ y : Fin m → ℤ, (∀ i, dotZ y (a i) ≠ 0) ∧
      ∃ i j, i ≠ j ∧ (dotZ y (a i)).natAbs = (dotZ y (a j)).natAbs :=
  LRC.OrderSevenN.exists_merge_model_all a hnz hnp

end LRC.OrderSixN
