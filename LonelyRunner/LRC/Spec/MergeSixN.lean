import LonelyRunner.LRC.Spec.MergeFiveN

/-! Six-row specialization of the shared exact merge. -/

namespace LRC.OrderSevenN
open LRC.OrderFiveN
variable {m : ℕ}

/-- **The exact merge, six rows**, the case order seven uses. -/
theorem exists_merge_model_six (a : Fin 6 → Fin m → ℤ) (hnz : ∀ i, a i ≠ 0)
    (hnp : ∃ i j, ¬ Parallel (a i) (a j)) :
    ∃ y : Fin m → ℤ, (∀ i, dotZ y (a i) ≠ 0) ∧
      ∃ i j, i ≠ j ∧ (dotZ y (a i)).natAbs = (dotZ y (a j)).natAbs :=
  exists_merge_model_all a hnz hnp

end LRC.OrderSevenN
