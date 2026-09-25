import LonelyRunner.LRC.Spec.Order8SkeletonN

/-!
# One end is enough: the conjecture from the slowest runner alone

2026-09-26.  The owner: runner 1 is runner 8's neighbour, because they are on a circle, so proving it at one end
proves it all over.  The exact form:

* Every subject's readings are some set `S` of at most seven positive whole numbers (after the reduction to whole
  numbers, `existenceAt8_of_nat`).  A set of seven is the readings of the **slowest** runner of the arrangement
  `(1, 1 + s₁, …, 1 + s₇)` (`readingsOf_cons`), all speeds positive, nobody at rest.  A set of at most six is settled
  by native order seven (`lonely_eight_of_card_le_six`).
* So (`lonelyRunnerAt8_of_slowest`) if the slowest runner of every arrangement of eight distinct positive whole-number
  speeds is lonely, the conjecture holds at eight runners for every runner of every real arrangement.

The other end is the same statement read backwards: reversing the speeds (`v ↦ c − v`) swaps the slowest and fastest
runners and changes no difference in absolute value.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.EndRunner

open LRC.OrderEightN LRC.Order8Skeleton

/-- **The conjecture from the slowest runner.** -/
theorem lonelyRunnerAt8_of_slowest
    (h : ∀ v : Fin 8 → ℕ, Arr8 v → (∀ i, v 0 ≤ v i) → Lonely8 (readingsOf v 0)) :
    LRC.Spec.LonelyRunnerAt8 := by
  refine LRC.Spec.lonelyRunnerAt8_of_existence (existenceAt8_of_nat fun S hpos hcard => ?_)
  classical
  by_cases h6 : S.card ≤ 6
  · exact lonely_eight_of_card_le_six hpos h6
  have hS : S.card = 7 := by omega
  have harr := arr8_cons S hS hpos
  have hslow : ∀ i, (Fin.cons 1 (fun i : Fin 7 => 1 + S.orderEmbOfFin hS i) : Fin 8 → ℕ) 0 ≤
      (Fin.cons 1 (fun i : Fin 7 => 1 + S.orderEmbOfFin hS i) : Fin 8 → ℕ) i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact le_refl _
    · simp only [Fin.cons_zero, Fin.cons_succ]; omega
  have := h _ harr hslow
  rwa [readingsOf_cons S hS] at this

end LRC.EndRunner
