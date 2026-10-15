import LonelyRunner.LRC.Spec.OrderSixN

/-! Cross-check of `six_residual_v1.py` against the Lean predicate `LRC.OrderSixN.SixResidual`.
Three sets the script calls residual are proved residual; for each of the six non-cardinality
fields, one set the script says fails exactly that field is proved not residual through it. -/

open LRC.OrderSixN

macro "res" : term => `(⟨by decide, by decide, by decide, by decide, by decide, by unfold FreeFlank; decide, by decide⟩)

example : SixResidual {1, 2, 3, 5, 12} := res
example : SixResidual {1, 2, 3, 5, 24} := res
example : SixResidual {1, 2, 3, 6, 20} := res

example : ¬ SixResidual {1, 2, 3, 5, 6} := fun h => absurd h.four (by decide)
example : ¬ SixResidual {1, 2, 3, 6, 16} := fun h => absurd h.five (by decide)
example : ¬ SixResidual {2, 3, 5, 6, 8} := fun h => absurd h.spread (by decide)
example : ¬ SixResidual {1, 2, 3, 4, 10} := fun h => absurd h.shape (by decide)
example : ¬ SixResidual {1, 2, 3, 8, 30} := fun h =>
  h.no_free_flank 30 (by decide) (by decide) (by unfold FreeFlank; decide)
example : ¬ SixResidual {1, 2, 3, 5, 36} := fun h => absurd h.not_fast (by decide)
