import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # No finite set of test points can give a necessary condition

Two attempts at a smaller necessary condition for band 2 both failed the same way:

* the candidates `R_k = (8k+1)/S` — a single `v ≈ 0.981` killed all ~14 of them;
* the 14 **integer** points of `[1,7] ∪ [9,15]` — a single `s ≈ 7.9333` killed all 14.

That is not bad luck. **One reading just below `8` blocks every point of any finite set.**

If `s = 8 − η` then `R·s = 8R − ηR`, and `8R` is a multiple of `8`, so `s` is within `1` of a
multiple of `8` at `R` exactly when `ηR < 1`. Choosing `η < 1/max(P)` blocks all of `P` at once.

> **Consequence.** Band-2 unreachability cannot be reduced to "some point of a fixed finite set is
> clear". Any such condition is satisfiable by a single reading, so it is vacuous. The covering must
> be tested on **intervals**, which is what the chain/LP formulation of `ANALYTIC_LAST_STEP_v1` does.

This is a negative result about method, and it forecloses a class of attacks rather than a single
attempt. -/

namespace NoFinitePoints

/-- **A reading just below `8` blocks at `R`.**  With `s = 8 − η` and `0 < ηR < 1`, the reading at
`R` is within `1` of the multiple `8R`, so the runner is in the way. -/
theorem near_eight_blocks {η R : ℝ} (hη : 0 < η) (hR : 0 < R) (h : η * R < 1) :
    |(8 - η) * R - 8 * R| < 1 := by
  have : (8 - η) * R - 8 * R = -(η * R) := by ring
  rw [this, abs_neg, abs_of_pos (mul_pos hη hR)]
  exact h

/-- **Hence one reading blocks an entire finite set.**  For any bound `B` on the points and any
`0 < η < 1/B`, the single reading `8 − η` is in the way at every `R ∈ (0, B]`. -/
theorem one_reading_blocks_all {η B : ℝ} (hη : 0 < η) (hB : 0 < B) (hηB : η < 1 / B)
    {R : ℝ} (hR0 : 0 < R) (hRB : R ≤ B) :
    |(8 - η) * R - 8 * R| < 1 := by
  refine near_eight_blocks hη hR0 ?_
  have h1 : η * B < 1 := by
    rw [lt_div_iff₀ hB] at hηB; linarith
  nlinarith

end NoFinitePoints
