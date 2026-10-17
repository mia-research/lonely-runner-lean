import LonelyRunner.LRC.Spec.OrderSevenFoldN
import LonelyRunner.LRC.Spec.OrderSevenBox6Tree50N

/-!
# Order seven for bounded spread: `v6 ≤ 50 v1`

As `OrderSevenSpreadN` with the larger kernel-checked six-runner tree (`O7Box6T50`, 190,117 leaves): if `v6 ≥ 6 v5` the
fastest-runner fold closes; otherwise the ratios lie in the tree's root box.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.O7Spread

theorem lonely7_spread50 {v1 v2 v3 v4 v5 v6 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4)
    (h45 : v4 < v5) (h56 : v5 < v6) (hs : v6 ≤ 50 * v1) :
    ∃ t : ℝ, ∀ d ∈ ({v1, v2, v3, v4, v5, v6} : Finset ℕ), (1 : ℝ) / 7 ≤ circDist ((d : ℝ) * t) := by
  rcases le_or_gt (6 * v5) v6 with h6 | h6
  · exact LRC.O7Fold.lonely7_of_fast6 h0 h12 h23 h34 h45 h6
  · refine LRC.O7Box6T50.lonely h0 h12 h23 h34 h45 h56 ?_ ?_
    · have : (v6 : ℝ) ≤ 50 * v1 := by exact_mod_cast hs
      push_cast; linarith
    · have : (v6 : ℝ) < 6 * v5 := by exact_mod_cast h6
      push_cast; linarith

end LRC.O7Spread
