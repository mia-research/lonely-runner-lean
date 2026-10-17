import LonelyRunner.LRC.Spec.OrderSevenFoldN
import LonelyRunner.LRC.Spec.OrderSevenKappaTree100N

/-!
# Order seven: the fastest-runner fold on `v5 ≤ 100 v1`

`kappa ≥ 3/28` on `v1 ≥ v5/100` (kernel-checked tree, `O7KTree100.kappa`) and the fold give: six whole numbers
`0 < v1 < … < v6` with `v5 ≤ 100 v1` and `8 v5 ≤ 3 v6` are lonely at `1/7`.  With `lonely7_of_fast6`, the fold
closes order seven for `v6 ≥ 6 v5` everywhere and for `v6 ≥ (8/3) v5` when `v5 ≤ 100 v1`.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.O7Fold

theorem lonely7_fold100 {v1 v2 v3 v4 v5 v6 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4)
    (h45 : v4 < v5) (h100 : v5 ≤ 100 * v1) (h6 : 8 * v5 ≤ 3 * v6) :
    ∃ t : ℝ, ∀ d ∈ ({v1, v2, v3, v4, v5, v6} : Finset ℕ), (1 : ℝ) / 7 ≤ circDist ((d : ℝ) * t) := by
  refine lonely7_of_kappa (by omega) h6 (LRC.O7KTree100.kappa h0 h12 h23 h34 h45 ?_)
  have : (v5 : ℝ) ≤ 100 * v1 := by exact_mod_cast h100
  push_cast; linarith

end LRC.O7Fold
