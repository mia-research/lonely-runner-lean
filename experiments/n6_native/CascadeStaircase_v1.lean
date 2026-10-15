import LonelyRunner.LRC.Cascade.Flanks

/-!
# The staircase and the early-ending criterion (observations formalised)

Observed on 17,135 order-six residual sets (`six_walk_end_v1.out`): every walk whose moves all land at
opening index 1 has strictly decreasing setters (8,240 of 8,240), and a walk ending at opening `k` of a
flank `x` ends within the first third of the slowest element's lap exactly when `v₁(6k+1) < 2x`.

* `staircase`: if the walk moves from opening `k` of `x` to opening `k` of `x'` (time strictly increases,
  `MomentIterationN.lt_nextOpening`), then `x' < x`.
* `early_iff`: `v₁ · (k + 1/6)/x < 1/3 ↔ v₁(6k+1) < 2x`.
-/

namespace CascadeStaircase

theorem staircase {n : ℕ} {x x' : ℝ} (hx : 0 < x) (hx' : 0 < x') (k : ℕ) (hn : 0 < n)
    (h : Flanks.flankOpening n x k < Flanks.flankOpening n x' k) : x' < x := by
  unfold Flanks.flankOpening at h
  have hc : (0 : ℝ) < (k : ℝ) + (n : ℝ)⁻¹ := by positivity
  rw [div_lt_div_iff_of_pos_left hc hx hx'] at h
  exact h

theorem early_iff {v1 x : ℝ} (hx : 0 < x) (k : ℕ) :
    v1 * Flanks.flankOpening 6 x k < 1 / 3 ↔ v1 * (6 * k + 1) < 2 * x := by
  unfold Flanks.flankOpening
  rw [show v1 * (((k : ℝ) + ((6 : ℕ) : ℝ)⁻¹) / x) = v1 * (6 * k + 1) / (6 * x) by
    push_cast; field_simp]
  rw [div_lt_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

end CascadeStaircase

#print axioms CascadeStaircase.staircase
#print axioms CascadeStaircase.early_iff
