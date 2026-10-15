import LonelyRunner.LRC.Cascade.Flanks

/-!
# BHK §8 in the walk, v2: one opening-1 rule, three instances

Supersedes `CascadeSecEight_v1.lean` (kept). Observed exactly (`six_s8_step_rule_v1.out`,
`six_s8_exceptions_v1.out`):
* `opening_one_blocks_iff`: for `0 < a < b < 7a`, `a` is in the way at opening 1 of `b`
  (time `7/(6b)`) exactly when `5b < 7a`.
* instances: `v₄` at `v₅`'s opening 1 (the walk steps on to `v₄`); runner 3 (or 2) at `v₄`'s opening 1
  (the §8 exceptions: 86 of 88 in `[1,60]` arise there after `(1,0) → (5,1) → (4,1)`).
* `s8_slow_clear_at_v5`: as in v1.
-/

namespace CascadeSecEight

open ConstructionN

theorem s8_slow_clear_at_v5 {v1 v5 d : ℝ} (hv1 : 0 < v1) (h5lo : 5 * v1 < v5) (h5hi : v5 < 7 * v1)
    (hd1 : v1 ≤ d) (hd3 : d ≤ 3 * v1) :
    ((6 : ℕ) : ℝ)⁻¹ ≤ circDist (d * Flanks.flankOpening 6 v5 1) := by
  haveI : Fact (2 ≤ 6) := ⟨by norm_num⟩
  have hv5 : 0 < v5 := by linarith
  refine Flanks.clear_at_first_opening_of_ratio (n := 6) hv5 ?_ ?_ <;> push_cast <;> nlinarith

/-- **Opening 1 of `b`.** For `0 < a < b < 7a`, `a` is in the way at `7/(6b)` iff `5b < 7a`. -/
theorem opening_one_blocks_iff {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb7 : b < 7 * a) :
    circDist (a * Flanks.flankOpening 6 b 1) < ((6 : ℕ) : ℝ)⁻¹ ↔ 5 * b < 7 * a := by
  have hb : 0 < b := by linarith
  have hy : a * Flanks.flankOpening 6 b 1 = 7 * a / (6 * b) := by
    unfold Flanks.flankOpening; push_cast; field_simp; ring
  rw [hy]
  have hlo : (6 : ℝ)⁻¹ < 7 * a / (6 * b) := by rw [lt_div_iff₀ (by positivity)]; nlinarith
  have hhi : 7 * a / (6 * b) < 7 / 6 := by rw [div_lt_iff₀ (by positivity)]; nlinarith
  push_cast
  constructor
  · intro h
    by_contra hc; push Not at hc
    have h56 : 7 * a / (6 * b) ≤ 5 / 6 := by rw [div_le_iff₀ (by positivity)]; nlinarith
    haveI : Fact (2 ≤ 6) := ⟨by norm_num⟩
    have := Flanks.circDist_ge_of_band (n := 6) (y := 7 * a / (6 * b)) 0 (by push_cast; linarith)
      (by push_cast; linarith)
    simp only [Int.cast_zero, add_zero] at this
    push_cast at this; linarith
  · intro h
    have h56 : 5 / 6 < 7 * a / (6 * b) := by rw [lt_div_iff₀ (by positivity)]; nlinarith
    have := circDist_le_abs_sub_int (7 * a / (6 * b)) 1
    push_cast at this
    have hab' : |7 * a / (6 * b) - 1| < 6⁻¹ := by rw [abs_lt]; constructor <;> linarith
    linarith

/-- The walk steps on from `v₅`'s opening 1 to `v₄` iff `7v₄ > 5v₅` (`v₁ < v₄ < v₅ < 7v₁`). -/
theorem s8_v4_steps_on {v1 v4 v5 : ℝ} (hv1 : 0 < v1) (h14 : v1 < v4) (h45 : v4 < v5) (h5 : v5 < 7 * v1) :
    circDist (v4 * Flanks.flankOpening 6 v5 1) < ((6 : ℕ) : ℝ)⁻¹ ↔ 5 * v5 < 7 * v4 :=
  opening_one_blocks_iff (by linarith) h45 (by linarith)

/-- The §8 exceptions: runner `j` (2 or 3, `v₁ ≤ v_j < v₄ < 7v₁`) is in the way at `v₄`'s opening 1
iff `5v₄ < 7v_j`. -/
theorem s8_slow_blocks_at_v4 {v1 vj v4 : ℝ} (hv1 : 0 < v1) (h1j : v1 ≤ vj) (hj4 : vj < v4) (h4 : v4 < 7 * v1) :
    circDist (vj * Flanks.flankOpening 6 v4 1) < ((6 : ℕ) : ℝ)⁻¹ ↔ 5 * v4 < 7 * vj :=
  opening_one_blocks_iff (by linarith) hj4 (by linarith)

end CascadeSecEight

#print axioms CascadeSecEight.opening_one_blocks_iff
#print axioms CascadeSecEight.s8_v4_steps_on
#print axioms CascadeSecEight.s8_slow_blocks_at_v4
#print axioms CascadeSecEight.s8_slow_clear_at_v5
