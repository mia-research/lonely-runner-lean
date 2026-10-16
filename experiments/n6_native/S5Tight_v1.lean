import LonelyRunner.LRC.Spec.OrderSixSixRestN

/-!
# §5, k = 1: the two tight points (n6_native, E110)

Near `(1, 3, 4, 5, 9)` and near `(1, 2, 3, 4, 5)` (both with `v₃ = v₁ + v₂`) the arrangement is lonely at one of the two
tight instants `t = 1/(6v₁)`, `t = 5/(6v₁)`: which one is decided by the edge relation (`v₄` against `5v₁`, resp. `v₅`
against `5v₁`). The bands are closed, so the exact-edge case is covered by the first instant (with equality).
-/

namespace LRC.S6Native
open LRC.S7Native LRC.S8Native

/-- A runner at the instant `c/(6v₁)` reads `c v/(6v₁)`; in the band of lap `p` when `(6p+1)v₁ ≤ cv ≤ (6p+5)v₁`. -/
theorem inst_band {v v1 c : ℝ} (h1 : 0 < v1) (p : ℤ) (ha : (6 * (p : ℝ) + 1) * v1 ≤ c * v)
    (hb : c * v ≤ (6 * (p : ℝ) + 5) * v1) : (6 : ℝ)⁻¹ ≤ circDist (v * (c / (6 * v1))) := by
  have e : v * (c / (6 * v1)) = c * v / (6 * v1) := by ring
  rw [e]
  apply clear_of_band (p := p)
  · rw [le_div_iff₀ (by positivity)]; linarith
  · rw [div_le_iff₀ (by positivity)]; linarith

/-- **Near `(1, 3, 4, 5, 9)`.** `v₃ = v₁ + v₂`, `v₂/v₁ ∈ [14/5, 17/5]`, `v₃ ≤ v₄ ≤ 29v₁/5`, `v₅/v₁ ∈ [43/5, 47/5]`:
lonely at `1/(6v₁)` (laps `(0,0,0,0,1)`) if `v₄ ≤ 5v₁`, else at `5/(6v₁)` (laps `(0,2,3,4,7)`). -/
theorem tight_13459 {v1 v2 v3 v4 v5 : ℝ} (h1 : 0 < v1) (hv3 : v3 = v1 + v2) (h2a : 14 * v1 ≤ 5 * v2)
    (h2b : 5 * v2 ≤ 17 * v1) (h34 : v3 ≤ v4) (h4 : 5 * v4 ≤ 29 * v1) (h5a : 43 * v1 ≤ 5 * v5)
    (h5b : 5 * v5 ≤ 47 * v1) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  rcases le_total v4 (5 * v1) with h | h
  · refine ⟨1 / (6 * v1), ?_, ?_, ?_, ?_, ?_⟩ <;> [apply inst_band h1 0; apply inst_band h1 0; apply inst_band h1 0;
      apply inst_band h1 0; apply inst_band h1 1] <;> push_cast <;> nlinarith
  · refine ⟨5 / (6 * v1), ?_, ?_, ?_, ?_, ?_⟩ <;> [apply inst_band h1 0; apply inst_band h1 2; apply inst_band h1 3;
      apply inst_band h1 4; apply inst_band h1 7] <;> push_cast <;> nlinarith

/-- **Near `(1, 2, 3, 4, 5)`.** `v₃ = v₁ + v₂`, `v₂/v₁ ∈ [2, 11/5]`, `v₄/v₁ ∈ [19/5, 23/5]`, `v₄ ≤ v₅ ≤ 29v₁/5`: lonely at
`1/(6v₁)` (all on lap 0) if `v₅ ≤ 5v₁`, else at `5/(6v₁)` (laps `(0,1,2,3,4)`). -/
theorem tight_12345 {v1 v2 v3 v4 v5 : ℝ} (h1 : 0 < v1) (hv3 : v3 = v1 + v2) (h2a : 2 * v1 ≤ v2)
    (h2b : 5 * v2 ≤ 11 * v1) (h4a : 19 * v1 ≤ 5 * v4) (h4b : 5 * v4 ≤ 23 * v1) (h45 : v4 ≤ v5)
    (h5 : 5 * v5 ≤ 29 * v1) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  rcases le_total v5 (5 * v1) with h | h
  · refine ⟨1 / (6 * v1), ?_, ?_, ?_, ?_, ?_⟩ <;> [apply inst_band h1 0; apply inst_band h1 0; apply inst_band h1 0;
      apply inst_band h1 0; apply inst_band h1 0] <;> push_cast <;> nlinarith
  · refine ⟨5 / (6 * v1), ?_, ?_, ?_, ?_, ?_⟩ <;> [apply inst_band h1 0; apply inst_band h1 1; apply inst_band h1 2;
      apply inst_band h1 3; apply inst_band h1 4] <;> push_cast <;> nlinarith

end LRC.S6Native

#print axioms LRC.S6Native.tight_13459
#print axioms LRC.S6Native.tight_12345
