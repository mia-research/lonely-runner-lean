import LonelyRunner.LRC.Cascade.Certificate

/-!
# The near-AP extremal family, and its lonely instant

Part of the cascade artefact (`LRC/Cascade/`).  Threshold `1/8`.

An exhaustive search over every seven-element set of integer differences with `d_max ≤ 30`
(2,035,800 sets) found exactly one *critical* configuration — one whose subject has a single free
flank: `{2, 3, 4, 5, 6, 7, 16}`.  It is not isolated.  It is the first member of

    Δ_m = {2, 3, 4, 5, 6, 7, 16m},   m ≥ 1,

and `{2,3,4,5,6,7,N}` is critical exactly when `16 ∣ N`.  This file proves the whole family lonely,
at the explicit instant

    t_m = (8m + 1) / (128m).

The mechanism, and why the family is extremal: the consecutive block sits at
`d · t_m = d/16 + d/(128m)`, which lies in `[1/8, 1/2]` for `2 ≤ d ≤ 7` and `m ≥ 1`, while the
outlier sits at `16m · t_m = m + 1/8` exactly.  So the minimum distance over the whole set is
**exactly `1/8`, attained by the outlier** — the order-8 bound is tight on this family, and
loneliness holds because the threshold is attained rather than exceeded (`Lonely` asks for
`1/n ≤ circDist`).  The block's own margin, `d/(128m)` at `d = 2`, tends to 0 as `m → ∞`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace NearAP

open ConstructionN MomentIterationN

/-- On `[0, 1/2]` the circle distance is the point itself. -/
theorem circDist_of_le_half {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : circDist x = x := by
  have hlt : x < 1 := by linarith
  unfold circDist
  rw [Int.fract_eq_self.mpr ⟨h0, hlt⟩]
  exact min_eq_left (by linarith)

/-- Every member of the consecutive block `2 ≤ d ≤ 7` is clear at `t_m`: it sits at
`d/16 + d/(128m)`, inside `[1/8, 1/2]`. -/
theorem block_clear {m : ℕ} (hm : 0 < m) {d : ℝ} (h2 : 2 ≤ d) (h7 : d ≤ 7) :
    ((8 : ℕ) : ℝ)⁻¹ ≤ circDist (d * ((8 * (m : ℝ) + 1) / (128 * (m : ℝ)))) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < 128 * (m : ℝ) := by linarith
  have key : d * ((8 * (m : ℝ) + 1) / (128 * (m : ℝ))) = (d * (8 * (m : ℝ) + 1)) / (128 * (m : ℝ)) := by
    ring
  have hlo : (1 : ℝ) / 8 ≤ (d * (8 * (m : ℝ) + 1)) / (128 * (m : ℝ)) := by
    rw [le_div_iff₀ hmpos]; nlinarith
  have hhi : (d * (8 * (m : ℝ) + 1)) / (128 * (m : ℝ)) ≤ 1 / 2 := by
    rw [div_le_iff₀ hmpos]; nlinarith
  rw [key, circDist_of_le_half (by linarith) hhi]
  simpa using hlo

/-- The outlier sits exactly on the threshold: `16m · t_m = m + 1/8`. -/
theorem outlier_clear {m : ℕ} (hm : 0 < m) :
    ((8 : ℕ) : ℝ)⁻¹ ≤ circDist ((16 * (m : ℝ)) * ((8 * (m : ℝ) + 1) / (128 * (m : ℝ)))) := by
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have e : (16 * (m : ℝ)) * ((8 * (m : ℝ) + 1) / (128 * (m : ℝ))) = 1 / 8 + ((m : ℤ) : ℝ) := by
    field_simp; push_cast; ring
  rw [e, circDist_add_int]
  rw [circDist_of_le_half (by norm_num) (by norm_num)]
  norm_num

/-- **The near-AP extremal family is lonely.**  For every `m ≥ 1` the difference set
`{2, 3, 4, 5, 6, 7, 16m}` is lonely at `t_m = (8m + 1)/(128m)`.  The minimum distance is exactly
`1/8`, attained by the outlier. -/
theorem near_ap_lonely (m : ℕ) (hm : 0 < m) :
    Lonely 8 ({2, 3, 4, 5, 6, 7, 16 * (m : ℝ)} : Finset ℝ)
      ((8 * (m : ℝ) + 1) / (128 * (m : ℝ))) := by
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with h | h | h | h | h | h | h <;> rw [h]
  · exact block_clear hm (by norm_num) (by norm_num)
  · exact block_clear hm (by norm_num) (by norm_num)
  · exact block_clear hm (by norm_num) (by norm_num)
  · exact block_clear hm (by norm_num) (by norm_num)
  · exact block_clear hm (by norm_num) (by norm_num)
  · exact block_clear hm (by norm_num) (by norm_num)
  · exact outlier_clear hm

end NearAP
