import LonelyRunner.LRC.Cascade.ScaleCandidates

/-! # The algebraic bridge

`D = e/(8k+1)` lies in disparity `d`'s bad interval at lap `M` exactly when `d/e` is within
`1/(8k+1)` of `8M/(8k+1)`.  Reuses `Flanks.candidateScale`; no measure, only field arithmetic.

**What it does and does not say.**  The demanded approximation quality is `1/q` with `q = 8k+1`,
which every real satisfies for free — the nearest integer to `q·(d/e)` is always within `1/2`.  The
content is entirely that the numerator must be a multiple of `8`.  So this is a **congruence**
condition wearing the clothes of a Diophantine one, and continued-fraction machinery has nothing
to bite on here. -/

namespace Bridge
open Flanks
variable {n : ℕ} [Fact (2 ≤ n)]

theorem inBad_iff_abs_sub_lt {d e : ℝ} (he : 0 < e) (k M : ℕ) (hM : 1 ≤ M) :
    (d / (8 * (M : ℝ) + 1) < candidateScale 8 e k ∧
     candidateScale 8 e k < d / (8 * (M : ℝ) - 1)) ↔
    |d / e - (8 * (M : ℝ)) / (8 * (k : ℝ) + 1)| < 1 / (8 * (k : ℝ) + 1) := by
  have hK : (0 : ℝ) < 8 * (k : ℝ) + 1 := by positivity
  have hM1 : (0 : ℝ) < 8 * (M : ℝ) + 1 := by positivity
  have hMr : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM2 : (0 : ℝ) < 8 * (M : ℝ) - 1 := by linarith
  have e1 : (8 * (M : ℝ) - 1) / (8 * (k : ℝ) + 1)
      = 8 * (M : ℝ) / (8 * (k : ℝ) + 1) - 1 / (8 * (k : ℝ) + 1) := by
    field_simp
  have e2 : (8 * (M : ℝ) + 1) / (8 * (k : ℝ) + 1)
      = 8 * (M : ℝ) / (8 * (k : ℝ) + 1) + 1 / (8 * (k : ℝ) + 1) := by
    field_simp
  have key : |d / e - (8 * (M : ℝ)) / (8 * (k : ℝ) + 1)| < 1 / (8 * (k : ℝ) + 1) ↔
      ((8 * (M : ℝ) - 1) / (8 * (k : ℝ) + 1) < d / e ∧
        d / e < (8 * (M : ℝ) + 1) / (8 * (k : ℝ) + 1)) := by
    rw [abs_lt, e1, e2]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
  rw [key]
  unfold candidateScale
  push_cast
  rw [div_lt_div_iff₀ hM1 hK, div_lt_div_iff₀ hK hM2,
      div_lt_div_iff₀ hK he, div_lt_div_iff₀ he hK]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by nlinarith, by nlinarith⟩

end Bridge
