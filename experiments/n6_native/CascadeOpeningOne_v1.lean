import LonelyRunner.LRC.Cascade.Flanks

/-!
# In the way at opening 1, for any lap (observations formalised)

`opening_one_inWay_iff`: for `x, z > 0`, `x` is in the way at opening 1 of `z` (time `7/(6z)`) iff
`|7x − 6Nz| < z` for some integer `N`. Instances observed exactly in the walk:
* `N = 1`: the staircase steps (`CascadeSecEight_v2.opening_one_blocks_iff`, `5z < 7x < 7z`);
* `N = 2`: delayed returns `x@1 → y@1 → z@1 → x@2` (`six_delayed_return_v1.out`, 342 of 342 satisfy
  `11z < 7x < 13z`).
The framework's `TerminationFour.return_lemma` covers immediate returns only; this is the opening-1
reading behind the delayed ones.
-/

namespace CascadeOpeningOne

open ConstructionN

theorem opening_one_inWay_iff {x z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    circDist (x * Flanks.flankOpening 6 z 1) < ((6 : ℕ) : ℝ)⁻¹ ↔ ∃ N : ℤ, |7 * x - 6 * N * z| < z := by
  have hy : x * Flanks.flankOpening 6 z 1 = 7 * x / (6 * z) := by
    unfold Flanks.flankOpening; push_cast; field_simp; ring
  rw [hy]
  have h6z : (0 : ℝ) < 6 * z := by positivity
  have key : ∀ N : ℤ, |7 * x / (6 * z) - N| < 6⁻¹ ↔ |7 * x - 6 * N * z| < z := by
    intro N
    have e : 7 * x - 6 * N * z = (6 * z) * (7 * x / (6 * z) - N) := by field_simp
    rw [e, abs_mul, abs_of_pos h6z]
    constructor
    · intro h; nlinarith [abs_nonneg (7 * x / (6 * z) - N)]
    · intro h; nlinarith [abs_nonneg (7 * x / (6 * z) - N)]
  push_cast
  constructor
  · intro h
    obtain ⟨N, hN⟩ := circDist_eq_abs_sub_some_int (7 * x / (6 * z))
    exact ⟨N, (key N).mp (by rw [← hN]; exact h)⟩
  · rintro ⟨N, hN⟩
    exact lt_of_le_of_lt (circDist_le_abs_sub_int _ N) ((key N).mpr hN)

end CascadeOpeningOne

#print axioms CascadeOpeningOne.opening_one_inWay_iff
