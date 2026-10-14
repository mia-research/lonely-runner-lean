import Mathlib

/-- A whole-number congruence certificate: lap 3 at flank 8 clears reading 3 (`3·(8·3+1) mod 64 = 11 ∈ [8, 56]`). -/
theorem probe_nat : ∃ k : ℕ, 8 ≤ 3 * (8 * k + 1) % 64 ∧ 3 * (8 * k + 1) % 64 ≤ 56 := ⟨3, by decide⟩

/-- A real-number statement with a named witness: no contradiction, the instant is written down. -/
theorem probe_real_named : ∃ t : ℝ, 0 < t ∧ t < 1 := ⟨1/2, by norm_num, by norm_num⟩

/-- The fractional part of a real is non-negative. -/
theorem probe_fract (x : ℝ) : 0 ≤ Int.fract x := Int.fract_nonneg x

/-- An existence statement over ℕ proved by contradiction. -/
theorem probe_contra : ∃ k : ℕ, 5 < k := by
  by_contra h
  push_neg at h
  exact absurd (h 6) (by norm_num)

#print axioms probe_nat
#print axioms probe_real_named
#print axioms probe_fract
#print axioms probe_contra
