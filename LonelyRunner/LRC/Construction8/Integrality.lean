import LonelyRunner.LRC.Construction8.Grid

/-!
# The converse of part 6(c)

`docs/n8/PROOF_CANDIDATE_v3.md` part 6(c); `docs/n8/PROOF_PLAN_v1.md` §2.

`Reference.lean` has the constructive direction: whole-eighth displacements with a
non-divisible index difference separate the pair.  This file has the converse, which is
where part 2(a) does its work.

The route.  Put `q k = fract (x k / n)`; taking fractional parts does not change a circle
distance, so the separation hypothesis transfers.  The positions are then in `[0,1)` and
pairwise `1/n` apart, so by `grid_of_pairwise` they are a regular `n`-gon.  The
normalisation `e₀ = 0` puts one of them at 0, and since all are nonnegative that one *is*
the sorted minimum — so the `n`-gon sits at 0 and every position is a whole number of
`1/n`s.  That forces each `x k` to be an integer, and separation then forbids congruence
mod `n`.

The normalisation is doing real work: without a position pinned at 0 the `n`-gon could sit
anywhere, and the `x k` would be integers only up to a common real shift.

Nothing here states or attempts part 7.
-/

namespace Construction8

/-- Every position is `sortedPos q` at some index — the sort is a bijection. -/
theorem exists_sorted_index {n : ℕ} (q : Fin n → ℝ) (k : Fin n) :
    ∃ j : Fin n, sortedPos q (j : ℕ) = q k := by
  refine ⟨(Tuple.sort q).symm k, ?_⟩
  rw [sortedPos_apply q ((Tuple.sort q).symm k).isLt]
  simp

/-- `sortedPos q 0` is a lower bound for every position. -/
theorem sortedPos_zero_le {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (k : Fin n) :
    sortedPos q 0 ≤ q k := by
  obtain ⟨j, hj⟩ := exists_sorted_index q k
  rw [← hj, sortedPos_apply q hn, sortedPos_apply q j.isLt]
  exact Tuple.monotone_sort q (show (⟨0, hn⟩ : Fin n) ≤ ⟨(j : ℕ), j.isLt⟩ from Nat.zero_le _)

/-- With some position at 0 and all nonnegative, the sorted minimum is 0. -/
theorem sortedPos_zero_eq {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (h0 : ∀ k, 0 ≤ q k) (k₀ : Fin n) (hk₀ : q k₀ = 0) : sortedPos q 0 = 0 := by
  have hle : sortedPos q 0 ≤ 0 := by rw [← hk₀]; exact sortedPos_zero_le hn q k₀
  have hge : 0 ≤ sortedPos q 0 := by rw [sortedPos_apply q hn]; exact h0 _
  linarith

/-- **Every position is a whole number of `1/n`s**, once the `n`-gon is pinned at 0. -/
theorem pos_eq_multiple {n : ℕ} (hn : 1 < n) (q : Fin n → ℝ)
    (h0 : ∀ k, 0 ≤ q k) (h1 : ∀ k, q k < 1)
    (hsep : ∀ a b : Fin n, a ≠ b → (n : ℝ)⁻¹ ≤ circDist (q a - q b))
    (k₀ : Fin n) (hk₀ : q k₀ = 0) (k : Fin n) :
    ∃ j : ℕ, j < n ∧ q k = (j : ℝ) * (n : ℝ)⁻¹ := by
  obtain ⟨j, hj⟩ := exists_sorted_index q k
  refine ⟨(j : ℕ), j.isLt, ?_⟩
  rw [← hj, grid_of_pairwise hn q h0 h1 hsep (j : ℕ) j.isLt,
      sortedPos_zero_eq (by omega) q h0 k₀ hk₀]
  ring

/-- If the fractional part of `x/n` is a whole number of `1/n`s, `x` is an integer. -/
theorem int_of_fract_multiple {n : ℕ} (hn : 0 < n) (x : ℝ) (j : ℕ)
    (h : Int.fract (x / n) = (j : ℝ) * (n : ℝ)⁻¹) : ∃ z : ℤ, x = (z : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  refine ⟨n * ⌊x / n⌋ + j, ?_⟩
  unfold Int.fract at h
  push_cast
  field_simp at h ⊢
  linarith

/-- Taking fractional parts does not change a circle distance. -/
theorem circDist_fract_sub {n : ℕ} (x y : ℝ) :
    circDist (Int.fract (x / n) - Int.fract (y / n)) = circDist ((x - y) / n) := by
  have h : Int.fract (x / n) - Int.fract (y / n)
      = (x - y) / n + ((⌊y / n⌋ - ⌊x / n⌋ : ℤ) : ℝ) := by
    unfold Int.fract; push_cast; ring
  rw [h, circDist_add_int]

/-- **The converse of part 6(c), integrality.**  If the `x k` are pairwise separated by
`1/n` over `n`, and the normalisation puts one of them at 0, then every `x k` is an
integer — the displacements are whole eighths. -/
theorem int_of_pairwise_sep {n : ℕ} (hn : 1 < n) (x : Fin n → ℝ)
    (k₀ : Fin n) (hk₀ : x k₀ = 0)
    (hsep : ∀ a b : Fin n, a ≠ b → (n : ℝ)⁻¹ ≤ circDist ((x a - x b) / n))
    (k : Fin n) : ∃ z : ℤ, x k = (z : ℝ) := by
  set q : Fin n → ℝ := fun k => Int.fract (x k / n) with hq
  have h0 : ∀ k, 0 ≤ q k := fun k => Int.fract_nonneg _
  have h1 : ∀ k, q k < 1 := fun k => Int.fract_lt_one _
  have hqsep : ∀ a b : Fin n, a ≠ b → (n : ℝ)⁻¹ ≤ circDist (q a - q b) := by
    intro a b hab
    simp only [hq]
    rw [circDist_fract_sub]
    exact hsep a b hab
  have hq0 : q k₀ = 0 := by simp [hq, hk₀]
  obtain ⟨j, hjn, hjeq⟩ := pos_eq_multiple hn q h0 h1 hqsep k₀ hq0 k
  exact int_of_fract_multiple (by omega) (x k) j hjeq

/-- **The converse of part 6(c), the bijection.**  A separated pair of integers is not
congruent mod `n`, so the map stays injective. -/
theorem not_dvd_of_sep {n : ℕ} (hn : 0 < n) {c : ℤ}
    (h : (n : ℝ)⁻¹ ≤ circDist ((c : ℝ) / n)) : ¬ ((n : ℤ) ∣ c) := by
  intro hdvd
  rw [circDist_int_div_of_dvd hn hdvd] at h
  have hpos : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
  linarith

end Construction8
