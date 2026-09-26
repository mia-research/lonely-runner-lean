import LonelyRunner.LRC.Cascade.Flanks

/-!
# The grand return: for whole-number readings the question lives on one half period

2026-09-27 (running log E100).  Owner: *"for integers, there is the grand return where all runners return to 0 at the
same time essentially, which means the pattern would repeat from there."*

For whole-number readings every runner is back at the start at every whole instant, so the pattern repeats with period
`1` (`lonely_add_int`), and it is mirror-symmetric inside the period (`lonely_mirror`: lonely at `s` exactly when lonely
at `1 − s`, from `circDist` being even).  Hence the subject is lonely at some positive instant exactly when it is lonely
at some instant of the first half period `(0, 1/2]` (`exists_lonely_iff_half`).  With the bound `1/(8·d_min)` the cascade's
question is a finite window `[1/(8·d_min), 1/2]`, ending at the half lap, the mirror's fixed point.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.GrandReturn

open Flanks ConstructionN MomentIterationN

/-- **The grand return.**  Whole-number readings: the pattern repeats after every whole instant. -/
theorem lonely_add_int {n : ℕ} {ds : Finset ℝ} (hint : ∀ d ∈ ds, ∃ a : ℤ, d = (a : ℝ)) (s : ℝ) (k : ℤ) :
    Lonely n ds (s + k) ↔ Lonely n ds s := by
  constructor <;> intro h d hd <;> have := h d hd <;> obtain ⟨a, rfl⟩ := hint d hd
  · rwa [show (a : ℝ) * (s + k) = (a : ℝ) * s + ((a * k : ℤ) : ℝ) by push_cast; ring, circDist_add_int] at this
  · rwa [show (a : ℝ) * (s + k) = (a : ℝ) * s + ((a * k : ℤ) : ℝ) by push_cast; ring, circDist_add_int]

/-- **The mirror.**  Whole-number readings: lonely at `1 − s` exactly when lonely at `s`. -/
theorem lonely_mirror {n : ℕ} [Fact (2 ≤ n)] {ds : Finset ℝ} (hint : ∀ d ∈ ds, ∃ a : ℤ, d = (a : ℝ)) (s : ℝ) :
    Lonely n ds (1 - s) ↔ Lonely n ds s := by
  have e : (1 - s) = -s + ((1 : ℤ) : ℝ) := by push_cast; ring
  rw [e, lonely_add_int hint, lonely_neg]

/-- **One half period suffices.**  Whole-number readings, at least one of them: the subject is lonely at some positive
instant exactly when it is lonely at some instant in `(0, 1/2]`. -/
theorem exists_lonely_iff_half {n : ℕ} [Fact (2 ≤ n)] {ds : Finset ℝ} (hne : ds.Nonempty)
    (hint : ∀ d ∈ ds, ∃ a : ℤ, d = (a : ℝ)) :
    (∃ s, 0 < s ∧ Lonely n ds s) ↔ ∃ s, 0 < s ∧ s ≤ 1 / 2 ∧ Lonely n ds s := by
  constructor
  · rintro ⟨s, -, hs⟩
    have hf := (lonely_add_int hint (Int.fract s) ⌊s⌋).mp (by rwa [Int.fract_add_floor])
    have hpos : 0 < Int.fract s := by
      rcases (Int.fract_nonneg s).lt_or_eq with h | h
      · exact h
      · exfalso
        obtain ⟨d, hd⟩ := hne
        have := hf d hd
        rw [← h, mul_zero] at this
        have h0 : circDist 0 = 0 := by unfold circDist; simp
        have : (0 : ℝ) < (n : ℝ)⁻¹ := by
          have : (2 : ℝ) ≤ n := by exact_mod_cast (Fact.out : 2 ≤ n)
          positivity
        linarith [h0 ▸ ‹(n : ℝ)⁻¹ ≤ circDist 0›]
    by_cases hh : Int.fract s ≤ 1 / 2
    · exact ⟨Int.fract s, hpos, hh, hf⟩
    · refine ⟨1 - Int.fract s, by linarith [Int.fract_lt_one s], by linarith, ?_⟩
      exact (lonely_mirror hint _).mpr hf
  · rintro ⟨s, hs, -, h⟩; exact ⟨s, hs, h⟩

end LRC.GrandReturn
