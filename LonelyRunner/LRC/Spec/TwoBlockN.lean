import LonelyRunner.LRC.Spec.TwoPinnerN

/-!
# The two-block rule: the AP at one scale, read on two laps of the grid

2026-09-27.  Running record: `RUNNING_LOG_order8_v1.md` E119.

In log coordinates the clear places of the grid are `F = [0, log 7] ∪ [log 9, log 15] ∪ [log 17, log 23] ∪ …` (the
logarithm of `[1, 7] + 8ℤ`), and changing the instant shifts the readings rigidly (the AP's scale invariance).  At the
instant `9/(8e)` (the scale `e/9`) a reading `d` sits at `9d/e`:

* **`lonely_eight_of_two_block`.**  If every reading lies in the lower block `[e/9, 7e/9]` (position `[1, 7]`) or the
  upper block `[e, 15e/9]` (position `[9, 15]`), the subject is lonely at `9/(8e)`.  R1 on two laps at once; first-lap
  clearance at `k = 1` is the case with nothing in the upper block.  `e` need not be a reading.
* **`exists_big_gap`.**  Seven increasing positive readings spanning more than a factor `7` have two consecutive ones in
  ratio at least `9/7` (`(9/7)⁶ < 7`).
* **`b1_remainder`.**  In the band `7·d₁ < d₇ < 9·d₁` (the fastest runner lapped once into the subject's slot at the AP
  scale): if no reading carries a two-block instant, the top four readings are dense, every consecutive ratio below
  `9/7`.  So the fast block above the highest large gap has at least four readings.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.TwoBlock

/-- **The two-block rule.** -/
theorem lonely_eight_of_two_block {S : Finset ℕ} {e : ℕ} (he : 0 < e)
    (h : ∀ d ∈ S, (e ≤ 9 * d ∧ 9 * d ≤ 7 * e) ∨ (e ≤ d ∧ 9 * d ≤ 15 * e)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  refine ⟨9 / (8 * e), by positivity, fun d hd => ?_⟩
  have hx : (d : ℝ) * (9 / (8 * e)) = 9 * d / (8 * e) := by ring
  rw [hx]
  rcases h d hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have a1 : (e : ℝ) ≤ 9 * d := by exact_mod_cast h1
    have a2 : 9 * (d : ℝ) ≤ 7 * e := by exact_mod_cast h2
    refine LRC.TwoPinner.clear_of_band (N := 0) ?_ ?_
    · rw [le_div_iff₀ (by positivity)]; push_cast; linarith
    · rw [div_le_iff₀ (by positivity)]; push_cast; linarith
  · have a1 : (e : ℝ) ≤ d := by exact_mod_cast h1
    have a2 : 9 * (d : ℝ) ≤ 15 * e := by exact_mod_cast h2
    refine LRC.TwoPinner.clear_of_band (N := 1) ?_ ?_
    · rw [le_div_iff₀ (by positivity)]; push_cast; linarith
    · rw [div_le_iff₀ (by positivity)]; push_cast; linarith

/-- **A large gap always exists** once seven readings span more than a factor `7` (no ordering needed beyond
`a0 < a1`). -/
theorem exists_big_gap {a0 a1 a2 a3 a4 a5 a6 : ℝ} (h01 : a0 < a1) (hspan : 7 * a0 < a6) :
    9 * a0 ≤ 7 * a1 ∨ 9 * a1 ≤ 7 * a2 ∨ 9 * a2 ≤ 7 * a3 ∨ 9 * a3 ≤ 7 * a4 ∨ 9 * a4 ≤ 7 * a5 ∨
      9 * a5 ≤ 7 * a6 := by
  by_contra hc
  push Not at hc
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hc
  -- `7⁶·a6 < 9⁶·a0 < 7⁷·a0`
  nlinarith

/-- **What is left of the band `7·d₁ < d₇ < 9·d₁` after the two-block rule.**  If no reading carries a two-block
instant, the top four readings are dense: `d₅/d₄, d₆/d₅, d₇/d₆` are all below `9/7`. -/
theorem b1_remainder {a0 a1 a2 a3 a4 a5 a6 : ℕ} (h0 : 0 < a0) (h01 : a0 < a1) (h12 : a1 < a2) (h23 : a2 < a3)
    (h34 : a3 < a4) (h45 : a4 < a5) (h56 : a5 < a6) (hlo : 7 * a0 < a6) (hhi : a6 < 9 * a0)
    (hno : ∀ e ∈ ({a0, a1, a2, a3, a4, a5, a6} : Finset ℕ),
      ¬ ∀ d ∈ ({a0, a1, a2, a3, a4, a5, a6} : Finset ℕ),
        (e ≤ 9 * d ∧ 9 * d ≤ 7 * e) ∨ (e ≤ d ∧ 9 * d ≤ 15 * e)) :
    7 * a4 < 9 * a3 ∧ 7 * a5 < 9 * a4 ∧ 7 * a6 < 9 * a5 := by
  have g6 : 7 * a6 < 9 * a5 := by
    by_contra hg; push Not at hg
    apply hno a6 (by simp)
    intro d hd; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have g5 : 7 * a5 < 9 * a4 := by
    by_contra hg; push Not at hg
    apply hno a5 (by simp)
    intro d hd; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have g4 : 7 * a4 < 9 * a3 := by
    by_contra hg; push Not at hg
    apply hno a4 (by simp)
    intro d hd; simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  exact ⟨g4, g5, g6⟩

/-- **The block rule at every lap.**  At the scale `e/(8K+1)` (the instant `(8K+1)/(8e)`, the flank `e` at its `K`-th
opening) the grid's clear places are the blocks `[8k+1, 8k+7]`, one per lap `k`.  If every reading's position
`(8K+1)·d/e` lies in some block, the subject is lonely there.  `e` need not be a reading.  The two-block rule is
`K = 1` with blocks `k = 0, 1`; the cascade's landings in the band's remainder are `K = 2` with blocks `0, 1, 2`. -/
theorem lonely_eight_of_blocks {S : Finset ℕ} {e K : ℕ} (he : 0 < e)
    (h : ∀ d ∈ S, ∃ k : ℕ, (8 * k + 1) * e ≤ (8 * K + 1) * d ∧ (8 * K + 1) * d ≤ (8 * k + 7) * e) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  refine ⟨(8 * K + 1) / (8 * e), by positivity, fun d hd => ?_⟩
  obtain ⟨k, h1, h2⟩ := h d hd
  have a1 : (8 * (k : ℝ) + 1) * e ≤ (8 * K + 1) * d := by exact_mod_cast h1
  have a2 : (8 * (K : ℝ) + 1) * d ≤ (8 * k + 7) * e := by exact_mod_cast h2
  have hx : (d : ℝ) * ((8 * K + 1) / (8 * e)) = (8 * K + 1) * d / (8 * e) := by ring
  rw [hx]
  refine LRC.TwoPinner.clear_of_band (N := k) ?_ ?_
  · rw [le_div_iff₀ (by positivity)]; push_cast; linarith
  · rw [div_le_iff₀ (by positivity)]; push_cast; linarith

/-- **The three-block rule at the top reading** (the cascade's landing in the band's remainder): at `17/(8e)`, readings
in `[e/17, 7e/17]`, `[9e/17, 15e/17]` or `[e, 23e/17]` are clear. -/
theorem lonely_eight_of_three_block {S : Finset ℕ} {e : ℕ} (he : 0 < e)
    (h : ∀ d ∈ S, (e ≤ 17 * d ∧ 17 * d ≤ 7 * e) ∨ (9 * e ≤ 17 * d ∧ 17 * d ≤ 15 * e) ∨
      (e ≤ d ∧ 17 * d ≤ 23 * e)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  refine lonely_eight_of_blocks (K := 2) he fun d hd => ?_
  rcases h d hd with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨0, by omega, by omega⟩
  · exact ⟨1, by omega, by omega⟩
  · exact ⟨2, by omega, by omega⟩

end LRC.TwoBlock
