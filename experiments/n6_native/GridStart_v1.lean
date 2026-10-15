import LonelyRunner.LRC.Spec.OrderSixN

/-!
# The grid start (n6_native, E23)

A *lap box* fixes, for each disparity `d i`, the lap `k i` whose clear band `[k + 1/6, k + 5/6]`
it reads in. `lap_box_lonely`: the boxes meet (hence a lonely instant exists) as soon as every
ordered pair satisfies `(6 k_i + 1) d_j ≤ (6 k_j + 5) d_i`; the instant is the latest band entry.

At the grid `c·(1,2,3,4,5)` two boxes are degenerate: laps `(0,0,0,0,0)` (instant `1/(6c)`) and
laps `(0,1,2,3,4)` (instant `5/(6c)`). `grid_tight_pairs`: for the second, every pair inequality
is strict except `(i, j) = (5, 1)`, where it reads `25 d_1 ≤ 5 d_5`. The first box is
`lonely_six_of_spread` (`d_5 ≤ 5 d_1`). So near the grid the two boxes are the two sides of the
single hyperplane `d_5 = 5 d_1`.
-/

namespace N6Native

/-- **Lap boxes meet.** -/
theorem lap_box_lonely {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (d : ι → ℝ) (k : ι → ℤ)
    (hd : ∀ i ∈ s, 0 < d i) (hk : ∀ i ∈ s, 0 ≤ k i)
    (h : ∀ i ∈ s, ∀ j ∈ s, (6 * (k i : ℝ) + 1) * d j ≤ (6 * (k j : ℝ) + 5) * d i) :
    ∃ t : ℝ, 0 < t ∧ ∀ i ∈ s, (6 : ℝ)⁻¹ ≤ circDist (d i * t) := by
  set l : ι → ℝ := fun i => (6 * (k i : ℝ) + 1) / (6 * d i) with hl
  refine ⟨s.sup' hs l, ?_, fun i hi => ?_⟩
  · obtain ⟨i, hi⟩ := hs
    have hli : 0 < l i := by
      have := hd i hi; have : (0 : ℝ) ≤ k i := by exact_mod_cast hk i hi
      simp only [hl]; positivity
    exact lt_of_lt_of_le hli (Finset.le_sup' l hi)
  · obtain ⟨j, hj, hjt⟩ := Finset.exists_mem_eq_sup' hs l
    have hdi := hd i hi
    have hdj := hd j hj
    have hlo : l i ≤ s.sup' hs l := Finset.le_sup' l hi
    have hup : s.sup' hs l ≤ (6 * (k i : ℝ) + 5) / (6 * d i) := by
      rw [hjt]; simp only [hl]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h j hj i hi]
    set t := s.sup' hs l
    have h1 : (k i : ℝ) + 1 / 6 ≤ d i * t := by
      simp only [hl] at hlo
      rw [div_le_iff₀ (by positivity)] at hlo; nlinarith
    have h2 : d i * t ≤ (k i : ℝ) + 5 / 6 := by
      rw [le_div_iff₀ (by positivity)] at hup; nlinarith
    have hfr : Int.fract (d i * t) = d i * t - k i := by
      rw [Int.fract_eq_iff]
      exact ⟨by linarith, by linarith, k i, by ring⟩
    unfold circDist
    rw [hfr]
    exact le_min (by linarith) (by linarith)

/-- **The grid's second box.** Laps `k_i = i - 1` at `d_i = c·i`: the pair inequality
`(6 k_i + 1) d_j ≤ (6 k_j + 5) d_i` reads `(6i - 5) j ≤ (6j - 1) i`; it holds for all pairs, and
is an equality only at `(i, j) = (5, 1)`. -/
theorem grid_tight_pairs :
    ∀ i ∈ Finset.Icc (1 : ℤ) 5, ∀ j ∈ Finset.Icc (1 : ℤ) 5,
      (6 * i - 5) * j ≤ (6 * j - 1) * i ∧ ((6 * i - 5) * j = (6 * j - 1) * i ↔ (i = 5 ∧ j = 1)) := by
  decide

end N6Native

#print axioms N6Native.lap_box_lonely
#print axioms N6Native.grid_tight_pairs
