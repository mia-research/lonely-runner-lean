import LonelyRunner.LRC.Spec.TwoPinnerN

/-!
# The slow group's first block: the d_max regime reduced to the fast group

2026-09-27.  Running record: `RUNNING_LOG_order8_v1.md` E148.

Split the readings at their largest gap into a slow group `S` and a fast group `G`.  From `t₀ = 1/(8 d_min)` every slow
reading has left its first window, and while the fastest slow reading `s_top` has not reached `7/8` the whole slow group
is clear: on `[1/(8 d_min), 7/(8 s_top)]` (non-empty exactly when `s_top ≤ 7 d_min`, `S` an R1 group).  So loneliness
reduces to the fast group alone on that block.  Exact computation (E148): on Case B to readings `≤ 24`, every landing
not at the bound but 772 of 210,335 is the fast group's own landing inside this block.

* `slow_clear`: a reading in `[d_min, s_top]` is clear at every instant of the block.
* `lonely_of_fast_in_slow_block`: if every fast reading is clear at an instant of the block, every reading is.
* `block_iff_fast`, `exists_block_iff_fast`: on the block the whole question is exactly the fast group's.
* `lonely_eight_of_fast_in_slow_block` (whole numbers) and `lonely_eight_of_regimes`: the bound, or the fast group
  clear somewhere in the slow group's first block, gives loneliness.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.SlowBlock

/-- **The slow group is clear on its first block.**  `d_min ≤ d ≤ s_top`, `d_min·t ≥ 1/8`, `s_top·t ≤ 7/8`. -/
theorem slow_clear {dmin stop d t : ℝ} (ht : 0 ≤ t) (hlo : dmin ≤ d) (hhi : d ≤ stop)
    (h1 : 1 / 8 ≤ dmin * t) (h2 : stop * t ≤ 7 / 8) : (8 : ℝ)⁻¹ ≤ circDist (d * t) := by
  refine LRC.TwoPinner.clear_of_band (N := 0) ?_ ?_
  · push_cast; nlinarith
  · push_cast; nlinarith

/-- **The d_max regime.**  Readings split into a slow group (`d_min ≤ d ≤ s_top`) and a fast group; at an instant `t` of
the slow group's first block, if every fast reading is clear, every reading is clear. -/
theorem lonely_of_fast_in_slow_block {ι : Type*} [DecidableEq ι] (S G : Finset ι) (x : ι → ℝ) {dmin stop t : ℝ}
    (ht : 0 ≤ t) (hS : ∀ i ∈ S, dmin ≤ x i ∧ x i ≤ stop) (h1 : 1 / 8 ≤ dmin * t) (h2 : stop * t ≤ 7 / 8)
    (hG : ∀ i ∈ G, (8 : ℝ)⁻¹ ≤ circDist (x i * t)) :
    ∀ i ∈ S ∪ G, (8 : ℝ)⁻¹ ≤ circDist (x i * t) := by
  intro i hi
  rcases Finset.mem_union.mp hi with h | h
  · exact slow_clear ht (hS i h).1 (hS i h).2 h1 h2
  · exact hG i h

/-- **On the slow group's first block, the whole question is the fast group's.**  For `t` in the block
(`d_min·t ≥ 1/8`, `s_top·t ≤ 7/8`), every reading is clear iff every fast reading is clear. -/
theorem block_iff_fast {ι : Type*} [DecidableEq ι] (S G : Finset ι) (x : ι → ℝ) {dmin stop t : ℝ}
    (ht : 0 ≤ t) (hS : ∀ i ∈ S, dmin ≤ x i ∧ x i ≤ stop) (h1 : 1 / 8 ≤ dmin * t) (h2 : stop * t ≤ 7 / 8) :
    (∀ i ∈ S ∪ G, (8 : ℝ)⁻¹ ≤ circDist (x i * t)) ↔ (∀ i ∈ G, (8 : ℝ)⁻¹ ≤ circDist (x i * t)) :=
  ⟨fun h i hi => h i (Finset.mem_union_right _ hi), lonely_of_fast_in_slow_block S G x ht hS h1 h2⟩

/-- **The existence form.**  Some instant of the block is clear for every reading iff some instant of the block is
clear for every fast reading. -/
theorem exists_block_iff_fast {ι : Type*} [DecidableEq ι] (S G : Finset ι) (x : ι → ℝ) {dmin stop : ℝ}
    (hd : 0 < dmin) (hS : ∀ i ∈ S, dmin ≤ x i ∧ x i ≤ stop) :
    (∃ t, 1 / 8 ≤ dmin * t ∧ stop * t ≤ 7 / 8 ∧ ∀ i ∈ S ∪ G, (8 : ℝ)⁻¹ ≤ circDist (x i * t)) ↔
      (∃ t, 1 / 8 ≤ dmin * t ∧ stop * t ≤ 7 / 8 ∧ ∀ i ∈ G, (8 : ℝ)⁻¹ ≤ circDist (x i * t)) := by
  constructor
  · rintro ⟨t, h1, h2, h⟩
    exact ⟨t, h1, h2, fun i hi => h i (Finset.mem_union_right _ hi)⟩
  · rintro ⟨t, h1, h2, h⟩
    have ht : 0 ≤ t := by
      by_contra hn; push Not at hn
      have : dmin * t < 0 := mul_neg_of_pos_of_neg hd hn
      linarith
    exact ⟨t, h1, h2, lonely_of_fast_in_slow_block S G x ht hS h1 h2 h⟩

/-- **Whole-number form (the d_max regime).**  Readings `R` with least reading at least `d_min`; the slow group is the
readings up to `top ≤ 7·d_min`.  If at some instant of the slow group's first block every faster reading is clear,
the subject is lonely. -/
theorem lonely_eight_of_fast_in_slow_block {R : Finset ℕ} {dmin top : ℕ} (hd : 0 < dmin)
    (hmin : ∀ d ∈ R, dmin ≤ d) {t : ℝ} (h1 : 1 / 8 ≤ (dmin : ℝ) * t) (h2 : (top : ℝ) * t ≤ 7 / 8)
    (hG : ∀ d ∈ R, top < d → (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t)) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ R, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  have hd' : (0 : ℝ) < dmin := by exact_mod_cast hd
  have ht : 0 < t := by
    by_contra hn; push Not at hn
    have : (dmin : ℝ) * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hd'.le hn
    linarith
  refine ⟨t, ht, fun d hd => ?_⟩
  by_cases hdt : top < d
  · exact hG d hd hdt
  · push Not at hdt
    exact slow_clear ht.le (by exact_mod_cast hmin d hd) (by exact_mod_cast hdt) h1 h2

/-- **The two regimes.**  Either the bound `1/(8 d_min)` is clear (d_min's regime), or some instant of the slow group's
first block is clear for every reading above `top` (d_max's regime); either way the subject is lonely.  What is not
proved here is that one of the two always holds: exact computation on Case B to readings `≤ 24` (E148, E150) finds the
two regimes, the grid nudge and the slow group leading. -/
theorem lonely_eight_of_regimes {R : Finset ℕ} {dmin top : ℕ} (hd : 0 < dmin) (hmin : ∀ d ∈ R, dmin ≤ d)
    (h : (∀ d ∈ R, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * (1 / (8 * dmin)))) ∨
      (∃ t : ℝ, 1 / 8 ≤ (dmin : ℝ) * t ∧ (top : ℝ) * t ≤ 7 / 8 ∧
        ∀ d ∈ R, top < d → (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t))) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ R, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  rcases h with h | ⟨t, h1, h2, hG⟩
  · have hd' : (0 : ℝ) < dmin := by exact_mod_cast hd
    exact ⟨1 / (8 * dmin), by positivity, h⟩
  · exact lonely_eight_of_fast_in_slow_block hd hmin h1 h2 hG

end LRC.SlowBlock
