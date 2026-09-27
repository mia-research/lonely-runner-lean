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

end LRC.SlowBlock
