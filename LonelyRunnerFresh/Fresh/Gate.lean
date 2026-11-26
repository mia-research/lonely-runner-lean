import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.Dilation
import Fresh.ChainLaws
import Fresh.Doors
import Fresh.LonelyCells

/-!
# The gate lemmas, natively (Task T; v9 section 7, record `GATE_LEMMAS_v1.md` L1, L4, L5, L7)

Written 2026-10-08.  Imports `Mathlib` and the Fresh modules `Framework`, `Cascade`, `Dilation`, `ChainLaws`, `Doors`,
`LonelyCells`; nothing from the existing `LonelyRunner` repo.  Exact reals only; every disparity is positive (no runner
is stationary).  Every statement is symbolic: for every finite set `ds` of positive disparities with least element
`m` (`IsLeast`), not for a sample.

Setting.  The cascade starts at `t₀ = 1/(8m)`; the record's coordinate is `R = 8·m·t`, so `R = 1` is the start and
`R = 7`, `R = 9` are the instants `7/(8m)`, `9/(8m)`.  The `d_min` reading's zones are `R ∈ (8j − 1, 8j + 1)`; on
`R ∈ [1, 7]` it is never in the way (`dmin_clear_first_window`).  The record's `K₇` (the lonely windows in `[1, 7]`) is
here the set of lonely instants `t` with `1/(8m) ≤ t ≤ 7/(8m)`.

Results (each [L] has its `#print axioms` line below it).
* **L1(b)** `lonely_slot`: every lonely instant has `8·m·t ∈ [8j + 1, 8j + 7]` for an integer `j` (R mod 8 in
  `[1, 7]`), because `d_min` itself must be clear.  `no_lonely_in_gate`: no lonely instant has `R ∈ (7, 9)`;
  `landing_not_in_gate`: no fixed point of the cascade has `R ∈ (7, 9)`.
* **L1(a)** `landing_gt_seven_iff` (landing form, no counting): a fixed point `t⋆` has `t⋆ > 7/(8m)` iff no lonely
  instant lies in `[1/(8m), 7/(8m)]`.  `exceeds_seven_iff` (sequence form): some state exceeds `7/(8m)` iff no lonely
  instant lies in `[1/(8m), 7/(8m)]`; its `←` uses `Doors.fixed_of_bddAbove`, which carries a
  `[PROVISIONAL: counting tool]` tag.
* **L1(c)** `move_lt_add_quarter`, `move_from_first_window`: a move from `R ≤ 7` lands at `R' < R + 2 ≤ 9` (the gap
  bound; the dilation bound `< 9/7` gives the same `R' < 9` from `R ≤ 7`, `move_ratio_from_first_window`).
  `first_state_above_seven`: the first state above `R = 7` lies in `(7, 9)`; `gate_move_ge_nine`: the move from it
  lands at `R ≥ 9`, since `d_min` is in the way there with next opening exactly `R = 9`; `gate_lands_at_nine_iff`:
  it lands at exactly `R = 9` iff no runner in the way there has a next opening beyond `R = 9`.  L1(d) (that it always
  lands at exactly 9) is not proved here [OWED].
* **L4** `faster_entry_before_own_entry`, `opener_closer_is_fastest`: at the left end `u` of a cell opened by `x`, any
  faster runner `y > x` enters strictly before `x`'s own entry `u + 3/(4x)`; hence if the opener of a cell is also its
  closer, the opener is the largest element of `ds` (`IsGreatest`).  The record's "reading 7".
* **L5** `setter_gt`, `seq_le_pow`, `staircase_setter`, `staircase_card`, `staircase_rank`: every setter of a move
  from `t` exceeds `7/(8t)`; the states satisfy `t_n ≤ (9/7)^n · t₀`; so every setter of a move at step `i ≤ k`
  exceeds `7·m·(7/9)^k`; if the setters of steps `0 … k` are pairwise distinct, at least `k + 1` elements of `ds`
  exceed `7·m·(7/9)^k`, and for `|ds| = 7` the reading of rank `7 − k` (1-indexed, increasing) exceeds it.
* **L7** `strictly_clear_iff`, `interior_strictly_clear`, `strictly_clear_eventually`, `cell_persists`,
  `cell_ends_continuousOn`, `cell_limit_lonely`, `lonely_interval_ceases_only_at_touch`: a point strictly inside a
  lonely interval has every runner strictly clear;
  strict clearness survives every small deformation of the disparities; so a cell of positive width persists (a
  positive-width cell of nearby disparities contains the same point) and a family of cells with fixed opener and
  closer converges to a lonely interval.  A cell can therefore cease only where its width reaches `0`: a single-point
  cell, which is a touch (`LonelyCells.degenerate_opener_ne_closer`: the exit of one runner equals the entry of
  another).

Not done here.  L1(d) (the move from the first state above `R = 7` lands at exactly `R = 9`) [OWED]:
`gate_lands_at_nine_iff` reduces it to "no runner in the way at that state has its next opening beyond `R = 9`", and
no symbolic reason for that was found.  The record's consequence of L4 (class K2s1 empty) is not formalised here.  L2, L3 and L6 were not in this task (L6 is
`Dilation.link_slower_lap_le` / `link_faster_lap_ge`).

Provenance (existing declarations whose argument was read and understood; no proof was copied).
* L1: record `GATE_LEMMAS_v1.md` L1(a)-(c), proved there by hand in `R`-coordinates with zones; the existing repo has
  no Lean declaration of L1 that I found (searched `LRC/` for `gate`, `seven`, `nine`).  Re-derived here from the
  cascade's own `IsMove`, `InWay`, `nextOpening`.
* L4: record L4 (proof `(7 − p_y)/ρ_y ≤ 6/ρ_y < 6/ρ_s`); re-derived with `LonelyCells.opener_eq_closer_window` and
  `LonelyCells.inWay_after_entry`.
* L5: record L5 (a)-(d); re-derived with `Dilation.seq_fix_or_ratio_lt`, `Dilation.one_le_lap_of_bound` and
  `ChainLaws.IsSetterAt`.
* L7: record L7 (open crossing family, boundary of touches); re-derived as continuity statements about cells,
  with `LonelyCells.cell_of_lonely`, `cell_left_end_is_opening`, `cell_right_end_is_entry`.
-/

open Classical Filter Topology

namespace Fresh

namespace Gate

open Cascade Dilation ChainLaws

/-! ## Preliminaries -/

theorem least_pos {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : IsLeast (ds : Set ℝ) m) : 0 < m :=
  hpos m hm.1

#print axioms least_pos

/-- **`d_min` is clear on its first window**: for `1/(8m) ≤ t ≤ 7/(8m)` (`R ∈ [1, 7]`) the reading `m·t` lies in
`[1/8, 7/8]`. -/
theorem dmin_clear_first_window {m t : ℝ} (hm : 0 < m) (h1 : 1 / (8 * m) ≤ t) (h7 : t ≤ 7 / (8 * m)) :
    (1 / 8 : ℝ) ≤ distInt (m * t) := by
  rw [div_le_iff₀ (by positivity)] at h1
  rw [le_div_iff₀ (by positivity)] at h7
  apply Localisation.clear_of_window 0 <;> push_cast <;> nlinarith

#print axioms dmin_clear_first_window

/-- **`d_min` is in the way in the gate**: for `7/(8m) < t < 9/(8m)` (`R ∈ (7, 9)`) the reading `m·t` is within `1/8`
of the lap line `1`, and its next opening is exactly `9/(8m)` (`R = 9`). -/
theorem dmin_inWay_gate {m t : ℝ} (hm : 0 < m) (h7 : 7 / (8 * m) < t) (h9 : t < 9 / (8 * m)) :
    InWay m t ∧ nextOpening m t = 9 / (8 * m) := by
  rw [div_lt_iff₀ (by positivity)] at h7
  rw [lt_div_iff₀ (by positivity)] at h9
  have hk : |m * t - ((1 : ℤ) : ℝ)| < 1 / 8 := by
    rw [abs_lt]; push_cast; constructor <;> nlinarith
  refine ⟨LonelyCells.inWay_of_near 1 hk, ?_⟩
  rw [nextOpening_eq hk]
  field_simp
  norm_num

#print axioms dmin_inWay_gate

/-! ## L1(b): the slot of a lonely instant -/

/-- **L1(b), general form** [L]: if `m ∈ ds`, every lonely instant `t` has `8·m·t ∈ [8j + 1, 8j + 7]` for some integer
`j` (in the record's words, `R mod 8 ∈ [1, 7]`).  The reason: `d_min` is one of the runners and must itself be clear,
`frac (m·t) ∈ [1/8, 7/8]`. -/
theorem lonely_slot {ds : Finset ℝ} {m t : ℝ} (hm : m ∈ ds) (hl : LonelyAt ds t) :
    ∃ j : ℤ, 8 * (j : ℝ) + 1 ≤ 8 * m * t ∧ 8 * m * t ≤ 8 * (j : ℝ) + 7 := by
  have hf := (Localisation.clear_iff_fract _).mp (hl m hm)
  refine ⟨⌊m * t⌋, ?_, ?_⟩ <;> unfold Int.fract at hf <;> linarith [hf.1, hf.2]

#print axioms lonely_slot

/-- **L1(b), the gate** [L]: no lonely instant has `R ∈ (7, 9)`; `d_min` is in the way there. -/
theorem no_lonely_in_gate {ds : Finset ℝ} {m t : ℝ} (hm : m ∈ ds) (hm0 : 0 < m) (h7 : 7 / (8 * m) < t)
    (h9 : t < 9 / (8 * m)) : ¬ LonelyAt ds t := fun hl =>
  (not_inWay_iff.mpr (hl m hm)) (dmin_inWay_gate hm0 h7 h9).1

#print axioms no_lonely_in_gate

/-- **L1(b), the landing** [L]: a fixed point of the cascade is never in the gate `R ∈ (7, 9)`. -/
theorem landing_not_in_gate {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : IsLeast (ds : Set ℝ) m)
    {N : ℕ} (hN : cascadeSeq ds (1 / (8 * m)) (N + 1) = cascadeSeq ds (1 / (8 * m)) N) :
    ¬ (7 / (8 * m) < cascadeSeq ds (1 / (8 * m)) N ∧ cascadeSeq ds (1 / (8 * m)) N < 9 / (8 * m)) := by
  rintro ⟨h7, h9⟩
  have h := cascadeSeq_isMove ds (1 / (8 * m)) N
  rw [hN] at h
  exact no_lonely_in_gate hm.1 (least_pos hpos hm) h7 h9 ((isMove_self_iff hpos).mp h)

#print axioms landing_not_in_gate

/-! ## L1(a): the landing exceeds `R = 7` iff `K₇` is empty -/

/-- **L1(a), landing form** [L]: if the cascade from `1/(8m)` fixes at step `N`, its landing exceeds `7/(8m)` iff
there is no lonely instant in `[1/(8m), 7/(8m)]` (the record's `K₇ = ∅`).  No counting step. -/
theorem landing_gt_seven_iff {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ}
    {N : ℕ} (hN : cascadeSeq ds (1 / (8 * m)) (N + 1) = cascadeSeq ds (1 / (8 * m)) N) :
    7 / (8 * m) < cascadeSeq ds (1 / (8 * m)) N ↔
      ¬ ∃ t, 1 / (8 * m) ≤ t ∧ t ≤ 7 / (8 * m) ∧ LonelyAt ds t := by
  have hmv := cascadeSeq_isMove ds (1 / (8 * m))
  constructor
  · rintro h ⟨t, h1, h7, hl⟩
    have := seq_le_of_lonely hpos hl (by rw [cascadeSeq_zero]; exact h1) hmv N
    linarith
  · intro h
    by_contra hc
    push Not at hc
    apply h
    refine ⟨_, ?_, hc, ?_⟩
    · have := start_le_seq hpos hmv N
      rwa [cascadeSeq_zero] at this
    · have hh := hmv N
      rw [hN] at hh
      exact (isMove_self_iff hpos).mp hh

#print axioms landing_gt_seven_iff

/-- **L1(a), sequence form** [L]: some state of the cascade exceeds `7/(8m)` iff no lonely instant lies in
`[1/(8m), 7/(8m)]`.  The `←` direction needs that a bounded cascade fixes, `Doors.fixed_of_bddAbove`, whose last step
is tagged there `[PROVISIONAL: counting tool]` (supports "a cascade whose states stay below `7/(8m)` fixes"). -/
theorem exceeds_seven_iff {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : IsLeast (ds : Set ℝ) m) :
    (∃ n, 7 / (8 * m) < cascadeSeq ds (1 / (8 * m)) n) ↔
      ¬ ∃ t, 1 / (8 * m) ≤ t ∧ t ≤ 7 / (8 * m) ∧ LonelyAt ds t := by
  have hmv := cascadeSeq_isMove ds (1 / (8 * m))
  constructor
  · rintro ⟨n, hn⟩ ⟨t, h1, h7, hl⟩
    have := seq_le_of_lonely hpos hl (by rw [cascadeSeq_zero]; exact h1) hmv n
    linarith
  · intro h
    by_contra hc
    push Not at hc
    -- [PROVISIONAL: counting tool] (inside `Doors.fixed_of_bddAbove`), supporting "a cascade bounded by `7/(8m)` fixes".
    obtain ⟨N, hN⟩ := Doors.fixed_of_bddAbove hpos hm.1 ⟨7 / (8 * m), by rintro _ ⟨n, rfl⟩; exact hc n⟩
    exact h ⟨_, by have := start_le_seq hpos hmv N; rwa [cascadeSeq_zero] at this, hc N,
      by have hh := hmv N; rw [hN] at hh; exact (isMove_self_iff hpos).mp hh⟩

#print axioms exceeds_seven_iff

/-! ## L1(c): the first state above `R = 7` -/

/-- **The gap bound** [L]: a move from `t ≥ 1/(8m)` (with `m` a lower bound of `ds`) lands before `t + 2/(8m)`, i.e.
`R' < R + 2`.  The setter `x ≥ m` advances the instant by `g/(8x)` with `g < 2`. -/
theorem move_lt_add_quarter {ds : Finset ℝ} {m t t' : ℝ} (hm : 0 < m) (hlow : ∀ d ∈ ds, m ≤ d)
    (hmv : IsMove ds t t') : t' < t + 2 / (8 * m) := by
  rcases hmv with ⟨_, rfl⟩ | ⟨x, hx, hw, rfl, _⟩
  · have : (0 : ℝ) < 2 / (8 * m) := by positivity
    linarith
  · have hx0 : 0 < x := lt_of_lt_of_le hm (hlow x hx)
    rw [nextOpening_eq_add_gap hx0 hw]
    have hg := gap_lt_two hw
    have hg0 := gap_pos hw
    have h1 : gap x t / (8 * x) < 2 / (8 * x) := div_lt_div_of_pos_right hg (by positivity)
    have h2 : 2 / (8 * x) ≤ 2 / (8 * m) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith [hlow x hx])
    linarith

#print axioms move_lt_add_quarter

/-- **L1(c), one move** [L]: a move from a state in `[1/(8m), 7/(8m)]` lands strictly before `9/(8m)`
(`R ≤ 7 ⇒ R' < 9`). -/
theorem move_from_first_window {ds : Finset ℝ} {m t t' : ℝ} (hm : 0 < m) (hlow : ∀ d ∈ ds, m ≤ d)
    (h7 : t ≤ 7 / (8 * m)) (hmv : IsMove ds t t') : t' < 9 / (8 * m) := by
  have := move_lt_add_quarter hm hlow hmv
  have e : 7 / (8 * m) + 2 / (8 * m) = 9 / (8 * m) := by field_simp; norm_num
  linarith

#print axioms move_from_first_window

/-- **The dilation form of the same bound** [L]: from `1/(8m) ≤ t ≤ 7/(8m)` a move fixes or has `t'/t < 9/7`; either
way `t' < 9/(8m)`, the same bound as the gap form at `R = 7` (the gap form `R' < R + 2` is sharper for `R < 7`). -/
theorem move_ratio_from_first_window {ds : Finset ℝ} {m t t' : ℝ} (hm : 0 < m) (hlow : ∀ d ∈ ds, m ≤ d)
    (h1 : 1 / (8 * m) ≤ t) (h7 : t ≤ 7 / (8 * m)) (hmv : IsMove ds t t') :
    (t' < 9 / 7 * t ∨ t' = t) ∧ t' < 9 / (8 * m) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) h1
  have e : 9 / 7 * (7 / (8 * m)) = 9 / (8 * m) := by field_simp
  have h97 : 9 / 7 * t ≤ 9 / (8 * m) := by rw [← e]; gcongr
  rcases isMove_fix_or_ratio_lt hm hlow h1 hmv with h | h
  · refine ⟨Or.inr h, ?_⟩
    rw [h]; linarith
  · rw [div_lt_iff₀ ht0] at h
    exact ⟨Or.inl (by linarith), by linarith⟩

#print axioms move_ratio_from_first_window

/-- **L1(c), the first state above `R = 7`** [L]: if some state of the cascade exceeds `7/(8m)`, there is a step `n`
with every state up to `n` at most `7/(8m)` and the next state in the gate `(7/(8m), 9/(8m))`. -/
theorem first_state_above_seven {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : IsLeast (ds : Set ℝ) m)
    (h : ∃ n, 7 / (8 * m) < cascadeSeq ds (1 / (8 * m)) n) :
    ∃ n, (∀ i ≤ n, cascadeSeq ds (1 / (8 * m)) i ≤ 7 / (8 * m)) ∧
      7 / (8 * m) < cascadeSeq ds (1 / (8 * m)) (n + 1) ∧
      cascadeSeq ds (1 / (8 * m)) (n + 1) < 9 / (8 * m) := by
  have hm0 := least_pos hpos hm
  set seq := cascadeSeq ds (1 / (8 * m)) with hseq
  have hmv := cascadeSeq_isMove ds (1 / (8 * m))
  let n₀ := Nat.find h
  have hn₀ : 7 / (8 * m) < seq n₀ := Nat.find_spec h
  have hmin : ∀ i < n₀, seq i ≤ 7 / (8 * m) := fun i hi => by
    have := Nat.find_min h hi
    push Not at this
    exact this
  have hne : n₀ ≠ 0 := by
    intro h0
    rw [h0, hseq, cascadeSeq_zero] at hn₀
    have : 1 / (8 * m) ≤ 7 / (8 * m) := div_le_div_of_nonneg_right (by norm_num) (by positivity)
    linarith
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hne
  refine ⟨n, fun i hi => hmin i (by omega), by rw [show n + 1 = n₀ from hn.symm]; exact hn₀, ?_⟩
  have := move_from_first_window hm0 (fun d hd => hm.2 hd) (hmin n (by omega)) (hmv n)
  exact this

#print axioms first_state_above_seven

/-- **L1(c), the move from the gate** [L]: from a state `s₀` in the gate `(7/(8m), 9/(8m))`, `d_min` is in the way with
next opening exactly `9/(8m)`, so the move goes forward and lands at or after `9/(8m)` (`R ≥ 9`). -/
theorem gate_move_ge_nine {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : IsLeast (ds : Set ℝ) m)
    {s₀ s₁ : ℝ} (h7 : 7 / (8 * m) < s₀) (h9 : s₀ < 9 / (8 * m)) (hmv : IsMove ds s₀ s₁) :
    9 / (8 * m) ≤ s₁ := by
  obtain ⟨hw, ho⟩ := dmin_inWay_gate (least_pos hpos hm) h7 h9
  rcases hmv with ⟨hn, _⟩ | ⟨x, hx, hwx, he, hmax⟩
  · exact absurd hw (hn m hm.1)
  · rw [← ho]; exact hmax m hm.1 hw

#print axioms gate_move_ge_nine

/-- **L1(c)/(d) boundary** [L]: the move from a gate state lands at exactly `9/(8m)` iff no runner in the way there has
its next opening beyond `9/(8m)`.  (So L1(d), "the move from the first state above 7 lands at 9", is equivalent to:
no reading is in the way at that state with a zone extending past `R = 9`.  It is not proved here [OWED].) -/
theorem gate_lands_at_nine_iff {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : IsLeast (ds : Set ℝ) m)
    {s₀ s₁ : ℝ} (h7 : 7 / (8 * m) < s₀) (h9 : s₀ < 9 / (8 * m)) (hmv : IsMove ds s₀ s₁) :
    s₁ = 9 / (8 * m) ↔ ∀ y ∈ ds, InWay y s₀ → nextOpening y s₀ ≤ 9 / (8 * m) := by
  obtain ⟨hw, ho⟩ := dmin_inWay_gate (least_pos hpos hm) h7 h9
  rcases hmv with ⟨hn, _⟩ | ⟨x, hx, hwx, he, hmax⟩
  · exact absurd hw (hn m hm.1)
  · constructor
    · intro h y hy hwy
      rw [← h]; exact hmax y hy hwy
    · intro h
      apply le_antisymm
      · rw [he]; exact h x hx hwx
      · rw [← ho]; exact hmax m hm.1 hw

#print axioms gate_lands_at_nine_iff

/-! ## L4: the opener is the closer only if it is the fastest -/

/-- **L4, the entry comparison** [L]: at the left end `u` of a cell opened by `x` (`x·u = k + 1/8`), a faster runner
`y > x` that is clear at `u` enters (reaches `N + 7/8`, `N = ⌊y·u⌋`) strictly before `x`'s own entry
`u + 3/(4x)`.  Reason: `y` needs at most `6/8` of a lap, at speed `y`, and `6/(8y) < 6/(8x)`.  (Record:
`(7 − p_y)/ρ_y ≤ 6/ρ_y < 6/ρ_s`.) -/
theorem faster_entry_before_own_entry {x y u : ℝ} (hx : 0 < x) (hxy : x < y)
    (hc : (1 / 8 : ℝ) ≤ distInt (y * u)) :
    u ≤ LonelyCells.nextEntry y u ∧ LonelyCells.nextEntry y u < u + 3 / (4 * x) := by
  have hy : 0 < y := lt_trans hx hxy
  have hf := (Localisation.clear_iff_fract _).mp hc
  unfold Int.fract at hf
  refine ⟨LonelyCells.le_nextEntry hy hc, ?_⟩
  have hyb := LonelyCells.mul_nextEntry (x := y) (t := u) hy
  -- y · (nextEntry − u) ≤ 6/8
  have h1 : y * (LonelyCells.nextEntry y u - u) ≤ 6 / 8 := by nlinarith [hf.1]
  have h2 : LonelyCells.nextEntry y u - u ≤ 6 / 8 / y := by
    rw [le_div_iff₀ hy]; linarith
  have h3 : 6 / 8 / y < 3 / (4 * x) := by
    rw [div_lt_div_iff₀ hy (by positivity)]; nlinarith
  linarith

#print axioms faster_entry_before_own_entry

/-- **L4** [L]: if the opener `x` of a cell `[u, w]` is also its closer (`x·u = k + 1/8`, `x·w = k' + 7/8`), then `x`
is the largest element of `ds`.  The cell is then `x`'s whole window, of width `3/(4x)`
(`LonelyCells.opener_eq_closer_window`), and a faster runner would enter inside it (`faster_entry_before_own_entry`)
and be in the way just after its entry, contradicting loneliness of the cell. -/
theorem opener_closer_is_fastest {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {u w x : ℝ}
    (h : LonelyCells.IsCell ds u w) (hx : x ∈ ds) {k k' : ℤ} (hu : x * u = (k : ℝ) + 1 / 8)
    (hw : x * w = (k' : ℝ) + 7 / 8) : IsGreatest (ds : Set ℝ) x := by
  have hx0 := hpos x hx
  obtain ⟨-, hwidth⟩ := LonelyCells.opener_eq_closer_window hx hx0 hu hw h.2.1 h.2.2.1
  refine ⟨hx, fun y hy => ?_⟩
  by_contra hc
  push Not at hc
  have hy0 := hpos y hy
  have hul : u ∈ LonelyCells.lonelySet ds := h.2.2.1 ⟨le_rfl, h.2.1⟩
  obtain ⟨hb1, hb2⟩ := faster_entry_before_own_entry hx0 hc (hul y hy)
  set b := LonelyCells.nextEntry y u with hbdef
  have hbw : b < w := by linarith
  set s := min (b + 1 / (8 * y)) w with hsdef
  have hq : (0 : ℝ) < 1 / (8 * y) := by positivity
  have hs1 : b < s := lt_min (by linarith) hbw
  have hs2 : s < b + 1 / (4 * y) := by
    have : 1 / (8 * y) < 1 / (4 * y) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hwy := LonelyCells.inWay_after_entry hy0 (LonelyCells.mul_nextEntry (x := y) (t := u) hy0) hs1 hs2
  exact LonelyCells.not_lonely_of_inWay hy hwy (h.2.2.1 ⟨by linarith, min_le_right _ _⟩)

#print axioms opener_closer_is_fastest

/-! ## L5: the staircase -/

/-- **L5(b)** [L]: a runner `x ≥ m` in the way at `t ≥ 1/(8m)` has `x > 7/(8t)` (in readings: `ρ > 7/R`).  It is past
its first lap (`Dilation.one_le_lap_of_bound`), so `x·t > 1 − 1/8`. -/
theorem setter_gt {m x t : ℝ} (hm : 0 < m) (hmx : m ≤ x) (ht : 1 / (8 * m) ≤ t) (hw : InWay x t) :
    7 / (8 * t) < x := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have hN := one_le_lap_of_bound hm hmx ht hw
  have hN' : (1 : ℝ) ≤ (lap x t : ℝ) := by exact_mod_cast hN
  have hb := abs_lt.mp (abs_sub_lap_lt hw)
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

#print axioms setter_gt

/-- **L5(a), iterated** [L]: along the cascade from `1/(8m)`, `t_n ≤ (9/7)^n · 1/(8m)` (each step fixes or multiplies
by less than `9/7`, `Dilation.seq_fix_or_ratio_lt`).  This is a bound on the instant at step `n`; it states nothing
about the number of moves. -/
theorem seq_le_pow {ds : Finset ℝ} {m : ℝ} (hm : 0 < m) (hlow : ∀ d ∈ ds, m ≤ d) (n : ℕ) :
    cascadeSeq ds (1 / (8 * m)) n ≤ (9 / 7) ^ n * (1 / (8 * m)) := by
  have hpos : ∀ d ∈ ds, 0 < d := fun d hd => lt_of_lt_of_le hm (hlow d hd)
  have hmv := cascadeSeq_isMove ds (1 / (8 * m))
  induction n with
  | zero => simp [cascadeSeq_zero]
  | succ n ih =>
    have hge : 1 / (8 * m) ≤ cascadeSeq ds (1 / (8 * m)) n := by
      have := start_le_seq hpos hmv n; rwa [cascadeSeq_zero] at this
    have hn0 : 0 < cascadeSeq ds (1 / (8 * m)) n := lt_of_lt_of_le (by positivity) hge
    have hp : (0 : ℝ) ≤ (9 / 7) ^ n * (1 / (8 * m)) := by positivity
    rcases seq_fix_or_ratio_lt hm hlow (cascadeSeq_zero ds _) hmv n with h | h
    · rw [h, pow_succ]; nlinarith
    · rw [div_lt_iff₀ hn0] at h
      rw [pow_succ]; nlinarith

#print axioms seq_le_pow

/-- **L5(d), one setter** [L]: the setter of the move at any step `i ≤ k` of the cascade from `1/(8m)` exceeds
`7·m·(7/9)^k`.  (Record: the `i`-th setter has `ρ > 7/R_{i−1} ≥ 7·(7/9)^{i−1}`.) -/
theorem staircase_setter {ds : Finset ℝ} {m : ℝ} (hm : 0 < m) (hlow : ∀ d ∈ ds, m ≤ d) {i k : ℕ} (hik : i ≤ k)
    {x : ℝ} (hx : IsSetterAt ds (cascadeSeq ds (1 / (8 * m))) i x) : 7 * m * (7 / 9) ^ k < x := by
  have hpos : ∀ d ∈ ds, 0 < d := fun d hd => lt_of_lt_of_le hm (hlow d hd)
  have hmv := cascadeSeq_isMove ds (1 / (8 * m))
  set t := cascadeSeq ds (1 / (8 * m)) i with ht
  have hge : 1 / (8 * m) ≤ t := by
    have := start_le_seq hpos hmv i; rwa [cascadeSeq_zero] at this
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) hge
  have h1 := setter_gt hm (hlow x hx.1) hge hx.2.1
  have h2 := seq_le_pow hm hlow (ds := ds) i
  rw [← ht] at h2
  -- 7·m·(7/9)^i ≤ 7/(8t)
  have hp : (0 : ℝ) < (9 / 7) ^ i := by positivity
  have hprod : (7 / 9 : ℝ) ^ i * (9 / 7) ^ i = 1 := by rw [← mul_pow]; norm_num
  have h3 : 7 * m * (7 / 9) ^ i ≤ 7 / (8 * t) := by
    rw [le_div_iff₀ (by positivity)]
    have h2' : 8 * m * t ≤ (9 / 7) ^ i := by
      rw [show (9 / 7 : ℝ) ^ i * (1 / (8 * m)) = (9 / 7) ^ i / (8 * m) by ring, le_div_iff₀ (by positivity)] at h2
      linarith
    have hq : (0 : ℝ) ≤ (7 / 9) ^ i := by positivity
    calc 7 * m * (7 / 9) ^ i * (8 * t) = 7 * (7 / 9) ^ i * (8 * m * t) := by ring
      _ ≤ 7 * (7 / 9) ^ i * (9 / 7) ^ i := by gcongr
      _ = 7 := by rw [mul_assoc, hprod, mul_one]
  have h4 : (7 / 9 : ℝ) ^ k ≤ (7 / 9) ^ i := pow_le_pow_of_le_one (by norm_num) (by norm_num) hik
  have h5 : 7 * m * (7 / 9) ^ k ≤ 7 * m * (7 / 9) ^ i := by gcongr
  linarith

#print axioms staircase_setter

/-- **L5(d), the staircase** [L]: if the moves at steps `0, …, k` of the cascade from `1/(8m)` are forward, with
setters `w 0, …, w k` that are pairwise distinct, then at least `k + 1` elements of `ds` exceed `7·m·(7/9)^k`.
[PROVISIONAL: counting tool] the last step (an injective image of `{0, …, k}` inside a finite set has `k + 1`
elements) supports the claim "the `(k+1)`-th largest reading exceeds `7·(7/9)^k`".  No bound on the number of moves
is stated: `k` is given by the hypothesis that the first `k + 1` setters exist and are distinct. -/
theorem staircase_card {ds : Finset ℝ} {m : ℝ} (hm : 0 < m) (hlow : ∀ d ∈ ds, m ≤ d) {k : ℕ} {w : ℕ → ℝ}
    (hw : ∀ i ≤ k, IsSetterAt ds (cascadeSeq ds (1 / (8 * m))) i (w i))
    (hinj : Set.InjOn w (Set.Iic k)) :
    k + 1 ≤ (ds.filter (fun x => 7 * m * (7 / 9) ^ k < x)).card := by
  have hsub : (Finset.range (k + 1)).image w ⊆ ds.filter (fun x => 7 * m * (7 / 9) ^ k < x) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    exact Finset.mem_filter.mpr ⟨(hw i hik).1, staircase_setter hm hlow hik (hw i hik)⟩
  -- [PROVISIONAL: counting tool] supporting "the (k+1)-th largest reading exceeds 7·(7/9)^k".
  have hcard : ((Finset.range (k + 1)).image w).card = k + 1 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    exact hinj (Set.mem_Iic.mpr (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)))
      (Set.mem_Iic.mpr (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))) hab
  rw [← hcard]
  exact Finset.card_le_card hsub

#print axioms staircase_card

/-- **L5(d), rank form** [L]: for `|ds| = 7`, with the readings listed in increasing order
`e 0 < e 1 < … < e 6` (`Finset.orderEmbOfFin`), if at least `k + 1` elements of `ds` exceed `c` then the element of
rank `7 − k` (1-indexed; `e (6 − k)`) exceeds `c`.  With `staircase_card` and `c = 7·m·(7/9)^k` this is the record's
`ρ_{7−k} > 7·(7/9)^k` (readings `ρ = d/m`).
[PROVISIONAL: counting tool] (cardinality of the elements `≤ c` against `7 − k`), supporting the same claim as
`staircase_card`. -/
theorem staircase_rank {ds : Finset ℝ} (hcard : ds.card = 7) {c : ℝ} {k : ℕ} (hk : k ≤ 6)
    (h : k + 1 ≤ (ds.filter (fun x => c < x)).card) :
    c < ds.orderEmbOfFin hcard ⟨6 - k, by omega⟩ := by
  by_contra hle
  push Not at hle
  set e := ds.orderEmbOfFin hcard with he
  set j₀ : Fin 7 := ⟨6 - k, by omega⟩ with hj₀
  have hsub : (Finset.Iic j₀).image e ⊆ ds.filter (fun x => ¬ c < x) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_filter.mpr ⟨Finset.orderEmbOfFin_mem ds hcard j, ?_⟩
    push Not
    exact le_trans (e.monotone (Finset.mem_Iic.mp hj)) hle
  -- [PROVISIONAL: counting tool] supporting "the rank-(7−k) reading exceeds c".
  have h1 : ((Finset.Iic j₀).image e).card = 7 - k := by
    rw [Finset.card_image_of_injective _ e.injective, Fin.card_Iic]
    simp [hj₀]
    omega
  have h2 := Finset.card_le_card hsub
  have h3 := Finset.card_filter_add_card_filter_not (s := ds) (fun x => c < x)
  omega

#print axioms staircase_rank

/-! ## L7: cells change only through touches

Native objects: a deformation is a path `γ : ℝ → ι → ℝ` of disparity tuples (`ι` finite), every value positive (no
runner stationary); the disparity set at parameter `s` is `Finset.univ.image (γ s)`.  The statements are about
continuity of cells, not about existence of cells. -/

/-- The lonely condition for a tuple of disparities, read runner by runner. -/
theorem lonelyAt_image_iff {ι : Type*} [Fintype ι] (d : ι → ℝ) (t : ℝ) :
    LonelyAt (Finset.univ.image d) t ↔ ∀ i, (1 / 8 : ℝ) ≤ distInt (d i * t) := by
  constructor
  · intro h i
    exact h _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  · intro h x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact h i

#print axioms lonelyAt_image_iff

/-- **Strict clearness is an open window** [L]: `1/8 < distInt y` iff `y` lies strictly inside some window
`(N + 1/8, N + 7/8)`. -/
theorem strictly_clear_iff (y : ℝ) :
    (1 / 8 : ℝ) < distInt y ↔ ∃ N : ℤ, (N : ℝ) + 1 / 8 < y ∧ y < (N : ℝ) + 7 / 8 := by
  constructor
  · intro h
    refine ⟨⌊y⌋, ?_, ?_⟩
    · have h0 := lt_of_lt_of_le h (Localisation.distInt_le y ⌊y⌋)
      have hf0 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
      rw [abs_of_nonneg (by linarith)] at h0
      linarith
    · have h1 := lt_of_lt_of_le h (Localisation.distInt_le y (⌊y⌋ + 1))
      have hf1 : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
      push_cast at h1
      rw [abs_of_neg (by linarith)] at h1
      linarith
  · rintro ⟨N, h1, h2⟩
    unfold distInt
    rcases le_or_gt (round y) N with hz | hz
    · have : ((round y : ℤ) : ℝ) ≤ N := by exact_mod_cast hz
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have : (N : ℝ) + 1 ≤ ((round y : ℤ) : ℝ) := by exact_mod_cast hz
      rw [abs_of_nonpos (by linarith)]
      linarith

#print axioms strictly_clear_iff

/-- **L7, interior points are strictly clear** [L]: if `[u, w]` is lonely and `u < t < w`, every runner is strictly
clear at `t`.  A runner standing at exactly `1/8` at `t` would be at an opening (in the way just before `t`) or at an
entry (in the way just after `t`), both inside `[u, w]`. -/
theorem interior_strictly_clear {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {u w t : ℝ}
    (hsub : Set.Icc u w ⊆ LonelyCells.lonelySet ds) (hut : u < t) (htw : t < w) {d : ℝ} (hd : d ∈ ds) :
    (1 / 8 : ℝ) < distInt (d * t) := by
  have hd0 := hpos d hd
  have hl : t ∈ LonelyCells.lonelySet ds := hsub ⟨hut.le, htw.le⟩
  have hf := (Localisation.clear_iff_fract _).mp (hl d hd)
  have hq : (1 : ℝ) / (8 * d) < 1 / (4 * d) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hq0 : (0 : ℝ) < 1 / (8 * d) := by positivity
  rw [strictly_clear_iff]
  refine ⟨⌊d * t⌋, ?_, ?_⟩
  · rcases lt_or_eq_of_le hf.1 with h1 | h1
    · unfold Int.fract at h1; linarith
    · exfalso
      have ha : d * t = ((⌊d * t⌋ : ℤ) : ℝ) + 1 / 8 := by unfold Int.fract at h1; linarith
      set s := max u (t - 1 / (8 * d)) with hsdef
      have hs1 : t - 1 / (4 * d) < s := lt_of_lt_of_le (by linarith) (le_max_right _ _)
      have hs2 : s < t := max_lt hut (by linarith)
      exact LonelyCells.not_lonely_of_inWay hd (LonelyCells.inWay_before_opening hd0 ha hs1 hs2)
        (hsub ⟨le_max_left _ _, by linarith⟩)
  · rcases lt_or_eq_of_le hf.2 with h1 | h1
    · unfold Int.fract at h1; linarith
    · exfalso
      have hb : d * t = ((⌊d * t⌋ : ℤ) : ℝ) + 7 / 8 := by unfold Int.fract at h1; linarith
      set s := min w (t + 1 / (8 * d)) with hsdef
      have hs1 : t < s := lt_min htw (by linarith)
      have hs2 : s < t + 1 / (4 * d) := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      exact LonelyCells.not_lonely_of_inWay hd (LonelyCells.inWay_after_entry hd0 hb hs1 hs2)
        (hsub ⟨by linarith, min_le_left _ _⟩)

#print axioms interior_strictly_clear

/-- **L7, strict clearness survives small deformations** [L]: if every runner of `γ s₀` is strictly clear at `t`
and the path is continuous at `s₀`, the same holds for every `s` near `s₀`. -/
theorem strictly_clear_eventually {ι : Type*} [Finite ι] (γ : ℝ → ι → ℝ) {s₀ t : ℝ} (hγ : ContinuousAt γ s₀)
    (h : ∀ i, (1 / 8 : ℝ) < distInt (γ s₀ i * t)) :
    ∀ᶠ s in 𝓝 s₀, ∀ i, (1 / 8 : ℝ) < distInt (γ s i * t) := by
  rw [Filter.eventually_all]
  intro i
  obtain ⟨N, h1, h2⟩ := (strictly_clear_iff _).mp (h i)
  have hc : ContinuousAt (fun s => γ s i * t) s₀ := (continuousAt_pi.mp hγ i).mul continuousAt_const
  have hev : ∀ᶠ s in 𝓝 s₀, γ s i * t ∈ Set.Ioo ((N : ℝ) + 1 / 8) ((N : ℝ) + 7 / 8) :=
    hc.eventually_mem (Ioo_mem_nhds h1 h2)
  filter_upwards [hev] with s hs
  exact (strictly_clear_iff _).mpr ⟨N, hs.1, hs.2⟩

#print axioms strictly_clear_eventually

/-- **L7, a cell of positive width persists** [L]: if `[u, w]` is a cell of `γ s₀` with `u < w`, then for every `s`
near `s₀` the midpoint `(u + w)/2` lies strictly inside a cell of `γ s` (which therefore has positive width). -/
theorem cell_persists {ι : Type*} [Fintype ι] (γ : ℝ → ι → ℝ) (hγpos : ∀ s i, 0 < γ s i) {s₀ u w : ℝ}
    (hγ : ContinuousAt γ s₀) (h : LonelyCells.IsCell (Finset.univ.image (γ s₀)) u w) (huw : u < w) :
    ∀ᶠ s in 𝓝 s₀, ∃ u' w', LonelyCells.IsCell (Finset.univ.image (γ s)) u' w' ∧
      u' < (u + w) / 2 ∧ (u + w) / 2 < w' := by
  set t := (u + w) / 2 with htdef
  have hut : u < t := by rw [htdef]; linarith
  have htw : t < w := by rw [htdef]; linarith
  have hpos₀ : ∀ d ∈ Finset.univ.image (γ s₀), 0 < d := by
    intro d hd; obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hd; exact hγpos _ i
  have hstrict : ∀ i, (1 / 8 : ℝ) < distInt (γ s₀ i * t) := fun i =>
    interior_strictly_clear hpos₀ h.2.2.1 hut htw (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hne₀ := LonelyCells.nonempty_of_cell h
  obtain ⟨_, hi₀⟩ := hne₀
  obtain ⟨i₀, -, -⟩ := Finset.mem_image.mp hi₀
  filter_upwards [strictly_clear_eventually γ hγ hstrict] with s hs
  have hposs : ∀ d ∈ Finset.univ.image (γ s), 0 < d := by
    intro d hd; obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hd; exact hγpos _ i
  have hne : (Finset.univ.image (γ s)).Nonempty := ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ i₀)⟩
  have hl : t ∈ LonelyCells.lonelySet (Finset.univ.image (γ s)) :=
    (lonelyAt_image_iff (γ s) t).mpr (fun i => (hs i).le)
  have ht0 : 0 < t := lt_trans h.1 hut
  obtain ⟨x, hx, y, hy, hc, hT, hS⟩ := LonelyCells.cell_of_lonely hposs hne ht0 hl
  refine ⟨_, _, hc, lt_of_le_of_ne hT ?_, lt_of_le_of_ne hS ?_⟩
  · intro he
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    have hm := LonelyCells.mul_lastOpening (x := γ s i) (t := t) (hγpos s i)
    rw [he] at hm
    have h8 : distInt (γ s i * t) = 1 / 8 := by
      rw [hm, add_comm]; exact Cascade.distInt_eighth_add_int _
    linarith [hs i]
  · intro he
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    have hm := LonelyCells.mul_nextEntry (x := γ s i) (t := t) (hγpos s i)
    rw [← he] at hm
    obtain ⟨N, h1, h2⟩ := (strictly_clear_iff _).mp (hs i)
    rw [hm] at h1 h2
    have a1 : ((⌊γ s i * t⌋ : ℤ) : ℝ) < (N : ℝ) := by linarith
    have a2 : (N : ℝ) < ((⌊γ s i * t⌋ : ℤ) : ℝ) + 1 := by linarith
    have b1 : ⌊γ s i * t⌋ < N := by exact_mod_cast a1
    have b2 : N < ⌊γ s i * t⌋ + 1 := by exact_mod_cast a2
    omega

#print axioms cell_persists

/-- **L7, the ends of a cell with fixed opener and closer are continuous** [L]: with opener `a` on lap `k` and closer
`b` on lap `k'`, the left end `(k + 1/8)/d_a`, the right end `(k' + 7/8)/d_b` and the width are continuous functions
of the disparities on the set where `d_a, d_b > 0`. -/
theorem cell_ends_continuousOn {ι : Type*} (a b : ι) (k k' : ℝ) :
    ContinuousOn (fun d : ι → ℝ => (k + 1 / 8) / d a) {d | 0 < d a ∧ 0 < d b} ∧
    ContinuousOn (fun d : ι → ℝ => (k' + 7 / 8) / d b) {d | 0 < d a ∧ 0 < d b} ∧
    ContinuousOn (fun d : ι → ℝ => (k' + 7 / 8) / d b - (k + 1 / 8) / d a) {d | 0 < d a ∧ 0 < d b} := by
  have hA : ContinuousOn (fun d : ι → ℝ => (k + 1 / 8) / d a) {d | 0 < d a ∧ 0 < d b} :=
    continuousOn_const.div (continuous_apply a).continuousOn (fun d hd => hd.1.ne')
  have hB : ContinuousOn (fun d : ι → ℝ => (k' + 7 / 8) / d b) {d | 0 < d a ∧ 0 < d b} :=
    continuousOn_const.div (continuous_apply b).continuousOn (fun d hd => hd.2.ne')
  exact ⟨hA, hB, hB.sub hA⟩

#print axioms cell_ends_continuousOn

/-- **L7, the limit of lonely intervals is lonely** [L]: if, for every `s < s₀`, `[u s, w s]` is a lonely interval of
`γ s` (for instance a cell with fixed opener and closer, whose ends are continuous by `cell_ends_continuousOn`), and
`γ`, `u`, `w` are continuous at `s₀`, then `[u s₀, w s₀]` is a lonely interval of `γ s₀` (possibly a single point). -/
theorem cell_limit_lonely {ι : Type*} [Fintype ι] (γ : ℝ → ι → ℝ) {s₀ : ℝ} (u w : ℝ → ℝ)
    (hγ : ContinuousAt γ s₀) (hu : ContinuousAt u s₀) (hw : ContinuousAt w s₀)
    (hcell : ∀ s < s₀, u s ≤ w s ∧ Set.Icc (u s) (w s) ⊆ LonelyCells.lonelySet (Finset.univ.image (γ s))) :
    u s₀ ≤ w s₀ ∧ Set.Icc (u s₀) (w s₀) ⊆ LonelyCells.lonelySet (Finset.univ.image (γ s₀)) := by
  have huw : u s₀ ≤ w s₀ := by
    have ht : Tendsto (fun s => w s - u s) (𝓝[<] s₀) (𝓝 (w s₀ - u s₀)) :=
      ((hw.sub hu).tendsto).mono_left nhdsWithin_le_nhds
    have := ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun s hs => sub_nonneg.mpr (hcell s hs).1)
    linarith
  refine ⟨huw, fun t ht => ?_⟩
  set f : ℝ → ℝ := fun s => max (u s) (min t (w s)) with hfdef
  have hf : ContinuousAt f s₀ := hu.max (continuousAt_const.min hw)
  have hf₀ : f s₀ = t := by
    simp only [hfdef]
    rw [min_eq_left ht.2, max_eq_right ht.1]
  show LonelyAt _ t
  rw [lonelyAt_image_iff]
  intro i
  rw [Localisation.le_distInt_iff]
  intro z
  have hg : ContinuousAt (fun s => |γ s i * f s - z|) s₀ :=
    (((continuousAt_pi.mp hγ i).mul hf).sub continuousAt_const).abs
  have hlim : Tendsto (fun s => |γ s i * f s - z|) (𝓝[<] s₀) (𝓝 (|γ s₀ i * f s₀ - z|)) :=
    hg.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ s in 𝓝[<] s₀, (1 / 8 : ℝ) ≤ |γ s i * f s - z| := by
    refine eventually_nhdsWithin_of_forall fun s hs => ?_
    have hc := hcell s hs
    have hmem : f s ∈ Set.Icc (u s) (w s) := ⟨le_max_left _ _, max_le hc.1 (min_le_right _ _)⟩
    have hl := (lonelyAt_image_iff (γ s) (f s)).mp (hc.2 hmem) i
    exact (Localisation.le_distInt_iff _ _).mp hl z
  have := ge_of_tendsto hlim hev
  rwa [hf₀] at this

#print axioms cell_limit_lonely

/-- **L7, a lonely interval ceases only through a touch** [L]: suppose `[u s, w s]` is lonely for `γ s` for every
`s < s₀` (`u`, `w`, `γ` continuous at `s₀`), and just after `s₀` the open interval `(u s₀, w s₀)` holds no lonely
instant of `γ s` (the interval has ceased).  Then `u s₀ = w s₀`: the width `w s − u s` tends to `0` at `s₀`, and
`[u s₀, u s₀]` is a single-point lonely set at which an opening meets an entry (for a cell, the touch of
`LonelyCells.degenerate_opener_ne_closer`, two different runners).  A lonely interval of positive width cannot cease:
its interior is strictly clear (`interior_strictly_clear`) and strict clearness survives (`strictly_clear_eventually`).
"Cease" is the hypothesis `hgone`, stated on the interval itself; nothing is said about other cells. -/
theorem lonely_interval_ceases_only_at_touch {ι : Type*} [Fintype ι] (γ : ℝ → ι → ℝ) (hγpos : ∀ s i, 0 < γ s i)
    {s₀ : ℝ} (u w : ℝ → ℝ) (hγ : ContinuousAt γ s₀) (hu : ContinuousAt u s₀) (hw : ContinuousAt w s₀)
    (hcell : ∀ s < s₀, u s ≤ w s ∧ Set.Icc (u s) (w s) ⊆ LonelyCells.lonelySet (Finset.univ.image (γ s)))
    (hgone : ∀ᶠ s in 𝓝[>] s₀, ∀ t ∈ Set.Ioo (u s₀) (w s₀),
      t ∉ LonelyCells.lonelySet (Finset.univ.image (γ s))) :
    u s₀ = w s₀ ∧ Tendsto (fun s => w s - u s) (𝓝 s₀) (𝓝 0) := by
  obtain ⟨huw, hsub⟩ := cell_limit_lonely γ u w hγ hu hw hcell
  have heq : u s₀ = w s₀ := by
    by_contra hne
    have hlt : u s₀ < w s₀ := lt_of_le_of_ne huw hne
    set t := (u s₀ + w s₀) / 2 with htdef
    have hut : u s₀ < t := by rw [htdef]; linarith
    have htw : t < w s₀ := by rw [htdef]; linarith
    have hpos₀ : ∀ d ∈ Finset.univ.image (γ s₀), 0 < d := by
      intro d hd; obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hd; exact hγpos _ i
    have hstrict : ∀ i, (1 / 8 : ℝ) < distInt (γ s₀ i * t) := fun i =>
      interior_strictly_clear hpos₀ hsub hut htw (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hev := (strictly_clear_eventually γ hγ hstrict)
    have hev' : ∀ᶠ s in 𝓝[>] s₀, ∀ i, (1 / 8 : ℝ) < distInt (γ s i * t) := nhdsWithin_le_nhds hev
    obtain ⟨s, hs1, hs2⟩ := (hev'.and hgone).exists
    exact hs2 t ⟨hut, htw⟩ ((lonelyAt_image_iff (γ s) t).mpr (fun i => (hs1 i).le))
  refine ⟨heq, ?_⟩
  have := (hw.sub hu).tendsto
  rwa [heq, sub_self] at this

#print axioms lonely_interval_ceases_only_at_touch

end Gate

end Fresh
