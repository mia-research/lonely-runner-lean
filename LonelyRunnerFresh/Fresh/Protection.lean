import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.Dilation

/-!
# Cumulative protection of a reading across a window of cascade moves (Task H)

Built on `Fresh/Framework.lean` (`distInt`, `InWay`, `nextOpening`, `IsMove`), `Fresh/Cascade.lean` (`distInt_le`,
`nextOpening_eq`) and `Fresh/Dilation.lean` (`gap`, `gap_pos`, `gap_lt_two`, `reading_shift`).  Nothing is imported
from the existing `LonelyRunner` repo; every proof below was written for this file.  Exact reals only; every
disparity used is positive (no runner is stationary).

The owner's idea (2026-10-07): after a setter `b` opens at `t_b` (`b·t_b = P + 1/8` exactly), the cascade makes moves
set by `c, d, e`; `b` stays clear through them if `b/c + b/d + b/e ≤ 3`.

Setting.  States `t 0, t 1, …, t n`; the move `t k → t (k+1)` (for `k < n`) is a forward move set by `x k > 0`: `x k` is
in the way at `t k` and `t (k+1) = nextOpening (x k) (t k)`.  (`exists_setters` shows every forward step of a cascade
sequence `IsMove ds` supplies such setters.)  `g k = gap (x k) (t k) ∈ (0, 2)`.

Contents.
* (1) `one_move_shift`: one move shifts every reading `b·t` (in laps) by `g·b/(8x)`; `telescope`: over the window,
  `b·t j = b·t 0 + Σ_{k<j} g_k·b/(8 x_k)`; `telescope_lower_edge`: with `b·t 0 = P + 1/8`.
  `shift_pos`, `shift_lt`: `0 < g·b/(8x) < b/(4x)` for `b > 0`.
* (2) `protection_offset` (reading at `P + 1/8 + δ`, `δ ≥ 0`: protected while `Σ b/x_k ≤ 3 − 4δ`) and its case `δ = 0`,
  `protection` (`Σ_{k<n} b/x_k ≤ 3` ⇒ `P + 1/8 < b·t j < P + 7/8` for every `1 ≤ j ≤ n`), `protection_not_inWay`.
* (3) `recapture_sum_gt`: if `b` is in the way at some `t j` (`j ≤ n`), then `3 < Σ_{k<j} b/x_k`.
* (4) `no_recapture_of_faster` (`x k ≥ b` for `k < n`, `n ≤ 3`) and `no_recapture_one_move` (one move, any setter with
  `3·x ≥ b`); relation to `no_return_after_faster` / `no_return_after_few_faster` in the remark after them.
* (5) `third_iff`, `owner_ratio_eq`, `owner_iff_fails`: the owner's line `b/(b/c+b/d+b/e) ≥ 1/3 ⟺ b/c+b/d+b/e ≤ 3`
  is an algebra slip; the correct equivalence is with `≤ 3b`.
* (6) The limit (lower edge only), with the exact example `offset_recapture_example`.

No bound on the number of moves or on a chain's length is stated anywhere (rule 7): every statement is LOCAL to a
given window of moves `t 0 → … → t n`, whatever produced it.

Provenance.  `one_move_shift` is `Dilation.reading_shift` divided by 8 (existing `Cascade/Iteration.lean`
`other_reading_shift`).  The telescoped form is the `[reasoned]` paragraph at the end of `Fresh/Dilation.lean`, here
proved.  The protection theorems have no direct counterpart in the existing repo; their relatives are
`WordRules.no_return_after_faster` (`LRC/Cascade/SmallOrders.lean`) and `FasterMoves.no_return_after_few_faster`
(`LRC/Cascade/FourDifferences.lean`), which were read and understood; their proofs (lap factors, a Bernoulli inequality)
were not used: the argument here is additive, in laps, and needs only `0 < g < 2`.
-/

open Classical

namespace Fresh

namespace Protection

open Cascade Dilation

/-! ## The window of a reading -/

/-- A reading in the closed window `[P + 1/8, P + 7/8]` is at distance at least `1/8` from every integer. -/
theorem eighth_le_distInt_of_window {y : ℝ} {P : ℤ} (h1 : (P : ℝ) + 1 / 8 ≤ y) (h2 : y ≤ (P : ℝ) + 7 / 8) :
    (1 / 8 : ℝ) ≤ distInt y := by
  by_contra hc
  rw [not_le] at hc
  unfold distInt at hc
  have hb := abs_lt.mp hc
  have hr1 : (P : ℝ) < (round y : ℝ) := by linarith
  have hr2 : (round y : ℝ) < (P : ℝ) + 1 := by linarith
  have a1 : P < round y := by exact_mod_cast hr1
  have a2 : round y < P + 1 := by exact_mod_cast hr2
  omega

#print axioms eighth_le_distInt_of_window

/-- So a reading `b·t` in the window is not in the way. -/
theorem not_inWay_of_window {b t : ℝ} {P : ℤ} (h1 : (P : ℝ) + 1 / 8 ≤ b * t) (h2 : b * t ≤ (P : ℝ) + 7 / 8) :
    ¬ InWay b t := by
  unfold InWay
  exact not_lt.mpr (eighth_le_distInt_of_window h1 h2)

#print axioms not_inWay_of_window

/-! ## (1) One move, and the telescoped window -/

/-- **(1a) One move shifts every reading by `g·b/(8x)` laps**: `b·t' = b·t + gap·b/(8x)`.
(`Dilation.reading_shift`, which is the same identity in eighths.) -/
theorem one_move_shift {x t : ℝ} (hx : 0 < x) (h : InWay x t) (b : ℝ) :
    b * nextOpening x t = b * t + gap x t * b / (8 * x) := by
  have hs := reading_shift hx h b
  have e : gap x t * b / (8 * x) = (gap x t * b / x) / 8 := by
    field_simp
  rw [e]
  linarith

#print axioms one_move_shift

/-- **(1b) The shift is positive** for `b > 0`. -/
theorem shift_pos {x t b : ℝ} (hx : 0 < x) (h : InWay x t) (hb : 0 < b) : 0 < gap x t * b / (8 * x) :=
  div_pos (mul_pos (gap_pos h) hb) (by positivity)

#print axioms shift_pos

/-- **(1c) The shift is less than `b/(4x)`**, because `g < 2`. -/
theorem shift_lt {x t b : ℝ} (hx : 0 < x) (h : InWay x t) (hb : 0 < b) :
    gap x t * b / (8 * x) < b / x / 4 := by
  have h2 : gap x t * b < 2 * b := mul_lt_mul_of_pos_right (gap_lt_two h) hb
  have e : b / x / 4 = 2 * b / (8 * x) := by field_simp; ring
  rw [e]
  exact div_lt_div_of_pos_right h2 (by positivity)

#print axioms shift_lt

/-- **(1d) Telescoped window.**  Over forward moves `t k → t (k+1) = nextOpening (x k) (t k)` (`x k` in the way at
`t k`), every reading satisfies `b·t j = b·t 0 + Σ_{k<j} g_k·b/(8 x_k)` for `j ≤ n`. -/
theorem telescope {t x : ℕ → ℝ} {n : ℕ} (hx : ∀ k < n, 0 < x k) (hw : ∀ k < n, InWay (x k) (t k))
    (hs : ∀ k < n, t (k + 1) = nextOpening (x k) (t k)) (b : ℝ) :
    ∀ j ≤ n, b * t j = b * t 0 + ∑ k ∈ Finset.range j, gap (x k) (t k) * b / (8 * x k) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    rw [Finset.sum_range_succ, hs j (by omega), one_move_shift (hx j (by omega)) (hw j (by omega)),
      ih (by omega)]
    ring

#print axioms telescope

/-- **(1e) The telescoped window from the lower edge**: if `b·t 0 = P + 1/8` then
`b·t j = P + 1/8 + Σ_{k<j} g_k·b/(8 x_k)`, each `g_k ∈ (0, 2)`. -/
theorem telescope_lower_edge {t x : ℕ → ℝ} {n : ℕ} (hx : ∀ k < n, 0 < x k) (hw : ∀ k < n, InWay (x k) (t k))
    (hs : ∀ k < n, t (k + 1) = nextOpening (x k) (t k)) {b : ℝ} {P : ℤ} (h0 : b * t 0 = (P : ℝ) + 1 / 8) :
    ∀ j ≤ n, b * t j = (P : ℝ) + 1 / 8 + ∑ k ∈ Finset.range j, gap (x k) (t k) * b / (8 * x k) ∧
      ∀ k < j, 0 < gap (x k) (t k) ∧ gap (x k) (t k) < 2 := by
  intro j hj
  refine ⟨by rw [telescope hx hw hs b j hj, h0], fun k hk => ⟨gap_pos (hw k (by omega)), gap_lt_two (hw k (by omega))⟩⟩

#print axioms telescope_lower_edge

/-- The total shift over the first `j ≥ 1` moves is positive and less than `(1/4)·Σ_{k<j} b/x_k`. -/
theorem total_shift_bounds {t x : ℕ → ℝ} {n : ℕ} (hx : ∀ k < n, 0 < x k) (hw : ∀ k < n, InWay (x k) (t k))
    {b : ℝ} (hb : 0 < b) {j : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    0 < ∑ k ∈ Finset.range j, gap (x k) (t k) * b / (8 * x k) ∧
      ∑ k ∈ Finset.range j, gap (x k) (t k) * b / (8 * x k) < (∑ k ∈ Finset.range j, b / x k) / 4 := by
  have hne : (Finset.range j).Nonempty := Finset.nonempty_range_iff.mpr (by omega)
  constructor
  · exact Finset.sum_pos (fun k hk => shift_pos (hx k (by simp at hk; omega)) (hw k (by simp at hk; omega)) hb) hne
  · rw [Finset.sum_div]
    exact Finset.sum_lt_sum_of_nonempty hne
      (fun k hk => shift_lt (hx k (by simp at hk; omega)) (hw k (by simp at hk; omega)) hb)

#print axioms total_shift_bounds

/-! ## (2) Protection -/

/-- **(2a) Protection with an offset.**  A reading that starts at `P + 1/8 + δ` (`δ ≥ 0`) stays strictly inside
`(P + 1/8, P + 7/8)` at `t j` (`1 ≤ j ≤ n`) whenever `Σ_{k<j} b/x_k ≤ 3 − 4δ`.  The lower edge is the case `δ = 0`. -/
theorem protection_offset {t x : ℕ → ℝ} {n : ℕ} (hx : ∀ k < n, 0 < x k) (hw : ∀ k < n, InWay (x k) (t k))
    (hs : ∀ k < n, t (k + 1) = nextOpening (x k) (t k)) {b : ℝ} (hb : 0 < b) {P : ℤ} {δ : ℝ} (hδ : 0 ≤ δ)
    (h0 : b * t 0 = (P : ℝ) + 1 / 8 + δ) {j : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n)
    (hsum : ∑ k ∈ Finset.range j, b / x k ≤ 3 - 4 * δ) :
    (P : ℝ) + 1 / 8 < b * t j ∧ b * t j < (P : ℝ) + 7 / 8 := by
  have ht := telescope hx hw hs b j hjn
  obtain ⟨h1, h2⟩ := total_shift_bounds hx hw hb hj1 hjn
  constructor <;> linarith

#print axioms protection_offset

/-- **(2b) PROTECTION.**  A reading `b > 0` at the lower edge `b·t 0 = P + 1/8`: if `Σ_{k<n} b/x_k ≤ 3` then
`P + 1/8 < b·t j < P + 7/8` for every `1 ≤ j ≤ n`. -/
theorem protection {t x : ℕ → ℝ} {n : ℕ} (hx : ∀ k < n, 0 < x k) (hw : ∀ k < n, InWay (x k) (t k))
    (hs : ∀ k < n, t (k + 1) = nextOpening (x k) (t k)) {b : ℝ} (hb : 0 < b) {P : ℤ}
    (h0 : b * t 0 = (P : ℝ) + 1 / 8) (hsum : ∑ k ∈ Finset.range n, b / x k ≤ 3) :
    ∀ j, 1 ≤ j → j ≤ n → (P : ℝ) + 1 / 8 < b * t j ∧ b * t j < (P : ℝ) + 7 / 8 := by
  intro j hj1 hjn
  have hmono : ∑ k ∈ Finset.range j, b / x k ≤ ∑ k ∈ Finset.range n, b / x k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hjn)
      (fun k hk _ => (div_pos hb (hx k (by simp at hk; omega))).le)
  exact protection_offset hx hw hs hb le_rfl (by rw [h0]; ring) hj1 hjn (by linarith)

#print axioms protection

/-- **(2c)** Under the same hypotheses `b` is not in the way at any `t j`, `j ≤ n` (at `j = 0` it stands exactly at
`1/8`, clear by the closed condition). -/
theorem protection_not_inWay {t x : ℕ → ℝ} {n : ℕ} (hx : ∀ k < n, 0 < x k) (hw : ∀ k < n, InWay (x k) (t k))
    (hs : ∀ k < n, t (k + 1) = nextOpening (x k) (t k)) {b : ℝ} (hb : 0 < b) {P : ℤ}
    (h0 : b * t 0 = (P : ℝ) + 1 / 8) (hsum : ∑ k ∈ Finset.range n, b / x k ≤ 3) :
    ∀ j ≤ n, ¬ InWay b (t j) := by
  intro j hjn
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact not_inWay_of_window (P := P) (by rw [h0]) (by rw [h0]; linarith)
  · obtain ⟨h1, h2⟩ := protection hx hw hs hb h0 hsum j hj hjn
    exact not_inWay_of_window h1.le h2.le

#print axioms protection_not_inWay

/-! ## (3) The contrapositive: a recapture needs `Σ b/x_k > 3` -/

/-- **(3) RECAPTURE.**  If `b` (at the lower edge at `t 0`) is in the way again at `t j`, `j ≤ n`, then
`3 < Σ_{k<j} b/x_k`. -/
theorem recapture_sum_gt {t x : ℕ → ℝ} {n : ℕ} (hx : ∀ k < n, 0 < x k) (hw : ∀ k < n, InWay (x k) (t k))
    (hs : ∀ k < n, t (k + 1) = nextOpening (x k) (t k)) {b : ℝ} (hb : 0 < b) {P : ℤ}
    (h0 : b * t 0 = (P : ℝ) + 1 / 8) {j : ℕ} (hjn : j ≤ n) (hre : InWay b (t j)) :
    3 < ∑ k ∈ Finset.range j, b / x k := by
  by_contra hc
  rw [not_lt] at hc
  exact protection_not_inWay (n := j) (fun k hk => hx k (by omega)) (fun k hk => hw k (by omega))
    (fun k hk => hs k (by omega)) hb h0 hc j le_rfl hre

#print axioms recapture_sum_gt

/-! ## (4) Corollaries -/

/-- **(4a) Three faster setters cannot recapture `b`**: if `n ≤ 3` and every setter has `b ≤ x k`, then `b` is not in
the way at any `t j`, `j ≤ n`. -/
theorem no_recapture_of_faster {t x : ℕ → ℝ} {n : ℕ} (hn : n ≤ 3) (hx : ∀ k < n, 0 < x k)
    (hw : ∀ k < n, InWay (x k) (t k)) (hs : ∀ k < n, t (k + 1) = nextOpening (x k) (t k)) {b : ℝ} (hb : 0 < b)
    (hbx : ∀ k < n, b ≤ x k) {P : ℤ} (h0 : b * t 0 = (P : ℝ) + 1 / 8) :
    ∀ j ≤ n, ¬ InWay b (t j) := by
  apply protection_not_inWay hx hw hs hb h0
  have h1 : ∑ k ∈ Finset.range n, b / x k ≤ ∑ k ∈ Finset.range n, (1 : ℝ) :=
    Finset.sum_le_sum (fun k hk => (div_le_one (hx k (by simpa using hk))).mpr (hbx k (by simpa using hk)))
  have h2 : ∑ k ∈ Finset.range n, (1 : ℝ) = n := by simp
  have h3 : (n : ℝ) ≤ 3 := by exact_mod_cast hn
  linarith

#print axioms no_recapture_of_faster

/-- **(4b) One move by any setter with `3·x ≥ b` cannot recapture `b`** (W1 at `n = 8`, with `x ≥ b` relaxed to
`x ≥ b/3`): `b` at its opening `b·t = P + 1/8`, `x` in the way at `t`. -/
theorem no_recapture_one_move {x t b : ℝ} (hx : 0 < x) (hw : InWay x t) (hb : 0 < b) (hbx : b ≤ 3 * x) {P : ℤ}
    (h0 : b * t = (P : ℝ) + 1 / 8) : ¬ InWay b (nextOpening x t) := by
  have := protection_not_inWay (t := fun k => if k = 0 then t else nextOpening x t) (x := fun _ => x) (n := 1)
    (fun _ _ => hx) (fun k hk => by simp [show k = 0 by omega]; exact hw)
    (fun k hk => by simp [show k = 0 by omega]) hb (by simpa using h0)
    (by simp; rw [div_le_iff₀ hx]; linarith) 1 le_rfl
  simpa using this

#print axioms no_recapture_one_move

/-! ### Relation to the manuscripts' word rules ([reasoned], not formalised as an implication)

`WordRules.no_return_after_faster` (W1, every `n ≥ 4`): a runner at its lap-`P` opening is not in the way straight
after a move set by a runner at least as fast.  `FasterMoves.no_return_after_few_faster`: not in the way after `m ≤ g`
moves set at laps `≥ P + 1`, when `n ≥ 2g + 2`; at `n = 8`, `g = 3`.

The additive argument here, run at a general threshold `1/n` [reasoned], reads: each move shifts `b` by
`g·b/(n x) < 2b/(n x)` laps and the window above the lower edge is `1 − 2/n`, so the reading is protected while
`Σ b/x_k ≤ (n − 2)/2`.  With every `b/x_k ≤ 1` (faster setters) that is `m ≤ (n − 2)/2`, i.e. `n ≥ 2m + 2`: exactly the
threshold of `no_return_after_few_faster`, reached by a different route (laps instead of lap factors).  At `n = 8` it
gives `(n − 2)/2 = 3`, the owner's `3`.  What is proved here, at `n = 8`, is `no_recapture_of_faster` (three faster
setters) and `no_recapture_one_move` (one setter with `x ≥ b/3`, which contains W1 at `n = 8`).  The hypotheses differ in
kind: the existing lemma assumes the setters' laps are `≥ P + 1`; here the assumption is on the ratios `b/x_k` only, and
setters slower than `b` are allowed as long as the weighted sum stays `≤ 3` (e.g. one setter with `x = b/3`, or a
setter with `x = b/2` followed by one with `x ≥ b`).  Neither hypothesis set is shown here to imply the other.

The exact evidence cited in the brief (`experiments/n8/protection_bound_check_v1.py`, not re-run here) has its smallest
recapture sum at `216/65 > 3`, consistent with (3); the gap between `3` and `216/65` is the gap between the worst case
`g → 2` used in the proof and the gaps the cascade actually produces.  No claim about that gap is made here. -/

/-! ## (5) The owner's ratio line is an algebra slip -/

/-- **(5a) The correct equivalence**: for `b, S > 0`, `1/3 ≤ b/S ↔ S ≤ 3b`. -/
theorem third_iff {b S : ℝ} (hS : 0 < S) : (1 / 3 : ℝ) ≤ b / S ↔ S ≤ 3 * b := by
  rw [le_div_iff₀ hS]
  constructor <;> intro h <;> linarith

#print axioms third_iff

/-- **(5b) The owner's left side does not depend on `b`**: `b/(b/c + b/d + b/e) = 1/(1/c + 1/d + 1/e)`.  So it cannot
be equivalent to the dimensionless protection condition `b/c + b/d + b/e ≤ 3`, which does depend on `b`. -/
theorem owner_ratio_eq {b c d e : ℝ} (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) :
    b / (b / c + b / d + b / e) = 1 / (1 / c + 1 / d + 1 / e) := by
  field_simp

#print axioms owner_ratio_eq

/-- **(5c) Counterexample to the owner's equivalence `1/3 ≤ b/(b/c+b/d+b/e) ↔ b/c+b/d+b/e ≤ 3`**, both directions,
exact.  Forward fails at `b = 2, c = d = e = 1` (`S = 6`, `b/S = 1/3`, but `6 > 3`).  Backward fails at `b = 1/4`,
`c = d = e = 1/2` (`S = 3/2 ≤ 3`, but `b/S = 1/6 < 1/3`). -/
theorem owner_iff_fails :
    ¬ (∀ b c d e : ℝ, 0 < b → 0 < c → 0 < d → 0 < e →
      ((1 / 3 : ℝ) ≤ b / (b / c + b / d + b / e) → b / c + b / d + b / e ≤ 3)) ∧
    ¬ (∀ b c d e : ℝ, 0 < b → 0 < c → 0 < d → 0 < e →
      (b / c + b / d + b / e ≤ 3 → (1 / 3 : ℝ) ≤ b / (b / c + b / d + b / e))) := by
  constructor
  · intro h
    have := h 2 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at this
  · intro h
    have := h (1 / 4) (1 / 2) (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
    norm_num at this

#print axioms owner_iff_fails

/-! Remark on the owner's per-step shift.  The owner writes the shift of `b` across a move set by `s_k` as `b/(8 s_k)`
laps.  By `one_move_shift` the shift is `g_k·b/(8 s_k)` with `g_k ∈ (0, 2)`; the owner's expression is the case
`g_k = 1`.  With `g_k = 1` the window `3/4` would give the threshold `Σ b/s_k < 6`; the threshold `3` is the worst case
`g_k → 2` (`shift_lt`), which is what `protection` uses.  So the owner's `3` is right for the bound, and the per-step
expression is the typical case, not the bound. -/

/-! ## (6) The limit: the lower edge is essential

`protection` concerns a reading that starts at the lower edge `P + 1/8` (a setter at its own opening).  A reading
clear elsewhere in its window, at `P + 1/8 + δ` with `δ ∈ (0, 3/4]`, has only `3/4 − δ` laps of margin; by
`protection_offset` it is protected while `Σ b/x_k ≤ 3 − 4δ`, and a shift smaller than the lower-edge threshold
recaptures it.  Why: the shift `g·b/(8x)` is positive and depends on the speeds only, not on where `b` stands; what
the lower edge supplies is the full margin `3/4`.

Exact example (`offset_recapture_example`): disparities `{1, 17/20}`, state `t = 1`.  The runner `1` reads `1` (in the
way, lap 1); `17/20` reads `17/20 = 0 + 1/8 + 29/40` (clear, `δ = 29/40`).  The cascade moves to
`nextOpening 1 1 = 9/8` (one setter, `g = 1`); `17/20` now reads `153/160`, within `7/160 < 1/8` of `1`: in the way.
Here `Σ b/x = 17/20 ≤ 3`, yet `b` is recaptured; the offset threshold is `3 − 4·29/40 = 1/10 < 17/20`.  This is a
single move on a two-element disparity set, not a full eight-runner arrangement. -/

/-- **(6) Exact example: a reading clear but not at its lower edge is recaptured with `Σ b/x = 17/20 ≤ 3`.** -/
theorem offset_recapture_example :
    IsMove ({1, 17 / 20} : Finset ℝ) 1 (9 / 8) ∧ nextOpening 1 1 = 9 / 8 ∧
    ¬ InWay (17 / 20) 1 ∧ InWay (17 / 20) (9 / 8) ∧ (17 / 20 : ℝ) / 1 ≤ 3 := by
  have hw1 : InWay 1 1 := by
    unfold InWay
    have := distInt_le ((1 : ℝ) * 1) 1
    norm_num at this ⊢
    linarith
  have hno : nextOpening 1 1 = 9 / 8 := by
    rw [nextOpening_eq (k := 1) (by norm_num)]
    norm_num
  have hclear : ¬ InWay (17 / 20) 1 :=
    not_inWay_of_window (P := 0) (by norm_num) (by norm_num)
  refine ⟨?_, hno, hclear, ?_, by norm_num⟩
  · refine Or.inr ⟨1, by simp, hw1, hno.symm, ?_⟩
    intro d' hd' hw'
    rcases Finset.mem_insert.mp hd' with rfl | hd'
    · rw [hno]
    · rw [Finset.mem_singleton.mp hd'] at hw'
      exact absurd hw' hclear
  · unfold InWay
    have := distInt_le ((17 / 20 : ℝ) * (9 / 8)) 1
    norm_num at this ⊢
    linarith

#print axioms offset_recapture_example

/-! ## Connection to the cascade: every forward step of a cascade sequence supplies its setter -/

/-- A forward step of `IsMove` is set by some runner of `ds` in the way, landing at its next opening. -/
theorem forward_setter {ds : Finset ℝ} {t t' : ℝ} (hm : IsMove ds t t') (hne : t' ≠ t) :
    ∃ x ∈ ds, InWay x t ∧ t' = nextOpening x t := by
  rcases hm with ⟨_, h⟩ | ⟨x, hx, hw, h, _⟩
  · exact absurd h hne
  · exact ⟨x, hx, hw, h⟩

#print axioms forward_setter

/-- Along a cascade sequence whose first `n` steps are forward, setters `x k ∈ ds` exist with the hypotheses used
above. -/
theorem exists_setters {ds : Finset ℝ} {seq : ℕ → ℝ} {n : ℕ} (hmv : ∀ k, IsMove ds (seq k) (seq (k + 1)))
    (hne : ∀ k < n, seq (k + 1) ≠ seq k) :
    ∃ x : ℕ → ℝ, ∀ k < n, x k ∈ ds ∧ InWay (x k) (seq k) ∧ seq (k + 1) = nextOpening (x k) (seq k) := by
  choose! x hx using fun k (hk : k < n) => forward_setter (hmv k) (hne k hk)
  exact ⟨x, hx⟩

#print axioms exists_setters

/-- **Protection along a cascade sequence**: `seq` a cascade sequence over positive disparities `ds`, its first `n`
steps forward with setters `x k`; a reading `b > 0` at the lower edge at `seq 0` with `Σ_{k<n} b/x_k ≤ 3` is not in the
way at any `seq j`, `j ≤ n`. -/
theorem protection_cascade {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {seq x : ℕ → ℝ} {n : ℕ}
    (hset : ∀ k < n, x k ∈ ds ∧ InWay (x k) (seq k) ∧ seq (k + 1) = nextOpening (x k) (seq k))
    {b : ℝ} (hb : 0 < b) {P : ℤ} (h0 : b * seq 0 = (P : ℝ) + 1 / 8)
    (hsum : ∑ k ∈ Finset.range n, b / x k ≤ 3) : ∀ j ≤ n, ¬ InWay b (seq j) :=
  protection_not_inWay (fun k hk => hpos _ (hset k hk).1) (fun k hk => (hset k hk).2.1)
    (fun k hk => (hset k hk).2.2) hb h0 hsum

#print axioms protection_cascade

end Protection

end Fresh
