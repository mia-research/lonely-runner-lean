import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.Dilation
import Fresh.ChainLaws
import Fresh.Ladder5

/-!
# The law of position: windows entered anew, the two-step law, the lap budget (Task BA)

Written 2026-10-09.  Imports `Mathlib`, `Fresh.Framework` and the Fresh modules named in the task.  Nothing is imported from
the existing `LonelyRunner` repo.  Exact reals only; every disparity is positive (no runner is stationary); no floats.

## The picture behind the statements (reasoned, used only as commentary here)

In the coordinate `R = 8 t`, reading `x` has a *window* `((8l-1)/x, (8l+1)/x)` for each lap `l`: the instants at which it is in
the way.  A move goes to the largest right end among the windows that contain the current instant.  The cascade is therefore
a greedy walk over a union of windows, and a landing is the right end of one window.

## What is proved here

* (1) `entered_anew` [L].  **Every window that contains a landing began at or after the previous instant.**  If `IsMove ds t t'`
  and `y ∈ ds` is in the way at `t'` on lap `l`, then `y·t ≤ l - 1/8`: at `t` it had not yet entered that window.  This is the
  maximality clause of `IsMove` read as an inequality between laps and readings; nothing else is used (no ordering of the
  readings, no base `m`, no lower bound on laps).
* (2) `two_step_lower` [L].  If `x` sets the move at `s+1`, then `seq (s+2) - seq s ≥ 1/(4x)`.  Together with
  `Ladder5.incr_setter` (`seq (s+2) - seq (s+1) < 1/(4x)`) every window length lies between one jump and two consecutive jumps:
  `d_s < 2/x_s ≤ d_s + d_{s-1}` in `R` units.
* (3) `lap_identity` [L].  A reading set at `n` and again at `k` satisfies `x (seq (k+1) - seq (n+1)) = lap_k - lap_n`: the
  elapsed time between two landings of the same reading is a whole number of its laps.  This is the lattice condition that the
  additive budget does not see.
* (4) `lap_budget` [L].  With `j = lap_k - lap_n`, the intermediate setters satisfy `4 j - 1 < ∑ x / w s`.  For `j = 1` this is
  `Ladder5.budget_sum`'s constant `3`; for `j ≥ 2` it is larger.  `lap_diff_pos` shows `j ≥ 1`, and `budget_of_reset` recovers
  `3 < ∑ x / w s` for a reading that is set again.

## What is NOT proved here (kept as commentary, not as statements)

No existence statement; no statement about which words occur; the exclusion of `v t u v` is NOT proved (it is false as a local
statement: see `experiments/n8/law_of_position_v1.out`, section 4, exact counterexamples at lap 15).

Provenance (existing declarations whose argument was read and understood, nothing copied): `Cascade.inWay_until_opening`
(for the shape of the no-overshoot argument), `Ladder5.budget_sum`, `Ladder5.sum_incr`, `Ladder5.incr_setter`,
`Dilation.setter_reading`.
-/

open Classical

namespace Fresh

namespace LawOfPosition

open Cascade Dilation ChainLaws Ladder5

/-! ## (1) Every window containing a landing was entered during the move -/

/-- **Entered anew** [L].  If `IsMove ds t t'` and a member `y` of `ds` is in the way at `t'`, on lap `l = lap y t'`, then
`y · t ≤ l - 1/8`.  Equivalently: no window that contains the landing contains the previous instant.
Hypotheses: `hpos` (positive disparities; REQUIRED: used to compare `y t` with `y t'` and to divide by `y`), the move `hm`,
`y ∈ ds` (REQUIRED: the maximality clause only speaks about members of `ds`), `InWay y t'`.  NOT REQUIRED: `0 < t`, any ordering
of the readings, a base `m`, `seq 0 = 1/(8m)`, integrality. -/
theorem entered_anew {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {t t' : ℝ} (hm : IsMove ds t t')
    {y : ℝ} (hy : y ∈ ds) (hw : InWay y t') : y * t ≤ (lap y t' : ℝ) - 1 / 8 := by
  have hy0 := hpos y hy
  have htt : t ≤ t' := le_of_isMove hpos hm
  rcases hm with ⟨hall, h⟩ | ⟨d, hd, hwd, hdt, hmax⟩
  · subst h
    exact absurd hw (hall y hy)
  · by_contra hcon
    push Not at hcon
    have hk := abs_lt.mp (abs_sub_lap_lt hw)
    have hmono : y * t ≤ y * t' := mul_le_mul_of_nonneg_left htt hy0.le
    have hnear : |y * t - ((lap y t' : ℤ) : ℝ)| < 1 / 8 := by
      rw [abs_lt]
      constructor <;> linarith
    have hwt : InWay y t := by
      unfold InWay
      exact lt_of_le_of_lt (distInt_le (y * t) (lap y t')) hnear
    have hle := hmax y hy hwt
    rw [nextOpening_eq hnear, div_le_iff₀ hy0] at hle
    linarith

#print axioms entered_anew

/-- Contrapositive form: a reading that is in the way at both `t` and `t'` (`t'` the landing) is on a strictly higher lap at
`t'` [L]: it left its old window past `+1/8` and entered a later one. -/
theorem lap_lt_of_inWay_both {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {t t' : ℝ} (hm : IsMove ds t t')
    {y : ℝ} (hy : y ∈ ds) (hw : InWay y t') (hw0 : InWay y t) : lap y t < lap y t' := by
  have h := entered_anew hpos hm hy hw
  have h1 := abs_lt.mp (abs_sub_lap_lt hw0)
  have h2 : (lap y t : ℝ) < (lap y t' : ℝ) := by linarith
  exact_mod_cast h2

#print axioms lap_lt_of_inWay_both

/-! ## (2) The two-step law -/

/-- **The two-step law, lower half** [L].  If `x` sets the move at `s+1` then `seq (s+2) - seq s ≥ 1/(4x)`: the window of the
setter at `s+1` has length `1/(4x)` (in `t` units), it was entered after `seq s` (`entered_anew`) and left at `seq (s+2)`.
Upper half: `Ladder5.incr_setter`, `seq (s+2) - seq (s+1) < 1/(4x)`. -/
theorem two_step_lower {ds : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ ds, 0 < d)
    (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) {s : ℕ} {x : ℝ} (hx : IsSetterAt ds seq (s + 1) x) :
    1 / (4 * x) ≤ seq (s + 2) - seq s := by
  have hx0 := hpos x hx.1
  have hanew := entered_anew hpos (hmv s) hx.1 hx.2.1
  have hland : x * seq (s + 2) = (lap x (seq (s + 1)) : ℝ) + 1 / 8 := by
    have e : seq (s + 2) = nextOpening x (seq (s + 1)) := hx.2.2
    rw [e]
    exact setter_reading hx0 hx.2.1
  have h4 : 1 / 4 ≤ x * (seq (s + 2) - seq s) := by nlinarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith

#print axioms two_step_lower

/-- **The two-step law, both halves** [L]: the setter at `s+1` has `1/(4x)` strictly above the last jump and at most the sum
of the last two jumps. -/
theorem two_step_law {ds : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ ds, 0 < d)
    (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) {s : ℕ} {x : ℝ} (hx : IsSetterAt ds seq (s + 1) x) :
    seq (s + 2) - seq (s + 1) < 1 / (4 * x) ∧ 1 / (4 * x) ≤ (seq (s + 2) - seq (s + 1)) + (seq (s + 1) - seq s) := by
  refine ⟨(incr_setter hpos hx).2, ?_⟩
  have := two_step_lower hpos hmv hx
  linarith

#print axioms two_step_law

/-! ## (3) The lattice identity and the lap budget -/

/-- **Lattice identity** [L].  A reading `x` set at `n` and again at `k > n` satisfies
`x · (seq (k+1) - seq (n+1)) = lap x (seq k) - lap x (seq n)`: the time between its two landings is a whole number of its laps.
Hypotheses: `0 < x` (REQUIRED for `setter_reading`), the two settings.  NOT REQUIRED: `n < k` (the identity is an equation of
the two landings; for `k = n` both sides are `0`), the cascade moves. -/
theorem lap_identity {ds : Finset ℝ} {seq : ℕ → ℝ} {n k : ℕ} {x : ℝ} (hx0 : 0 < x) (hn : IsSetterAt ds seq n x)
    (hk : IsSetterAt ds seq k x) :
    x * (seq (k + 1) - seq (n + 1)) = (lap x (seq k) : ℝ) - (lap x (seq n) : ℝ) := by
  have e1 : x * seq (n + 1) = (lap x (seq n) : ℝ) + 1 / 8 := by
    rw [hn.2.2]; exact setter_reading hx0 hn.2.1
  have e2 : x * seq (k + 1) = (lap x (seq k) : ℝ) + 1 / 8 := by
    rw [hk.2.2]; exact setter_reading hx0 hk.2.1
  nlinarith

#print axioms lap_identity

/-- **The lap difference of two settings of one reading is positive** [L]: `lap x (seq n) < lap x (seq k)` for `n < k`. -/
theorem lap_diff_pos {ds : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ ds, 0 < d)
    (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) {n k : ℕ} (hnk : n < k) {x : ℝ} (hn : IsSetterAt ds seq n x)
    (hk : IsSetterAt ds seq k x) : lap x (seq n) < lap x (seq k) := by
  have hx0 := hpos x hn.1
  have h1 : seq (n + 1) ≤ seq k := seq_mono hpos hmv (Nat.succ_le_of_lt hnk)
  have h2 : seq k < seq (k + 1) := by
    have := (incr_setter hpos hk).1
    linarith
  have hid := lap_identity hx0 hn hk
  have hpos' : 0 < x * (seq (k + 1) - seq (n + 1)) := mul_pos hx0 (by linarith)
  have : (lap x (seq n) : ℝ) < (lap x (seq k) : ℝ) := by linarith
  exact_mod_cast this

#print axioms lap_diff_pos

/-- **The lap budget** [L].  `x` set at `n` and again at `k > n`, `w s` the setter of the move at `s` for `n < s < k`.  With
`j = lap x (seq k) - lap x (seq n)` (a positive integer, `lap_diff_pos`):
`4 j - 1 < ∑_{s=n+1}^{k-1} x / w s`.  For `j = 1` the constant is `3`, that of `Ladder5.budget_sum`; for `j ≥ 2` it is larger,
which the additive budget does not see.  Hypotheses: positive disparities (REQUIRED: division), `x` set at BOTH `n` and `k` (REQUIRED as stated: the identity
`lap_identity` needs the landing reading at `k+1`; with `x` only in the way at `k` the sharper constant is not available), and the
setters `w s` of the moves between.  NOT REQUIRED (the proof does not use them; the compiler flags the cascade-move hypothesis as
unused and it is removed from the statement): `∀ n, IsMove E (seq n) (seq (n+1))`, any ordering of the readings, a base `m`,
`0 < seq 0`, integrality of the readings.  `lap_diff_pos` (which gives `j ≥ 1`) does use the moves. -/
theorem lap_budget {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d)
    {n k : ℕ} (hnk : n < k) {x : ℝ} (hn : IsSetterAt E seq n x)
    (hk : IsSetterAt E seq k x) (w : ℕ → ℝ) (hws : ∀ s, n < s → s < k → IsSetterAt E seq s (w s)) :
    4 * ((lap x (seq k) : ℝ) - (lap x (seq n) : ℝ)) - 1 < ∑ s ∈ Finset.Ico (n + 1) k, x / w s := by
  have hx0 := hpos x hn.1
  have hid := lap_identity hx0 hn hk
  have hsum := sum_incr hpos (n + 1) w (k - (n + 1)) (by
    intro s h1 h2
    exact hws s (by omega) (by omega))
  rw [show n + 1 + (k - (n + 1)) = k by omega] at hsum
  have hlast := (incr_setter hpos hk).2
  have hcongr : x * ∑ s ∈ Finset.Ico (n + 1) k, 1 / (4 * w s) = (∑ s ∈ Finset.Ico (n + 1) k, x / w s) / 4 := by
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hs' := Finset.mem_Ico.mp hs
    have hw0 := hpos _ (hws s (by omega) (by omega)).1
    field_simp
  have htot : seq (k + 1) - seq (n + 1) < ∑ s ∈ Finset.Ico (n + 1) k, 1 / (4 * w s) + 1 / (4 * x) := by
    linarith
  have hmul : x * (seq (k + 1) - seq (n + 1)) <
      x * (∑ s ∈ Finset.Ico (n + 1) k, 1 / (4 * w s) + 1 / (4 * x)) := mul_lt_mul_of_pos_left htot hx0
  have e : x * (∑ s ∈ Finset.Ico (n + 1) k, 1 / (4 * w s) + 1 / (4 * x)) =
      (∑ s ∈ Finset.Ico (n + 1) k, x / w s) / 4 + 1 / 4 := by
    rw [mul_add, hcongr]
    field_simp
  rw [hid, e] at hmul
  linarith

#print axioms lap_budget

/-- **A reading that is set again passes more than `3`** [L]: `3 < ∑ x / w s`.  The lap difference is an integer `≥ 1`
(`lap_diff_pos`), so `4 j - 1 ≥ 3` and `lap_budget` gives the additive budget law of `Ladder5.budget_sum` for this case, by a
different proof (lattice identity instead of the return inequality). -/
theorem budget_of_reset {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) {n k : ℕ} (hnk : n < k) {x : ℝ} (hn : IsSetterAt E seq n x)
    (hk : IsSetterAt E seq k x) (w : ℕ → ℝ) (hws : ∀ s, n < s → s < k → IsSetterAt E seq s (w s)) :
    3 < ∑ s ∈ Finset.Ico (n + 1) k, x / w s := by
  have h := lap_budget hpos hnk hn hk w hws
  have hj := lap_diff_pos hpos hmv hnk hn hk
  have hj' : (lap x (seq n) : ℝ) + 1 ≤ (lap x (seq k) : ℝ) := by
    have : lap x (seq n) + 1 ≤ lap x (seq k) := by omega
    exact_mod_cast this
  linarith

#print axioms budget_of_reset

end LawOfPosition

end Fresh
