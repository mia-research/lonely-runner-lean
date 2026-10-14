import Mathlib
import Fresh.Framework
import Fresh.Cascade

/-!
# One cascade move is one dilation (Task G; v9 sections 6 and 7)

Built on `Fresh/Framework.lean` (`distInt`, `InWay`, `nextOpening`, `IsMove`) and `Fresh/Cascade.lean` (its basic
facts on `distInt`, `nextOpening_eq`, `lt_nextOpening`, `not_inWay_at_nextOpening`, `start_le_seq`).  Nothing is
imported from the existing `LonelyRunner` repo; every proof below was written for this file.  Exact reals only; every
disparity used is positive (no runner is stationary).

Setting: a runner of disparity `x > 0` in the way at an instant `t > 0`; `N = lap x t` the integer nearest `x·t`
(so `|x·t − N| < 1/8`); `g = gap x t = 8N + 1 − 8·x·t`; `t' = nextOpening x t`.

Contents.
* (1) `0 < g < 2`, `t' = t + g/(8x)`, `x·t' = N + 1/8` (the setter reads exactly `8N + 1` eighths).
* (2) For every disparity `d`: `8·d·t' = 8·d·t + g·d/x` (every other reading shifts by `g·d/x` eighths).
* (3) `t'/t = (8N + 1)/(8·x·t)`, `1 < t'/t`, and for `N ≥ 1`, `t'/t < (8N + 1)/(8N − 1) ≤ 9/7`.
* (4) From the bound `t ≥ 1/(8m)`, `m` a positive lower bound of the disparities, every runner in the way has `N ≥ 1`.
* (5) Along a cascade sequence from `1/(8m)`: each step fixes or multiplies the instant by less than `9/7`; the setter
  of a forward move is not in the way at the instant it set, so consecutive forward moves have different setters.
  No bound on the number of moves is stated (rule 7): the factor bound is a tool, not a result.
* (6) The link rule (record L6): after a move to the exit of runner `x`'s lap-`j` zone, a slower runner in the way there
  is on a lap `≤ j`, a faster one on a lap `≥ j + 1`; a runner of the same disparity is not in the way.
  Stated both for one move and for consecutive forward moves of a cascade sequence.

Provenance (the existing declaration each theorem corresponds to; the argument was read and understood, not copied):
`LRC/Cascade/Iteration.lean` `dilation_factor`, `one_lt_dilation_factor`, `setter_reading_at_nextScale`,
`other_reading_shift`, `shift_coeff_mem`, `nextOpening_at_scale` (there in the scale coordinate `D` with threshold
`1/n`; here directly in the instant `t` at `n = 8`); `LRC/Spec/ZoneLinkN.lean` `slower_lap_le`, `faster_lap_lt`,
`equal_not_inZone` (there for an abstract zone exit `(8j+1)/ρ_x` in `R`-coordinates; here for the cascade's own
`InWay` and `nextOpening`).  The factor bound `9/7` is record L5 (v9 section 7), proved there by hand.
-/

open Classical

namespace Fresh

namespace Dilation

open Cascade

/-! ## The lap and the gap -/

/-- The lap of runner `d` at `t`: the integer nearest `d·t` (the same `round` as in `distInt`). -/
noncomputable def lap (d t : ℝ) : ℤ := round (d * t)

/-- The gap of the setter `x` at `t`: how far, in eighths, its reading `8·x·t` sits below `8N + 1`. -/
noncomputable def gap (x t : ℝ) : ℝ := 8 * (lap x t : ℝ) + 1 - 8 * x * t

/-- In the way means within `1/8` of its lap. -/
theorem abs_sub_lap_lt {x t : ℝ} (h : InWay x t) : |x * t - (lap x t : ℝ)| < 1 / 8 := h

#print axioms abs_sub_lap_lt

/-- Conversely, within `1/8` of some integer `k` means in the way, and `k` is the lap. -/
theorem lap_eq_of_near {x t : ℝ} {k : ℤ} (hk : |x * t - k| < 1 / 8) : lap x t = k := by
  unfold lap
  rw [round_eq, Int.floor_eq_iff]
  have := abs_lt.mp hk
  constructor <;> linarith

#print axioms lap_eq_of_near

/-! ## (1) The gap, the next opening, and the setter's landing reading -/

/-- The next opening of a runner in the way is `(N + 1/8)/x`, `N` its lap. -/
theorem nextOpening_eq_lap {x t : ℝ} (h : InWay x t) :
    nextOpening x t = ((lap x t : ℝ) + 1 / 8) / x :=
  nextOpening_eq (abs_sub_lap_lt h)

#print axioms nextOpening_eq_lap

/-- **(1a) The gap is positive.** -/
theorem gap_pos {x t : ℝ} (h : InWay x t) : 0 < gap x t := by
  have := abs_lt.mp (abs_sub_lap_lt h)
  unfold gap
  linarith

#print axioms gap_pos

/-- **(1b) The gap is less than two.** -/
theorem gap_lt_two {x t : ℝ} (h : InWay x t) : gap x t < 2 := by
  have := abs_lt.mp (abs_sub_lap_lt h)
  unfold gap
  linarith

#print axioms gap_lt_two

/-- **(1c) The move advances the instant by `g/(8x)`.** -/
theorem nextOpening_eq_add_gap {x t : ℝ} (hx : 0 < x) (h : InWay x t) :
    nextOpening x t = t + gap x t / (8 * x) := by
  rw [nextOpening_eq_lap h]
  unfold gap
  field_simp
  ring

#print axioms nextOpening_eq_add_gap

/-- **(1d) The setter lands exactly one eighth past its lap line**: `x·t' = N + 1/8`. -/
theorem setter_reading {x t : ℝ} (hx : 0 < x) (h : InWay x t) :
    x * nextOpening x t = (lap x t : ℝ) + 1 / 8 := by
  rw [nextOpening_eq_lap h]
  field_simp

#print axioms setter_reading

/-- **(1e) In eighths, the setter reads exactly `8N + 1`.** -/
theorem setter_reading_eighths {x t : ℝ} (hx : 0 < x) (h : InWay x t) :
    8 * x * nextOpening x t = 8 * (lap x t : ℝ) + 1 := by
  rw [mul_assoc, setter_reading hx h]
  ring

#print axioms setter_reading_eighths

/-! ## (2) Every other reading shifts by `g·d/x` eighths -/

/-- **(2) Every reading, in eighths, moves by `g·d/x`.**  The coefficient `g ∈ (0, 2)` is the setter's alone; the
ratio `d/x` is fixed by the speeds.  (Provenance: `other_reading_shift`.) -/
theorem reading_shift {x t : ℝ} (hx : 0 < x) (h : InWay x t) (d : ℝ) :
    8 * d * nextOpening x t = 8 * d * t + gap x t * d / x := by
  rw [nextOpening_eq_add_gap hx h]
  field_simp

#print axioms reading_shift

/-! ## (3) The dilation factor -/

/-- **(3a) The move is one dilation by `λ = (8N + 1)/(8·x·t)`.**  (Provenance: `dilation_factor`.) -/
theorem dilation_eq {x t : ℝ} (hx : 0 < x) (ht : 0 < t) (h : InWay x t) :
    nextOpening x t / t = (8 * (lap x t : ℝ) + 1) / (8 * x * t) := by
  rw [nextOpening_eq_lap h]
  field_simp

#print axioms dilation_eq

/-- Every reading is multiplied by the same factor: `d·t' = λ·(d·t)`. -/
theorem reading_dilation {x t : ℝ} (ht : 0 < t) (d : ℝ) :
    d * nextOpening x t = (nextOpening x t / t) * (d * t) := by
  field_simp

#print axioms reading_dilation

/-- **(3b) The factor exceeds one.**  (Provenance: `one_lt_dilation_factor`.) -/
theorem one_lt_dilation {x t : ℝ} (hx : 0 < x) (ht : 0 < t) (h : InWay x t) :
    1 < nextOpening x t / t := by
  rw [one_lt_div ht]
  exact lt_nextOpening hx h

#print axioms one_lt_dilation

/-- **(3c) For `N ≥ 1`, the factor is below `(8N + 1)/(8N − 1)`.** -/
theorem dilation_lt {x t : ℝ} (hx : 0 < x) (ht : 0 < t) (h : InWay x t) (hN : 1 ≤ lap x t) :
    nextOpening x t / t < (8 * (lap x t : ℝ) + 1) / (8 * (lap x t : ℝ) - 1) := by
  have hb := abs_lt.mp (abs_sub_lap_lt h)
  have hN' : (1 : ℝ) ≤ (lap x t : ℝ) := by exact_mod_cast hN
  have hxt : 0 < x * t := mul_pos hx ht
  rw [dilation_eq hx ht h]
  apply div_lt_div_of_pos_left (by linarith) (by linarith)
  linarith

#print axioms dilation_lt

/-- `(8N + 1)/(8N − 1) ≤ 9/7` for every `N ≥ 1` (equality at `N = 1`). -/
theorem ratio_le_nine_sevenths {N : ℝ} (hN : 1 ≤ N) : (8 * N + 1) / (8 * N - 1) ≤ 9 / 7 := by
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

#print axioms ratio_le_nine_sevenths

/-- **(3d) For `N ≥ 1`, the factor is below `9/7`.** -/
theorem dilation_lt_nine_sevenths {x t : ℝ} (hx : 0 < x) (ht : 0 < t) (h : InWay x t)
    (hN : 1 ≤ lap x t) : nextOpening x t / t < 9 / 7 :=
  lt_of_lt_of_le (dilation_lt hx ht h hN) (ratio_le_nine_sevenths (by exact_mod_cast hN))

#print axioms dilation_lt_nine_sevenths

/-! ## (4) From the bound, every runner in the way is past its first lap -/

/-- **(4) `d_min` never blocks at its own scale**: if `t ≥ 1/(8m)` and `0 < m ≤ x`, a runner `x` in the way at `t`
has lap `N ≥ 1` (its reading `x·t ≥ 1/8` cannot be within `1/8` of `0`). -/
theorem one_le_lap_of_bound {m x t : ℝ} (hm : 0 < m) (hmx : m ≤ x) (ht : 1 / (8 * m) ≤ t)
    (h : InWay x t) : 1 ≤ lap x t := by
  have hb := abs_lt.mp (abs_sub_lap_lt h)
  have h8 : 1 / 8 ≤ m * t := by
    rw [div_le_iff₀ (by positivity)] at ht
    linarith
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have hxt : m * t ≤ x * t := mul_le_mul_of_nonneg_right hmx ht0.le
  have : (0 : ℝ) < (lap x t : ℝ) := by linarith
  exact_mod_cast this

#print axioms one_le_lap_of_bound

/-! ## (5) Consequences for cascade sequences -/

/-- **(5a) One move from at or above the bound fixes `t` or multiplies it by less than `9/7`.** -/
theorem isMove_fix_or_ratio_lt {ds : Finset ℝ} {m t t' : ℝ} (hm : 0 < m) (hlow : ∀ d ∈ ds, m ≤ d)
    (ht : 1 / (8 * m) ≤ t) (hmv : IsMove ds t t') : t' = t ∨ t' / t < 9 / 7 := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  rcases hmv with ⟨_, rfl⟩ | ⟨x, hx, hw, rfl, _⟩
  · exact Or.inl rfl
  · exact Or.inr (dilation_lt_nine_sevenths (lt_of_lt_of_le hm (hlow x hx)) ht0 hw
      (one_le_lap_of_bound hm (hlow x hx) ht hw))

#print axioms isMove_fix_or_ratio_lt

/-- **(5b) Along a cascade sequence from `1/(8m)`**, every step fixes the instant or multiplies it by less than
`9/7`.  (Record L5, first clause.) -/
theorem seq_fix_or_ratio_lt {ds : Finset ℝ} {m : ℝ} (hm : 0 < m) (hlow : ∀ d ∈ ds, m ≤ d)
    {seq : ℕ → ℝ} (h0 : seq 0 = 1 / (8 * m)) (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) (n : ℕ) :
    seq (n + 1) = seq n ∨ seq (n + 1) / seq n < 9 / 7 := by
  have hpos : ∀ d ∈ ds, 0 < d := fun d hd => lt_of_lt_of_le hm (hlow d hd)
  have hge : 1 / (8 * m) ≤ seq n := h0 ▸ start_le_seq hpos hmv n
  exact isMove_fix_or_ratio_lt hm hlow hge (hmv n)

#print axioms seq_fix_or_ratio_lt

/-- **(5c) The setter of a move is not in the way at the instant it set.** -/
theorem setter_not_inWay {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {x t t' : ℝ} (hx : x ∈ ds)
    (hset : t' = nextOpening x t) (_hmv : IsMove ds t t') : ¬ InWay x t' := by
  rw [hset]
  exact not_inWay_at_nextOpening (hpos x hx)

#print axioms setter_not_inWay

/-- **(5d) Consecutive forward moves have different setters**: if `x` sets the move `t → t'` and `y` sets the move
`t' → t''` (each in the way at its start and landing at its own next opening), then `y ≠ x`. -/
theorem consecutive_setters_ne {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {x y t t' : ℝ} (hx : x ∈ ds)
    (hset : t' = nextOpening x t) (hy : InWay y t') : y ≠ x := by
  rintro rfl
  rw [hset] at hy
  exact not_inWay_at_nextOpening (hpos y hx) hy

#print axioms consecutive_setters_ne

/-- A runner of the same disparity as the setter (a duplicate value is the same runner in a `Finset`) is never in the
way at the setter's opening; the record's `equal_not_inZone`. -/
theorem equal_not_inWay {x t : ℝ} (hx : 0 < x) : ¬ InWay x (nextOpening x t) :=
  not_inWay_at_nextOpening hx

#print axioms equal_not_inWay

/-! ## (6) The link rule (record L6)

After a move set by `x` on lap `j = lap x t`, the cascade stands at the exit `t' = (j + 1/8)/x` of `x`'s lap-`j` zone.
A runner `y` in the way there is within `1/8` of its lap `lap y t'`.  Since `x·t' = j + 1/8` exactly, a slower `y` has
`y·t' < j + 1/8`, so its lap is `< j + 1/4`, hence `≤ j`; a faster `y` has `y·t' > j + 1/8`, so its lap is `> j`. -/

/-- The setter's next opening is positive when it starts at a positive instant. -/
theorem nextOpening_pos {x t : ℝ} (hx : 0 < x) (ht : 0 < t) (h : InWay x t) : 0 < nextOpening x t :=
  lt_trans ht (lt_nextOpening hx h)

#print axioms nextOpening_pos

/-- **(6a) Link rule, slower runner**: a runner `y < x` in the way at the exit of `x`'s lap-`j` zone is on a lap
`≤ j`.  (Provenance: `ZoneLink.slower_lap_le`.)  No positivity of `y` is used. -/
theorem link_slower_lap_le {x y t : ℝ} (hx : 0 < x) (ht : 0 < t) (h : InWay x t) (hyx : y < x)
    (hy : InWay y (nextOpening x t)) : lap y (nextOpening x t) ≤ lap x t := by
  have ht' := nextOpening_pos hx ht h
  have hs := setter_reading hx h
  have hb := abs_lt.mp (abs_sub_lap_lt hy)
  have hlt : y * nextOpening x t < x * nextOpening x t := mul_lt_mul_of_pos_right hyx ht'
  have : (lap y (nextOpening x t) : ℝ) < (lap x t : ℝ) + 1 := by linarith
  have : lap y (nextOpening x t) < lap x t + 1 := by exact_mod_cast this
  omega

#print axioms link_slower_lap_le

/-- **(6b) Link rule, faster runner**: a runner `y > x` in the way at the exit of `x`'s lap-`j` zone is on a lap
`≥ j + 1`.  (Provenance: `ZoneLink.faster_lap_lt`.) -/
theorem link_faster_lap_ge {x y t : ℝ} (hx : 0 < x) (ht : 0 < t) (h : InWay x t) (hxy : x < y)
    (hy : InWay y (nextOpening x t)) : lap x t + 1 ≤ lap y (nextOpening x t) := by
  have ht' := nextOpening_pos hx ht h
  have hs := setter_reading hx h
  have hb := abs_lt.mp (abs_sub_lap_lt hy)
  have hlt : x * nextOpening x t < y * nextOpening x t := mul_lt_mul_of_pos_right hxy ht'
  have : (lap x t : ℝ) < (lap y (nextOpening x t) : ℝ) := by linarith
  have : lap x t < lap y (nextOpening x t) := by exact_mod_cast this
  omega

#print axioms link_faster_lap_ge

/-- **(6c) Link rule along a cascade sequence.**  If the forward move `seq n → seq (n+1)` is set by `x` and the
forward move `seq (n+1) → seq (n+2)` is set by `y`, then `y ≠ x`; if `y < x` the lap of `y` at `seq (n+1)` is at most
the lap of `x` at `seq n`; if `x < y` it is at least one more; and the next instant is `y`'s opening on that lap. -/
theorem link_rule_seq {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {seq : ℕ → ℝ} (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) {n : ℕ} {x y : ℝ} (hx : x ∈ ds)
    (hwx : InWay x (seq n)) (hsx : seq (n + 1) = nextOpening x (seq n))
    (hwy : InWay y (seq (n + 1))) (hsy : seq (n + 2) = nextOpening y (seq (n + 1))) :
    y ≠ x ∧
    (y < x → lap y (seq (n + 1)) ≤ lap x (seq n)) ∧
    (x < y → lap x (seq n) + 1 ≤ lap y (seq (n + 1))) ∧
    seq (n + 2) = ((lap y (seq (n + 1)) : ℝ) + 1 / 8) / y := by
  have htn : 0 < seq n := lt_of_lt_of_le h0 (start_le_seq hpos hmv n)
  have hx0 := hpos x hx
  refine ⟨consecutive_setters_ne hpos hx hsx hwy, ?_, ?_, ?_⟩
  · intro hyx
    rw [hsx] at hwy ⊢
    exact link_slower_lap_le hx0 htn hwx hyx hwy
  · intro hxy
    rw [hsx] at hwy ⊢
    exact link_faster_lap_ge hx0 htn hwx hxy hwy
  · rw [hsy]
    exact nextOpening_eq_lap hwy

#print axioms link_rule_seq

/-! ## Successive setters' start slots ([reasoned], not formalised)

[reasoned] The proved statements constrain the laps of successive setters at the landing, not their positions at the
start `t₀ = 1/(8m)`.  Composing (2) along the chain gives, for every disparity `d`, `8·d·tₙ = 8·d·t₀ + d·Σₖ gₖ/xₖ`
(a telescoping of `8·d·(tₖ₊₁ − tₖ) = gₖ·d/xₖ`, which is `8·d·(tₙ − t₀)`), so the total shift of every reading is
proportional to its own disparity with one common coefficient `Σₖ gₖ/xₖ = 8·(tₙ − t₀)`.  A setter's start slot is
therefore determined by its landing lap and that common coefficient: `8·y·t₀ = 8·lap y tₙ ± (<1) − 8·y·(tₙ − t₀)`.
A strict descent of start slots between successive setters would need a comparison between `8·y·(tₙ − t₀)` and the
lap difference given by (6), which depends on the ratio `y/x` and not only on its sign; (6) controls the sign only.
No symbolic reason for or against a slot relation was found here, and none is claimed.
-/

end Dilation

end Fresh
