import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.Dilation

/-!
# Chain laws: the order of setters along a cascade (Task I; record E315, E323, E332)

Built on `Fresh/Framework.lean` (`InWay`, `nextOpening`, `IsMove`), `Fresh/Cascade.lean` (`le_of_isMove`,
`start_le_seq`, `not_inWay_at_nextOpening`) and `Fresh/Dilation.lean` (`lap`, `setter_reading`,
`nextOpening_eq_lap`, `link_rule_seq`).  Nothing is imported from the existing `LonelyRunner` repo; every proof below
was written for this file.  Exact reals only; every disparity is positive (no runner is stationary).

Setting: `ds` a finite set of positive disparities; `seq` a cascade sequence (`IsMove ds (seq n) (seq (n+1))` for all
`n`) with `seq 0 > 0`.  `x` is **the setter at `n`** when `x ∈ ds`, `x` is in the way at `seq n`, and
`seq (n+1) = nextOpening x (seq n)` (a forward move).  A fixed step has no setter.

The record found three order statements by enumeration (E332 [TESTED 0/372,642], E323 [TREE 0/9,651], E315 [TESTED]).
The symbolic reason lying inside all three is one inequality, `later_lap_of_ge` below:

  **after `x` sets on lap `j`, every runner at least as fast as `x` that is in the way at any later instant of the
  cascade is on lap `≥ j + 1`.**

Why: the setter lands at `x · seq (n+1) = j + 1/8` exactly (`Dilation.setter_reading`); the cascade never goes back
(`Cascade.le_of_isMove`), so for `m > n` and `y ≥ x`, `y · seq m ≥ x · seq (n+1) = j + 1/8`; being in the way at
`seq m` puts `y · seq m` within `1/8` of its lap, so that lap is `> j`.  Neither the maximality clause of `IsMove`
(the move goes to the LARGEST next opening) nor any property of the other runners is used: the law is a consequence
of "readings only grow" plus "the setter lands one eighth past its lap".  No bound on the number of moves or on the
length of a word is stated or used (rule 7).

Contents.
* (1) `lap_mono`: the lap is monotone in the instant (`d > 0`); `seq_mono`, `lap_seq_mono`: along the cascade, the
  instant and every reading's lap never decrease (E315, first clause).
* (2) `later_lap_of_ge` (the law); `setter_later_lap`: a setter in the way again later is on a strictly higher lap;
  `setter_recur_lap`: a recurring setter recurs on a strictly higher lap (E323 / E315); `setter_not_twice_in_row`:
  the same reading never sets two consecutive moves (E315, second clause).
* (3) `per_lap_decrease`: two setters on the same lap, the later one is strictly slower (E332).
* (4) `word_strictAntiOn_lap`: the rank form; for any choice of setter at every forward step, the setters on one lap
  form a strictly decreasing sequence in speed.  `setters_same_step_distinct_lap`: two different setters of one step
  (a tie of next openings) are on different laps, so the choice never puts two entries of one lap at one step.
* (5) A [reasoned] comment on how this fits with `Dilation.link_rule_seq`, and a Lean form of the "extra fact".

Provenance.  `lap_mono` corresponds to `LRC/Spec/LapDeadlineN.lean` `lap_mono` (there for the stored label
`⌊d·t − 1/8⌋`, here for `round (d·t)`); `later_lap_of_ge` extends the faster clause of `LRC/Spec/ZoneLinkN.lean`
`faster_lap_lt` (re-proved here as `Dilation.link_faster_lap_ge`) from the landing instant to every later instant of
the sequence, and includes the equal case; `setter_not_twice_in_row` is `Dilation.consecutive_setters_ne`
restated in this file's setting.  No existing declaration states the per-lap decrease (E332) or the recurrence law
(E323) as a theorem; I searched `LRC/` for setter/recur/lap lemmas and found none.  No proof was copied.
-/

open Classical

namespace Fresh

namespace ChainLaws

open Cascade Dilation

/-- `x` is the setter of the forward move `seq n → seq (n+1)`: a member of `ds`, in the way at `seq n`, and the move
lands at its next opening. -/
-- STANDING: DEFINITION
def IsSetterAt (ds : Finset ℝ) (seq : ℕ → ℝ) (n : ℕ) (x : ℝ) : Prop :=
  x ∈ ds ∧ InWay x (seq n) ∧ seq (n + 1) = nextOpening x (seq n)

/-! ## (1) Monotonicity of the lap -/

/-- **(1) The lap is monotone in the instant**: `t ≤ t'` and `d > 0` give `lap d t ≤ lap d t'`.  (Only `0 ≤ d` is
used.) -/
theorem lap_mono {d t t' : ℝ} (hd : 0 ≤ d) (htt : t ≤ t') : lap d t ≤ lap d t' := by
  unfold lap
  rw [round_eq, round_eq]
  apply Int.floor_mono
  have : d * t ≤ d * t' := mul_le_mul_of_nonneg_left htt hd
  linarith

#print axioms lap_mono

/-- The cascade's instants never decrease: `n ≤ m → seq n ≤ seq m`. -/
theorem seq_mono {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {seq : ℕ → ℝ}
    (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) : Monotone seq :=
  monotone_nat_of_le_succ (fun n => le_of_isMove hpos (hmv n))

#print axioms seq_mono

/-- **A reading's lap never decreases along the cascade** (E315, first clause), for every positive disparity `d`,
in `ds` or not. -/
theorem lap_seq_mono {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {seq : ℕ → ℝ}
    (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) {d : ℝ} (hd : 0 < d) {n m : ℕ} (hnm : n ≤ m) :
    lap d (seq n) ≤ lap d (seq m) :=
  lap_mono hd.le (seq_mono hpos hmv hnm)

#print axioms lap_seq_mono

/-! ## (2) The law, and the recurrence of a setter -/

/-- **(2) The chain law.**  If `x` sets the move at `n` on lap `j = lap x (seq n)`, then every runner `y ≥ x` that is
in the way at a later instant `seq m` (`m > n`) is on lap `≥ j + 1` there.  `y` need not be in `ds`; only `seq 0 > 0`,
the positivity of `ds`, and the cascade moves are used (not the maximality of the move). -/
theorem later_lap_of_ge {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {seq : ℕ → ℝ} (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) {n m : ℕ} (hnm : n < m) {x y : ℝ}
    (hx : IsSetterAt ds seq n x) (hxy : x ≤ y) (hy : InWay y (seq m)) :
    lap x (seq n) + 1 ≤ lap y (seq m) := by
  obtain ⟨hxds, hxw, hxs⟩ := hx
  have hx0 : 0 < x := hpos x hxds
  -- the landing reading of the setter: x · seq (n+1) = j + 1/8
  have hland : x * seq (n + 1) = (lap x (seq n) : ℝ) + 1 / 8 := by
    rw [hxs]; exact setter_reading hx0 hxw
  have hle : seq (n + 1) ≤ seq m := seq_mono hpos hmv (Nat.succ_le_of_lt hnm)
  have hm0 : 0 < seq m := lt_of_lt_of_le h0 (start_le_seq hpos hmv m)
  -- readings only grow, and y is at least as fast as x
  have h1 : x * seq (n + 1) ≤ x * seq m := mul_le_mul_of_nonneg_left hle hx0.le
  have h2 : x * seq m ≤ y * seq m := mul_le_mul_of_nonneg_right hxy hm0.le
  have hb := abs_lt.mp (abs_sub_lap_lt hy)
  have : (lap x (seq n) : ℝ) < (lap y (seq m) : ℝ) := by linarith
  have : lap x (seq n) < lap y (seq m) := by exact_mod_cast this
  omega

#print axioms later_lap_of_ge

/-- **A setter in the way again later is on a strictly higher lap**: if `x` sets at `n` and is in the way at `seq m`,
`m > n`, then `lap x (seq n) + 1 ≤ lap x (seq m)`.  (After its opening `x` stands at `j + 1/8` and only moves on.) -/
theorem setter_later_lap {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {seq : ℕ → ℝ} (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) {n m : ℕ} (hnm : n < m) {x : ℝ}
    (hx : IsSetterAt ds seq n x) (hw : InWay x (seq m)) :
    lap x (seq n) + 1 ≤ lap x (seq m) :=
  later_lap_of_ge hpos h0 hmv hnm hx le_rfl hw

#print axioms setter_later_lap

/-- **A recurring reading recurs on a strictly higher lap** (E323 / E315): if `x` sets at `n` and again at `m > n`,
then `lap x (seq n) < lap x (seq m)`. -/
theorem setter_recur_lap {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {seq : ℕ → ℝ} (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) {n m : ℕ} (hnm : n < m) {x : ℝ}
    (hxn : IsSetterAt ds seq n x) (hxm : IsSetterAt ds seq m x) :
    lap x (seq n) < lap x (seq m) := by
  have := setter_later_lap hpos h0 hmv hnm hxn hxm.2.1
  omega

#print axioms setter_recur_lap

/-- **The same reading never sets twice in a row** (E315, second clause): a setter at `n` is not in the way at
`seq (n+1)`, so it is not the setter at `n+1`. -/
theorem setter_not_twice_in_row {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {seq : ℕ → ℝ} {n : ℕ} {x : ℝ}
    (hx : IsSetterAt ds seq n x) : ¬ IsSetterAt ds seq (n + 1) x := by
  rintro ⟨_, hw, _⟩
  rw [hx.2.2] at hw
  exact not_inWay_at_nextOpening (hpos x hx.1) hw

#print axioms setter_not_twice_in_row

/-! ## (3) The per-lap decrease (E332) -/

/-- **(3) Per-lap decrease.**  If `x` sets at `n`, `y` sets at `m > n`, and both are on the same lap
(`lap x (seq n) = lap y (seq m)`), then `y < x`.  Contrapositive of `later_lap_of_ge`: `y ≥ x` would put `y` on a
lap `≥ j + 1` at `seq m`.  The case `y = x` is the recurrence law; the case `y > x` is the faster clause of the link
rule carried forward to every later instant.  The brief's longer route (y also in the way at `seq n`, then the
maximality of the move) is valid but not needed. -/
theorem per_lap_decrease {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {seq : ℕ → ℝ} (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) {n m : ℕ} (hnm : n < m) {x y : ℝ}
    (hx : IsSetterAt ds seq n x) (hy : IsSetterAt ds seq m y)
    (hlap : lap x (seq n) = lap y (seq m)) : y < x := by
  by_contra hc
  push Not at hc
  have := later_lap_of_ge hpos h0 hmv hnm hx hc hy.2.1
  omega

#print axioms per_lap_decrease

/-! ## (4) The rank form of E332 -/

/-- **(4) Rank form.**  Let `w n` be any choice of setter at every forward step (`hw : ∀ n ∈ F, IsSetterAt … n (w n)`
on a set `F` of step indices).  Restricted to the entries on one lap `j`, the word is strictly decreasing in speed:
`n < m` in `F` with `lap (w n) (seq n) = j = lap (w m) (seq m)` gives `w m < w n`.  Order only; no length or count. -/
theorem word_strictAntiOn_lap {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {seq : ℕ → ℝ} (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) {F : Set ℕ} {w : ℕ → ℝ}
    (hw : ∀ n ∈ F, IsSetterAt ds seq n (w n)) (j : ℤ) :
    StrictAntiOn w {n | n ∈ F ∧ lap (w n) (seq n) = j} := by
  intro n hn m hm hnm
  exact per_lap_decrease hpos h0 hmv hnm (hw n hn.1) (hw m hm.1) (hn.2.trans hm.2.symm)

#print axioms word_strictAntiOn_lap

/-- The setter's lap at a step from a positive instant is non-negative. -/
theorem setter_lap_nonneg {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {seq : ℕ → ℝ} (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) {n : ℕ} {x : ℝ} (hx : IsSetterAt ds seq n x) :
    0 ≤ lap x (seq n) := by
  have hn0 : 0 < seq n := lt_of_lt_of_le h0 (start_le_seq hpos hmv n)
  have hxt : 0 < x * seq n := mul_pos (hpos x hx.1) hn0
  have hb := abs_lt.mp (abs_sub_lap_lt hx.2.1)
  have : (-1 : ℝ) < (lap x (seq n) : ℝ) := by linarith
  have : (-1 : ℤ) < lap x (seq n) := by exact_mod_cast this
  omega

#print axioms setter_lap_nonneg

/-- **Ties of next openings.**  The setter of a step need not be unique (two runners in the way can share the largest
next opening, e.g. `x = 1` on lap 0 and `y = 9` on lap 1 both open at `1/8`).  Two different setters of one step are
on different laps: equal laps would give `(j + 1/8)/x = (j + 1/8)/y` with `j + 1/8 > 0`, so `x = y`.  Hence the rank
form never has to order two entries of the same step on one lap. -/
theorem setters_same_step_distinct_lap {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {seq : ℕ → ℝ}
    (h0 : 0 < seq 0) (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) {n : ℕ} {x y : ℝ}
    (hx : IsSetterAt ds seq n x) (hy : IsSetterAt ds seq n y) (hlap : lap x (seq n) = lap y (seq n)) :
    x = y := by
  have hx0 := hpos x hx.1
  have hy0 := hpos y hy.1
  have hj := setter_lap_nonneg hpos h0 hmv hx
  have hj' : (0 : ℝ) ≤ (lap x (seq n) : ℝ) := by exact_mod_cast hj
  have hex : seq (n + 1) = ((lap x (seq n) : ℝ) + 1 / 8) / x := by
    rw [hx.2.2]; exact nextOpening_eq_lap hx.2.1
  have hey : seq (n + 1) = ((lap x (seq n) : ℝ) + 1 / 8) / y := by
    rw [hy.2.2, hlap]; exact nextOpening_eq_lap hy.2.1
  rw [hex] at hey
  have hne : ((lap x (seq n) : ℝ) + 1 / 8) ≠ 0 := by positivity
  rw [div_eq_div_iff hx0.ne' hy0.ne'] at hey
  exact (mul_left_cancel₀ hne hey).symm

#print axioms setters_same_step_distinct_lap

/-! ## (5) How the chain laws sit with the link rule

[reasoned] `Dilation.link_rule_seq` speaks about CONSECUTIVE setters (`n`, `n+1`) and about the lap of the later one
at the landing instant `seq (n+1)`.  The per-lap decrease concerns a pair `(n, m)` with `m > n + 1` possible, so it is
not the link rule applied once, and chaining the link rule along `n, n+1, …, m` does not give it either: the slower
clause (`lap ≤ j`) is not transitive in the needed direction, and the intermediate setters can be faster or slower in
any order.  The extra fact needed is that the FASTER clause is persistent: once `x` has landed at `j + 1/8`, the bound
`y · t ≥ j + 1/8` for `y ≥ x` survives every later move because the cascade never goes back and readings are
monotone in `t`.  That persistence is exactly `later_lap_of_ge` (proved, [L]); `link_faster_lap_ge` is its case
`m = n + 1`, `y > x`, and `setter_not_twice_in_row` / `consecutive_setters_ne` is its case `m = n + 1`, `y = x` (with
`InWay` at the opening itself excluded by the exact reading `1/8`).  The slower clause has no persistent form: a
slower runner's lap at a later instant may be any value `≥` its lap at `seq (n+1)` (`lap_seq_mono`); it is the
faster clause alone that orders setters on one lap.  The following theorem records the persistence in the link rule's
own terms. -/

/-- **Persistent faster clause** (Lean form of the extra fact in (5)): with the hypotheses of `link_rule_seq` for the
move at `n`, any `y ≥ x` in the way at any `seq m`, `m ≥ n + 1`, is on lap `≥ lap x (seq n) + 1`. -/
theorem link_faster_persistent {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {seq : ℕ → ℝ} (h0 : 0 < seq 0)
    (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) {n m : ℕ} (hnm : n + 1 ≤ m) {x y : ℝ} (hx : x ∈ ds)
    (hwx : InWay x (seq n)) (hsx : seq (n + 1) = nextOpening x (seq n)) (hxy : x ≤ y)
    (hwy : InWay y (seq m)) : lap x (seq n) + 1 ≤ lap y (seq m) :=
  later_lap_of_ge hpos h0 hmv hnm ⟨hx, hwx, hsx⟩ hxy hwy

#print axioms link_faster_persistent

end ChainLaws

end Fresh
