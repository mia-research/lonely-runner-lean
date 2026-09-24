import LonelyRunner.LRC.Spec.IrrationalN
import LonelyRunner.LRC.Cascade.FourDifferences

/-!
# Order five: the obligation, named — and why the order-six proof does not reach it

2026-09-21.  Order five reduces to **one missing theorem**, and this file states it in Lean with
its hypothesis explicit, in the manner of `experiments/n8/RCapObligation_v1.lean`.

## The reduction

A five-runner subject has at most four disparities (`LRC.SpecN.diffSet_card_le`).

* **at most three** — `exists_lonely_of_card_le_three`, unconditional, real-valued, every `n ≥ 4`;
* **exactly four** — open.  `exists_lonely_of_card_le_four` is proved from
  `FourDifferencesSix.four_diffs_stop_ge_six`, whose hypothesis is `6 ≤ n`.

So the whole of order five is the single statement *four differences terminate at `n = 5`*.  Note
what that means: it is **real-valued**, so it closes the commensurable case and the incommensurable
case at once.  Nothing in `FlankFiniteN`, `ResonanceN`, `WindowN`, `SelfSimilarN`, `OtherFlankN` or
`IrrationalN` is needed for it — those criteria cover sets, and this covers the order.

## Why order four goes through and order five does not — the proof SHAPE changes

Every small-order termination result in this tree is a **move count**: the `N`-th iterate is
fixed, for a fixed `N`.

    2 differences, n ≥ 3 : 1 move    `two_diffs_stop_within_one_move`
    3 differences, n ≥ 4 : 3 moves   `three_diffs_stop_within_three_moves`
    4 differences, n ≥ 6 : 7 moves   `four_diffs_stop_ge_six`

Order four is the diagonal case of the second row, and its proof
(`TerminationFour.four_stops_within_three_moves`) is an **exhaustion of the setter word**: at
`n = 4` the nearest runner is clear across the whole of `[1/4, 3/4]` (`clear_in_window`), so it
never sets a move, which leaves `card − 1 = 2` possible setters; consecutive setters differ, so
the word alternates; and `no_four_alternation` (W2) kills `x y x y`.  Hence the word is at most
`x y x`, three moves.  That is attained — `(1,3,12)` has setter word `[12, 3, 12]`.

**At `n = 5` no move count exists at all.**  With `card − 1 = 3` setters the extremal word is a
*shuttle*, `A B A C A B A C A`, which contains no `x y x y` and so never triggers W2.  The family

    ds = (1, 5k − 2, 5k, 10k − 2)

has cascade length `2k + 1` for even `k` and `2k + 2` for odd `k` — verified in exact rational
arithmetic out to `k = 100`, length 201 (`experiments/nN/cascade_length_unbounded_v1.out`).  So
for every `N` there is a five-runner difference set whose `N`-th iterate is not fixed, and the
shape of the three rows above is **unavailable at order five**, not merely unproved.

What does stay bounded along that family is the ratio: `R → 3/2`, never near `4`.  The cascade is
**capped but not short**.  That is the whole reason this file states the obligation as `RCapped`
and not as a move count — `Flanks.exists_fixed_of_capped` is the tool that matches the phenomenon.

`four_diffs_stop_ge_six` is therefore not a theorem whose hypothesis is one too strong.  Its
*conclusion* is false at `n = 5`: six arrangements with entries in `[1,40]` need eight or nine
moves, the first being `(1, 19, 21, 40)` at nine.

## Why the order-six counting bound also fails at five, with the number

`four_diffs_stop_ge_six` runs on `FourSixAlgebra.g_count_bound`:

    g n 1 * (g n 3 * g n 3) ≤ n - 1.

At `n = 6` that is `≤ 5`, and holds.  At `n = 5` the left side is **exactly `968/147`** and the
right side is `4`.  `968/147 = 6.585…`, so it fails **by a factor of `242/147 ≈ 1.646`**
(`g_five_counting_bound_fails`).  That is not a margin a sharper estimate closes: the product of
worst-case growth factors genuinely exceeds the budget at five, and the tools that repair it at
six — `no_return_after_few_faster` needs `n ≥ 2g + 2`, so `g = 2` at six and only `g = 1` at
five — are weaker at five for a stated reason.  **Do not attempt to lower the `6` in
`four_diffs_stop_ge_six`.**

## A CORRECTION, 2026-09-22: `RCapped` is not the obligation, and naming it one was the error

`MANUSCRIPT_v19`, recording the v18 amendment, in terms:

> *To discharge a cap is to bound how far a run goes, which is an obligation the conjecture does
> not carry, and stating the target that way put every attempt on a route that needs one.* …
> *the amended obligation is discharged by* **exhibiting `(e, k)`**, *which is §6.7's
> rules-with-conditions form, so each rule covers a class and the reach is a number, where a cap
> admits no partial result.*

`RCapped` below is a cap, so it is exactly the form v18 amended away — and it is **stronger than
`DoorCapped`**, which is the cap the doors already carry: `DoorCapped v k := ∃ U, ∀ N, …` is
per subject and is an `iff` to loneliness, whereas `RCapped n B` demands one `B` uniform over
every arrangement.  So `RCapped` is strictly stronger than the conjecture at order five, which is
why the `sup R = 31/9` certificate can only reach it for ratio `≤ 26`.

**The obligation at order five is `LRC.SpecN.DoorFlank`** — exhibit a flank and an index — which
`doors_agree` already proves equivalent to loneliness, both directions, unconditionally.  The
rules of `FlankFiniteN`, `ResonanceN`, `WindowN`, `SelfSimilarN`, `OtherFlankN`, `IrrationalN`,
`RationalN` and §3 below are in that form; a cap is not.

What §1 and §2 of this file do establish stands, and is worth keeping for one reason: they show
the *move-count* shape is not merely unproved at five but **false**, so no amount of work on
`four_diffs_stop_*` reaches order five.  That is a negative result about an imported shape, not a
route to a proof.

## What is owed

Two Props, both `OWED` on `scripts/nN/spec_gate.sh`'s register, neither proved here, each
appearing only as an explicit hypothesis.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.OrderFive

open Flanks MomentIterationN LRC.SpecN Arrangement

/-! ## 1. the counting bound at five, computed -/

/-- `g 5 1 = 3/2`. -/
theorem g_five_one : FourSixAlgebra.g 5 1 = 3 / 2 := by
  simp [FourSixAlgebra.g, Finset.prod_range_succ]
  norm_num

/-- `g 5 3 = 44/21`. -/
theorem g_five_three : FourSixAlgebra.g 5 3 = 44 / 21 := by
  simp [FourSixAlgebra.g, Finset.prod_range_succ]
  norm_num

/-- **The order-six counting bound fails at five, and by how much.**  `g_count_bound` asks for
`g n 1 * (g n 3 * g n 3) ≤ n - 1`.  At `n = 5` the left side is `968/147 ≈ 6.585` against a budget
of `4`.  Recorded so that no session spends time sharpening the constant. -/
theorem g_five_counting_bound_fails :
    FourSixAlgebra.g 5 1 * (FourSixAlgebra.g 5 3 * FourSixAlgebra.g 5 3) = 968 / 147 ∧
      ((5 : ℝ) - 1) < FourSixAlgebra.g 5 1 * (FourSixAlgebra.g 5 3 * FourSixAlgebra.g 5 3) := by
  rw [g_five_one, g_five_three]
  norm_num

/-! ## 2. the obligation, with its hypothesis explicit

`R` is the ratio of the cascade's final instant to the subject's first reading.  A universal cap
on it is `DoorCapped`, which `doors_agree` proves equivalent to loneliness.  So the hypothesis
below is exactly as strong as the conjecture at order five — it is a *name* for the gap, not a
weakening of it, and the manuscript's `sup R = 31/9` certificate discharges it for every
arrangement of ratio `d_max / d_min ≤ 26`. -/

/-- **The `R`-cap at order `n`.**  Every cascade iterate stays within a universal factor `B` of the
subject's first reading. -/
def RCapped (n : ℕ) [Fact (2 ≤ n)] (B : ℝ) : Prop :=
  ∀ v : Fin n → ℝ, Function.Injective v → ∀ k : Fin n, ∀ N : ℕ,
    (move n (diffSet v k))^[N] (firstReading v k) ≤ B * firstReading v k

/-- A universal `R`-cap gives `DoorCapped` at every subject. -/
theorem doorCapped_of_RCapped {n : ℕ} [Fact (2 ≤ n)] {B : ℝ} (h : RCapped n B)
    (v : Fin n → ℝ) (hv : Function.Injective v) (k : Fin n) :
    DoorCapped v k :=
  ⟨B * firstReading v k, fun N => h v hv k N⟩

/-- **The chain to the target, at every order.** -/
theorem lonelyRunnerAtN_of_RCapped {n : ℕ} [Fact (2 ≤ n)] {B : ℝ} (h : RCapped n B) :
    LonelyRunnerAtN n :=
  lonelyRunnerAtN_of_doorCapped fun v hv k => doorCapped_of_RCapped h v hv k

/-- **Order five, in one line.**  Any universal cap whatever closes it — the `4` of `R < 4` is
what the certificate route aims at, but the implication needs no particular value. -/
theorem lonelyRunnerAtFive_of_RCapped {B : ℝ} (h : RCapped 5 B) : LonelyRunnerAtN 5 :=
  lonelyRunnerAtN_of_RCapped h

/-! ## 3. the band ladder — the uniform criterion that does not bound the flank ratio

`Flanks.clear_at_opening_of_band` says a runner at ratio `x = d/e` to the flank is clear at the
`k`-th opening when `x·(nk+1)` lands in `[nM+1, nM+n−1]` for some integer `M`.  Reading that as a
band in `d` rather than in the lap:

    d ∈ [ (nM+1)·e/(nk+1), (nM+n−1)·e/(nk+1) ].

At `k = M = 0` this is `d ∈ [e/1, (n−1)e/1]`, which is the ratio condition (Theorem 4.8, P2).  For
`k ≥ 1` and `M = 0` it is `d ∈ [e/(nk+1), (n−1)e/(nk+1)]`: a band of the **same internal spread
`n−1`**, sitting arbitrarily far below the flank.

That is the part worth having.  The order-5 certificate is bounded by `d_max/d_min ≤ 26`; this
criterion has **no bound on the ratio to the flank at all**, only on the spread among the
disparities themselves.  The flank is clear at its own opening for free (`M = k`). -/

variable {n : ℕ} [Fact (2 ≤ n)]

/-- **The flank is always clear at its own openings**, at every index — the `M = k` instance. -/
theorem clear_at_own_flank {e : ℝ} (he : 0 < e) (k : ℕ) :
    (n : ℝ)⁻¹ ≤ circDist (e * flankOpening n e k) := by
  have hn2 : 2 ≤ n := Fact.out
  have hN : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  refine clear_at_opening_of_band he k (k : ℤ) ?_ ?_
  · rw [div_self he.ne']; push_cast; linarith
  · rw [div_self he.ne']; push_cast; linarith

/-- **The band ladder.**  If every disparity other than the flank lies in the band
`[(nM+1)e/(nk+1), (nM+n−1)e/(nk+1)]`, the flank's `k`-th opening is lonely.

Real-valued, every order, and with **no hypothesis bounding `d/e` from below** beyond membership
of the band — so a set whose disparities are all tiny relative to the flank is covered, provided
they are within a factor `(nM+n−1)/(nM+1)` of one another. -/
theorem lonely_flank_of_band {ds : Finset ℝ} {e : ℝ} (he0 : 0 < e) (k : ℕ) (M : ℤ)
    (hlo : ∀ d ∈ ds, d ≠ e → ((n : ℝ) * (M : ℝ) + 1) * e ≤ d * ((n : ℝ) * (k : ℝ) + 1))
    (hhi : ∀ d ∈ ds, d ≠ e → d * ((n : ℝ) * (k : ℝ) + 1) ≤ ((n : ℝ) * (M : ℝ) + (n : ℝ) - 1) * e) :
    Lonely n ds (flankOpening n e k) := by
  intro d hd
  by_cases hde : d = e
  · subst hde; exact clear_at_own_flank he0 k
  · refine clear_at_opening_of_band he0 k M ?_ ?_
    · rw [div_mul_eq_mul_div, le_div_iff₀ he0]; exact hlo d hd hde
    · rw [div_mul_eq_mul_div, div_le_iff₀ he0]; exact hhi d hd hde

/-- **The `M = 0` rung, stated as a spread condition.**  Every disparity but the flank lies in
`[e/(nk+1), (n−1)e/(nk+1)]`: internal spread at most `n−1`, flank ratio unbounded. -/
theorem lonely_flank_of_spread {ds : Finset ℝ} {e : ℝ} (he0 : 0 < e) (k : ℕ)
    (hlo : ∀ d ∈ ds, d ≠ e → e ≤ d * ((n : ℝ) * (k : ℝ) + 1))
    (hhi : ∀ d ∈ ds, d ≠ e → d * ((n : ℝ) * (k : ℝ) + 1) ≤ ((n : ℝ) - 1) * e) :
    Lonely n ds (flankOpening n e k) := by
  refine lonely_flank_of_band he0 k 0 ?_ ?_ <;> intro d hd hde
  · have := hlo d hd hde; push_cast; linarith
  · have := hhi d hd hde; push_cast; linarith

/-- **And it gives a lonely instant.** -/
theorem exists_lonely_of_spread {ds : Finset ℝ} {e : ℝ} (he0 : 0 < e) (k : ℕ)
    (hlo : ∀ d ∈ ds, d ≠ e → e ≤ d * ((n : ℝ) * (k : ℝ) + 1))
    (hhi : ∀ d ∈ ds, d ≠ e → d * ((n : ℝ) * (k : ℝ) + 1) ≤ ((n : ℝ) - 1) * e) :
    ∃ s : ℝ, 0 < s ∧ Lonely n ds s :=
  ⟨flankOpening n e k, flankOpening_pos he0 k, lonely_flank_of_spread he0 k hlo hhi⟩

/-! ## 3a. item 2 of the working list: the band family's condition, in integers

The band ladder fires at `(k, M)` when every non-flank ratio lies in
`[(nM+1)/(nk+1), (nM+n−1)/(nk+1)]`.  Written on the disparities rather than the ratios, that is
two integer inequalities and no real number survives — which is what lets the condition be
reasoned about rather than only checked.

Eliminating `M` between them gives a **necessary** condition with no `M` in it at all: the spread
of the non-flank disparities, scaled by the opening index, is bounded by the flank.

And at `k = 0` with the flank at `d_min` that bound **is** the ratio condition, Theorem 4.8.  So
P2 is not a separate rule; it is the `k = 0` rung of this family, and the family is the statement
of P2 at every opening index. -/

/-- **The band condition, in integers.** -/
def BandFits (n e dmin dmax k M : ℕ) : Prop :=
  e * (n * M + 1) ≤ dmin * (n * k + 1) ∧ dmax * (n * k + 1) ≤ e * (n * M + n - 1)

/-- **The band family forces a spread bound**, with `M` eliminated: the non-flank spread times
the opening scale is at most `(n−2)` flanks.  Necessary, not sufficient — `M` must still be an
integer — but it holds with no search and is the family's reach in one inequality. -/
theorem bandFits_forces_spread {e dmin dmax k M : ℕ} (hle : dmin ≤ dmax)
    (h : BandFits n e dmin dmax k M) :
    (dmax - dmin) * (n * k + 1) ≤ e * (n - 2) := by
  have hn2 : 2 ≤ n := Fact.out
  obtain ⟨h1, h2⟩ := h
  have hBA : e * (n * M + n - 1) = e * (n * M + 1) + e * (n - 2) := by
    have : n * M + n - 1 = (n * M + 1) + (n - 2) := by omega
    rw [this, Nat.mul_add]
  have hsub : (dmax - dmin) * (n * k + 1) = dmax * (n * k + 1) - dmin * (n * k + 1) :=
    Nat.sub_mul _ _ _
  have hmono : dmin * (n * k + 1) ≤ dmax * (n * k + 1) := Nat.mul_le_mul_right _ hle
  rw [hBA] at h2
  omega

/-- **At `k = 0` with the flank at `d_min`, the spread bound is Theorem 4.8.**  The ratio
condition `d_max ≤ (n−1)·d_min` and the band family's `k = 0` rung are the same statement. -/
theorem spread_zero_iff_ratio {dmin dmax : ℕ} (hle : dmin ≤ dmax) (hpos : 0 < dmin) :
    (dmax - dmin) * (n * 0 + 1) ≤ dmin * (n - 2) ↔ dmax ≤ dmin * (n - 1) := by
  have hn2 : 2 ≤ n := Fact.out
  have hexp : dmin * (n - 1) = dmin * (n - 2) + dmin := by
    have : n - 1 = (n - 2) + 1 := by omega
    rw [this, Nat.mul_add, Nat.mul_one]
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one]
  omega

/-- **A unit disparity collapses the band family.**  If the non-flank disparities include `1`,
the band condition forces every one of them below `n`.

The two hypotheses fight: `e·(nM+1) ≤ 1·(nk+1)` puts the opening scale `T = nk+1` at or above the
flank, and the spread bound `(dmax − 1)·T ≤ e·(n−2)` then has `T ≥ e` to divide out, leaving
`dmax − 1 ≤ n − 2`.

Consequence, with `ratWorks_family_fails_iff`: a set on which the divisibility family fails
carries a multiple of `n`, hence a disparity at least `n`.  So if such a set also contains `1`,
the band family can fire only where that large disparity is itself the flank — or where `1` is.
That is the whole of the band family's reach on those sets, and it is two named cases rather than
a residue. -/
theorem bandFits_with_unit_forces_small {e dmax k M : ℕ} (he : 0 < e)
    (hle : 1 ≤ dmax) (h : BandFits n e 1 dmax k M) : dmax ≤ n - 1 := by
  have hn2 : 2 ≤ n := Fact.out
  obtain ⟨h1, h2⟩ := h
  simp only [Nat.one_mul] at h1
  have hT : e ≤ n * k + 1 := by
    have hge : e ≤ e * (n * M + 1) := Nat.le_mul_of_pos_right e (by omega)
    omega
  have hsp := bandFits_forces_spread (n := n) hle ⟨by simpa using h1, h2⟩
  have hmul : (dmax - 1) * e ≤ (dmax - 1) * (n * k + 1) := Nat.mul_le_mul_left _ hT
  have hfin : (dmax - 1) * e ≤ (n - 2) * e := by
    calc (dmax - 1) * e ≤ (dmax - 1) * (n * k + 1) := hmul
      _ ≤ e * (n - 2) := hsp
      _ = (n - 2) * e := Nat.mul_comm _ _
  have := Nat.le_of_mul_le_mul_right hfin he
  omega

/-- **And the band condition gives the opening**, so the integer form is a rule and not only a
bound: `BandFits` at `(k, M)` clears the flank's `k`-th opening. -/
theorem lonely_flank_of_bandFits {ds : Finset ℝ} {e : ℝ} {E dmin dmax k M : ℕ}
    (he0 : 0 < e) (hE : e = (E : ℝ)) (hEpos : 0 < E)
    (hfit : BandFits n E dmin dmax k M)
    (hlo : ∀ d ∈ ds, d ≠ e → (dmin : ℝ) ≤ d) (hhi : ∀ d ∈ ds, d ≠ e → d ≤ (dmax : ℝ)) :
    Lonely n ds (flankOpening n e k) := by
  have hn2 : 2 ≤ n := Fact.out
  have hEr : (0 : ℝ) < (E : ℝ) := by exact_mod_cast hEpos
  obtain ⟨f1, f2⟩ := hfit
  have f1' : ((E : ℝ)) * ((n : ℝ) * (M : ℝ) + 1) ≤ (dmin : ℝ) * ((n : ℝ) * (k : ℝ) + 1) := by
    have := f1; push_cast at this ⊢; exact_mod_cast this
  have f2' : (dmax : ℝ) * ((n : ℝ) * (k : ℝ) + 1) ≤ ((E : ℝ)) * ((n : ℝ) * (M : ℝ) + (n : ℝ) - 1) := by
    have hc : ((n * M + n - 1 : ℕ) : ℝ) = (n : ℝ) * (M : ℝ) + (n : ℝ) - 1 := by
      have : 1 ≤ n * M + n := by omega
      push_cast [Nat.cast_sub this]; ring
    have := f2
    have hcast : ((dmax * (n * k + 1) : ℕ) : ℝ) ≤ ((E * (n * M + n - 1) : ℕ) : ℝ) := by
      exact_mod_cast this
    rw [Nat.cast_mul, Nat.cast_mul, hc] at hcast
    push_cast at hcast ⊢; linarith
  refine lonely_flank_of_band he0 k (M : ℤ) ?_ ?_ <;> intro d hd hde
  · have := hlo d hd hde
    have hmul : (dmin : ℝ) * ((n : ℝ) * (k : ℝ) + 1) ≤ d * ((n : ℝ) * (k : ℝ) + 1) := by
      have hk0 : (0 : ℝ) ≤ (n : ℝ) * (k : ℝ) + 1 := by positivity
      exact mul_le_mul_of_nonneg_right this hk0
    rw [hE]; push_cast; linarith
  · have := hhi d hd hde
    have hmul : d * ((n : ℝ) * (k : ℝ) + 1) ≤ (dmax : ℝ) * ((n : ℝ) * (k : ℝ) + 1) := by
      have hk0 : (0 : ℝ) ≤ (n : ℝ) * (k : ℝ) + 1 := by positivity
      exact mul_le_mul_of_nonneg_right this hk0
    rw [hE]; push_cast; linarith

/-! ## 4. the window constant at order five — the complementary rung, and what it is owed

The band ladder of §3 bounds the **spread among the disparities** and leaves the ratio to the
flank free.  The criterion below does the opposite: it leaves the spread free and asks the flank
to stand clear of the rest.

`LRC.FlankFinite.exists_lonely_flankOpening_of_gap` converts a clear window longer than `1/e` into
a lonely opening of `e`.  So the question is how short the longest clear window of three blockers
can be.  Measured exhaustively over whole-number triples with entries to 45, in exact rational
arithmetic, and sampled over random real triples:

    min over triples (a,b,c) of  W(a,b,c) · max(a,b,c)  =  1/5,

attained at exactly `(1,2,3)` and `(1,3,4)` up to scale
(`experiments/nN/window_constant_v1.out`).  **It is not a `1/n` law** — the same sweep gives
`5/18` at `n = 6`, `1/3` at `n = 7` and `3/8` at `n = 8`, none of them `1/n`.  So `1/5` is a
constant about order five and three blockers, not an instance of a pattern.

`[EMPIRICAL]`.  Stated as a `Prop` and used only as a hypothesis. -/

/-- **The window constant at order five.**  Any three positive reals leave a clear window of
length at least `1/(5·max)` somewhere on the positive axis.  `[EMPIRICAL — exhaustive to 45 in
exact rationals, tight at (1,2,3) and (1,3,4); NOT proved]` -/
def WindowConstantFive : Prop :=
  ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → a ≤ c → b ≤ c →
    ∃ x : ℝ, 0 ≤ x ∧ ∀ t ∈ Set.Ioo x (x + 1 / (5 * c)),
      (5 : ℝ)⁻¹ ≤ circDist (a * t) ∧ (5 : ℝ)⁻¹ ≤ circDist (b * t) ∧
        (5 : ℝ)⁻¹ ≤ circDist (c * t)

/-- **A clear window off the flank is enough.**  The flank need not be clear on the window — it is
clear at its own opening for free (`clear_at_own_flank`), which is where the criterion lands. -/
theorem exists_lonely_flankOpening_of_gap_off_flank {ds : Finset ℝ} {e : ℝ} (he : 0 < e)
    {x L : ℝ} (hx : 0 ≤ x) (hL : 1 / e < L)
    (hwin : ∀ t ∈ Set.Ioo x (x + L), ∀ d ∈ ds, d ≠ e → (n : ℝ)⁻¹ ≤ circDist (d * t)) :
    ∃ j : ℕ, Lonely n ds (flankOpening n e j) := by
  obtain ⟨j, hj⟩ := LRC.FlankFinite.exists_flankOpening_mem_Ioo (n := n) he hx hL
  refine ⟨j, fun d hd => ?_⟩
  by_cases hde : d = e
  · subst hde; exact clear_at_own_flank he j
  · exact hwin _ hj d hd hde

/-- **The wide-flank criterion at order five**, conditional on `WindowConstantFive`: a subject
whose flank exceeds five times every other disparity is lonely.  No bound on the spread among the
other three, so this reaches arrangements of unbounded ratio — the ones the `sup R = 31/9`
certificate does not cover. -/
theorem exists_lonely_of_wide_flank (hW : WindowConstantFive) {ds : Finset ℝ} {e : ℝ}
    (hpos : ∀ d ∈ ds, 0 < d) (he : e ∈ ds) {a b c : ℝ}
    (hsub : ∀ d ∈ ds, d ≠ e → d = a ∨ d = b ∨ d = c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hac : a ≤ c) (hbc : b ≤ c)
    (hwide : 5 * c < e) :
    ∃ s : ℝ, 0 < s ∧ Lonely 5 ds s := by
  have he0 : 0 < e := hpos e he
  obtain ⟨x, hx, hwin⟩ := hW a b c ha hb hc hac hbc
  have hL : 1 / e < 1 / (5 * c) := by
    have h5c : (0 : ℝ) < 5 * c := by linarith
    exact one_div_lt_one_div_of_lt h5c hwide
  obtain ⟨j, hj⟩ :=
    exists_lonely_flankOpening_of_gap_off_flank (n := 5) he0 hx hL
      (fun t ht d hd hde => by
        rcases hsub d hd hde with rfl | rfl | rfl
        · exact (hwin t ht).1
        · exact (hwin t ht).2.1
        · exact (hwin t ht).2.2)
  exact ⟨flankOpening 5 e j, flankOpening_pos he0 j, hj⟩

/-! ## 5. how many disparities there actually are — the circle collapses, it does not add

`diffSet v k` is the image of `i ↦ |v i − v k|`, a **Finset**, so two runners equidistant from the
subject on opposite sides contribute one member, not two.  It is worth being exact about which way
that cuts, because it bears on how much of order five is open.

* **Never more than `n − 1`** (`diffSet_card_le`).  The absolute value is the only place the circle
  enters the count, and it can only identify members.
* **Never fewer than `n − 1` at an extreme subject** (`diffSet_card_eq_of_extreme` below).  For the
  fastest or the slowest runner every `v i − v k` has one sign, so `|·|` is injective there and no
  collapse is possible.  Both extreme subjects of every arrangement carry the full `n − 1`.
* **Often fewer at an interior subject**: `v i + v j = 2 v k` identifies `i` and `j`.  Measured over
  the 33,649 five-runner integer arrangements with speeds in `[0,22]`
  (`experiments/nN/disparity_count_v1.out`): 22,605 of the 100,947 interior subjects collapse to
  `card ≤ 3` and are settled by `exists_lonely_of_card_le_three`; all 67,298 extreme subjects have
  `card = 4`; **no arrangement has every subject at `card ≤ 3`**, and no subject anywhere exceeds 4.

So the open case cannot be dodged by collapse, and it is exactly `card = 4`. -/

/-- **No collapse at an extreme subject.**  If `v k` is the least (or the greatest) speed, every
difference has one sign, so `i ↦ |v i − v k|` is injective off `k` and the subject carries the full
`n − 1` disparities.  A circle identifies a runner ahead with one behind; an extreme runner has
nothing behind it. -/
theorem diffSet_card_eq_of_extreme {v : Fin n → ℝ} (hv : Function.Injective v) (k : Fin n)
    (hext : (∀ i, v k ≤ v i) ∨ (∀ i, v i ≤ v k)) :
    (diffSet v k).card = n - 1 := by
  classical
  have hinj : Set.InjOn (fun i => |v i - v k|) ↑(Finset.univ.erase k) := by
    intro i _ j _ hij
    simp only at hij
    rcases hext with h | h
    · rw [abs_of_nonneg (by linarith [h i] : (0:ℝ) ≤ v i - v k),
          abs_of_nonneg (by linarith [h j] : (0:ℝ) ≤ v j - v k)] at hij
      exact hv (by linarith)
    · rw [abs_of_nonpos (by linarith [h i] : v i - v k ≤ (0:ℝ)),
          abs_of_nonpos (by linarith [h j] : v j - v k ≤ (0:ℝ))] at hij
      exact hv (by linarith)
  rw [SpecN.diffSet, Finset.card_image_of_injOn hinj,
    Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]

/-- **Order five reduces to `card = 4` exactly.**  `card ≤ 3` is already settled unconditionally,
so the obligation of §2 only has to reach the subjects carrying all four disparities — which, by
`diffSet_card_eq_of_extreme`, is at least the two extreme subjects of every arrangement. -/
theorem lonelyRunnerAtFive_of_card_four
    (h : ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card = 4 → ∃ s : ℝ, 0 < s ∧ Lonely 5 ds s) :
    LonelyRunnerAtN 5 := by
  refine lonelyRunnerAtN_of_existence (n := 5) ?_
  intro ds hpos hcard
  rcases eq_or_lt_of_le (show ds.card ≤ 4 by simpa using hcard) with hc | hc
  · exact h ds hpos hc
  · exact exists_lonely_of_card_le_three (n := 5) (by norm_num) hpos (by omega)

end LRC.OrderFive
