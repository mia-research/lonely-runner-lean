import LonelyRunner.LRC.Spec.RationalN
import LonelyRunner.LRC.Spec.ResonanceN

/-!
# Orders six and seven in the same form, and where they differ from five

2026-09-22.  Asked whether the order-five treatment transfers.  It does, and the parts that do
not have stated reasons.  Nothing here imports a cap, a move count or a demand for uniformity.

## The obligation transfers at no cost

`doors_agree` is general `n` — it never depended on the order — so `DoorFlank` is equivalent to
loneliness at six and at seven, both directions, unconditionally, with no new work
(`orderSix_obligation`, `orderSeven_obligation` below, and the two closure statements).

## What is already free at six and seven and is NOT free at five

`exists_lonely_of_card_le_four` carries the hypothesis `6 ≤ n`.  So at **both** six and seven
every subject with at most four distinct disparities is settled unconditionally — by the very
theorem that is unavailable at five.  The open part is therefore `card = n − 1` exactly: five
disparities at order six, five or six at order seven.

That is an inversion worth stating plainly: in this one respect **order five is harder than six
and seven**, because the four-difference termination result reaches them and not it.

## CORRECTED 2026-09-22: the rule that I said fails does not, and the reason was not primality

This file first claimed P1′ *fails* at order six because `n` must be prime, and reported it
firing on **0 of 15,246** sets.  Both were wrong, and the second was my own script.

The criterion's witness is `a = e·(e⁻¹ mod n)`, whose readings are `e·(d·s mod n)`.  Since
`gcd(s,n) = 1`, the band holds exactly when `n ∤ d`.  **Nothing in that needs a prime.**  What it
needs is `gcd(e,n) = 1` — the flank **non-resonant** — which at prime `n` is the same as `n ∤ e`
and at composite `n` is not.  `LRC.Resonance.flankWorks_of_coprime` and
`flankWorks_of_not_resonant` now carry it with no primality hypothesis.

The 0 at order six was an artefact: my script tested `n.Prime ∧ (no disparity divisible by n)`,
which encodes the *theorem's* hypothesis rather than the mechanism.  Corrected
(`experiments/nN/totient_discriminator_v1.out`), taking any coprime flank:

| | order 5 | order 6 | order 7 | order 8 | order 9 |
|---|---|---|---|---|---|
| as first reported (prime form) | 7,537 | **0** | 2,507 | 0 | 0 |
| corrected (coprime flank) | 5,621 | **5,936** | 1,715 | 792 | 165 |

**And the discriminator is neither primality nor parity — it is the totient.**  The usable flanks
at order `n` are the residues coprime to `n`, a `φ(n)/n` fraction:

    n         5     6     7     8     9    10    11    12    15    16
    φ(n)/n  0.800 0.333 0.857 0.500 0.667 0.400 0.909 0.333 0.533 0.500

Primality is the top of that scale, not a switch: `φ(p)/p = 1 − 1/p`.  Evenness is a consequence,
not a cause: `2 ∣ n` forces `φ(n)/n ≤ 1/2`, which is why even orders look uniformly bad.  Neither
rule predicts the two cases that separate them — **order 9** (odd, not prime) sits at `2/3`,
between the primes and order 8, where parity would put it with the primes and primality with
order 6; and **order 15** (odd, not a prime power) sits at `8/15`, no better than order 16.

My earlier measurement could not have distinguished these: 5 and 7 are *both* prime and odd, 6 is
*both* composite and even.  Order 9 is the discriminating case, and it is the one I had just
argued was unnecessary to run.

This is §5's `φ(n)` count (`isolation_iff_coprime`, `card_coprime_eq_totient`) reached from the
flank side.  The framework had already named the quantity; I called it primality.

## The one rule that has to be restated

At order five the **largest** flank hosts a lonely opening for every set.  It does not at six or
seven — 49 of 15,246 fail at six, 81 of 4,998 at seven.  So `DoorLargestFlank` is refuted there
(already recorded), and any rule written at the largest flank must be rewritten at a general
flank, which `lonely_iff_exists_flank` permits.  That rewrite was the single largest gain in the
order-five work.

## What transfers best, and the trap beside it

`ratWorks_le_order` is general `n`: for `q ≤ n`, `t = 1/q` is lonely when no disparity is
divisible by `q`.  That is `n − 1` rules at order `n`, and it gets **stronger** with the order,
because the band `[1/n, 1 − 1/n]` widens while each blocker excludes only `2/n`.

Measured on a matched sample (12,000 random primitive tuples per order, entries from `[1,200]`),
the smallest working denominator does not grow with the order: maxima `19, 20, 20, 23, 22, 23`
and medians `5, 5, 6, 7, 7, 7` at `n = 5 … 10`.

**The trap.** Those maxima invite the statement *"`q ≤ 23` always works"*, and that would be a
cap — the same foreign shape as `RCapped`, and refused for the same reason.  It is also false as
far as anything here shows: an adversarial search at order five reaches `q = 43`.  The native
statement is not a bound on `q`.  It is the family of rules above, one per `q`, each with an
explicit divisibility condition, and the open question is whether their conditions are jointly
exhaustive — a case analysis, which admits partial results, and not a bound, which does not.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.OrderSixSeven

open LRC.SpecN LRC.RationalN MomentIterationN

instance fact_two_le_six : Fact (2 ≤ 6) := ⟨by norm_num⟩
instance fact_two_le_seven : Fact (2 ≤ 7) := ⟨by norm_num⟩

/-! ## 1. the obligation, at six and at seven -/

/-- **Order six: the flank door is the conjecture.**  No new work — `doors_agree` is general `n`. -/
theorem orderSix_obligation (v : Fin 6 → ℝ) (hv : Function.Injective v) (k : Fin 6) :
    DoorFlank v k ↔ LonelyForSubject v k := (doors_agree (n := 6) hv k).1

/-- **Order seven: likewise.** -/
theorem orderSeven_obligation (v : Fin 7 → ℝ) (hv : Function.Injective v) (k : Fin 7) :
    DoorFlank v k ↔ LonelyForSubject v k := (doors_agree (n := 7) hv k).1

/-- Exhibiting a flank and an index at every subject closes order six. -/
theorem lonelyRunnerAtSix_of_doorFlank
    (h : ∀ v : Fin 6 → ℝ, Function.Injective v → ∀ k : Fin 6, DoorFlank v k) :
    LonelyRunnerAtN 6 := lonelyRunnerAtN_of_doorFlank h

/-- And order seven. -/
theorem lonelyRunnerAtSeven_of_doorFlank
    (h : ∀ v : Fin 7 → ℝ, Function.Injective v → ∀ k : Fin 7, DoorFlank v k) :
    LonelyRunnerAtN 7 := lonelyRunnerAtN_of_doorFlank h

/-! ## 2. what is free at six and seven and not at five -/

/-- **Four disparities are settled at six**, unconditionally, by the theorem that does not reach
five.  So the open part at order six is `card = 5`. -/
theorem six_card_le_four {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 4) :
    ∃ s : ℝ, 0 < s ∧ Lonely 6 ds s :=
  exists_lonely_of_card_le_four (n := 6) (by norm_num) hpos hcard

/-- **And at seven.**  The open part at order seven is `card = 5` or `card = 6`. -/
theorem seven_card_le_four {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 4) :
    ∃ s : ℝ, 0 < s ∧ Lonely 7 ds s :=
  exists_lonely_of_card_le_four (n := 7) (by norm_num) hpos hcard

/-! ## 3. the divisibility rules, at six and at seven

`ratWorks_le_order` gives `q = 2, …, n`.  Order six has five such rules, order seven has six.
Each is a condition on the difference set, not a bound on anything. -/

/-- **Order six, `t = 1/q` for any `q ≤ 6`.** -/
theorem lonely_six_of_not_dvd {ds : Finset ℝ} (L : List ℕ) (q : ℕ) (hq0 : 0 < q) (hq6 : q ≤ 6)
    (hcov : ∀ d ∈ ds, ∃ m ∈ L, d = (m : ℝ)) (h : ∀ d ∈ L, ¬ (q ∣ d)) :
    ∃ s : ℝ, 0 < s ∧ Lonely 6 ds s :=
  exists_lonely_of_ratWorks (n := 6) L 1 q hq0 (by norm_num) hcov
    (ratWorks_le_order (n := 6) L q hq0 hq6 h)

/-- **Order seven, `t = 1/q` for any `q ≤ 7`.** -/
theorem lonely_seven_of_not_dvd {ds : Finset ℝ} (L : List ℕ) (q : ℕ) (hq0 : 0 < q) (hq7 : q ≤ 7)
    (hcov : ∀ d ∈ ds, ∃ m ∈ L, d = (m : ℝ)) (h : ∀ d ∈ L, ¬ (q ∣ d)) :
    ∃ s : ℝ, 0 < s ∧ Lonely 7 ds s :=
  exists_lonely_of_ratWorks (n := 7) L 1 q hq0 (by norm_num) hcov
    (ratWorks_le_order (n := 7) L q hq0 hq7 h)

/-! ## 4. worked instances, so neither is vacuous -/

/-- At order six, `(1, 5, 7, 11, 13)` — no disparity even, so `t = 1/2`. -/
theorem six_instance : ratWorks 6 [1, 5, 7, 11, 13] 1 2 = true := by decide

/-- At order seven, `(1, 2, 4, 5, 8, 10)` — no disparity divisible by 3, so `t = 1/3`. -/
theorem seven_instance : ratWorks 7 [1, 2, 4, 5, 8, 10] 1 3 = true := by decide

/-! ## 5. cases composing — what the native form looks like when it assembles

A rule that fires on a condition is one case.  Two rules whose conditions are complementary over
a describable region are a **case analysis**, and that is what a proof is in this form.  The
prime halves of P1′ compose exactly that way, and the composition names its own remaining case
rather than leaving it implicit.

At prime `n`, `flankWorks_of_prime` needs the flank not divisible by `n` and no other disparity
divisible by `n`; `flankWorks_of_prime_dvd` needs the flank divisible by `n`, no other disparity
divisible by `n`, and the flank largest.  Between them they settle every whole-number difference
set with **at most one** multiple of `n`, except when that multiple is not the largest member. -/

section PrimeCases
open LRC.FlankFinite LRC.Resonance

/-- **No multiple of `n` at all**: the largest flank opens.  Case A. -/
theorem prime_case_none {n : ℕ} [Fact (2 ≤ n)] (hp : n.Prime) (L : List ℕ) (e : ℕ) (he : 0 < e)
    (hnone : ∀ d ∈ e :: L, ¬ (n ∣ d)) :
    flankWorks n (e :: L) e = true :=
  flankWorks_of_prime hp (e :: L) e he (hnone e List.mem_cons_self) hnone

/-- **Exactly one multiple of `n`, and it is the largest**: take it as the flank.  Case B. -/
theorem prime_case_one {n : ℕ} [Fact (2 ≤ n)] (hp : n.Prime) (L : List ℕ) (e : ℕ) (he : 0 < e)
    (hen : n ∣ e) (hrest : ∀ d ∈ L, ¬ (n ∣ d)) (hlt : ∀ d ∈ L, d < e)
    (hlen : L.length + 1 < n) :
    flankWorks n (e :: L) e = true :=
  flankWorks_of_prime_dvd hp L e he hen hrest hlt hlen

/-- **The two cases together.**  At prime `n`, a whole-number difference set whose multiples of
`n` number at most one, with that one (if present) the largest member, has a lonely flank opening.

The hypothesis `L.length + 1 < n` is `card < n`, which every difference set of an arrangement
satisfies (`diffSet_card_le`).  **The case this does not reach**, named rather than left implicit:
exactly one multiple of `n`, not the largest.  Choosing the largest as flank fails because the
multiple is then a non-flank member divisible by `n`; choosing the multiple as flank fails the
`d < e` hypothesis.  That is one case, and it is the next one to write. -/
theorem prime_at_most_one_multiple {n : ℕ} [Fact (2 ≤ n)] (hp : n.Prime) (L : List ℕ) (e : ℕ)
    (he : 0 < e) (hrest : ∀ d ∈ L, ¬ (n ∣ d)) (hlt : ∀ d ∈ L, d < e) (hlen : L.length + 1 < n) :
    flankWorks n (e :: L) e = true := by
  by_cases hen : n ∣ e
  · exact prime_case_one hp L e he hen hrest hlt hlen
  · refine prime_case_none hp L e he ?_
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hdL
    · exact hen
    · exact hrest d hdL

end PrimeCases

end LRC.OrderSixSeven
