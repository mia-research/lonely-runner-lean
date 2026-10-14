# Divisor-closed profiles: the category, the reduction, and what is still owed

Reasoning forward from `Rescale.gcd_covariant`. **Not closed.** The reduction is proved; the last
step is not, and the gap is named exactly.

## The category

**Divisor-closed:** every reading divides the largest, `m`. The rule is fixed, not searched:
**take `sₖ = m`.**

**Verified:** 1,662,240 profiles — exhaustive over every `m < 1200` with at least seven divisors and
every 7-subset containing `1` and `m` — `sₖ = m` supplies a witness in **all** of them, 0 failures.
The same profiles under Branch A's move `sₖ = 1` fail **23%** of the time, so `sₖ = m` is doing the
work, not the category.

## The reduction — proved

`Rescale.divisor_reduces` (Lean, axiom-clean): `s ∣ m → (blocks s A m ↔ blocks 1 A (m/s))`.

Because `gcd(sᵢ, m) = sᵢ`, `gcd_covariant` collapses **every** constraint to a unit one. The
profile's interaction structure disappears; only the seven quotients `bᵢ = m/sᵢ` survive. Two are
free — `sᵢ = m` gives `b = 1`, `sᵢ = 1` gives `b = m` — leaving **five** constraints.

Writing `A = 8q+1`, `blocks 1 A b` says `q mod b` sits within `≈ b/8` of `0`. So a witness is an
integer `q` with

> `‖q/bᵢ‖ ≳ 1/8` for five moduli `b₁..b₅`.

That is an **order-6 question at threshold `1/8`**, and the proved bound at order 6 is `1/6`. There
is slack, not a deficit — the opposite situation to the counting wall.

## What is owed

The order-6 bound supplies a **real** witness; the reduction needs an **integer** `q`. Closing the
category means converting one to the other, and the slack (`1/6` against `1/8`) is the room to do it
in. `ReachRule.witness_normalised` is the natural tool, since it already says a witness may be taken
rational with a controlled denominator. **Untried.**

## Refuted on the way

**`A = c·m + 1` is not the witness.** Derived from the reduction: `A mod 8bᵢ = bᵢ·(c·sᵢ mod 8) + 1`,
which lands in `[bᵢ, 7bᵢ]` exactly when `c·sᵢ mod 8 ∈ [1,6]`. The derivation is correct — 0
mismatches in 857,328 exhaustive profiles whenever such a `c` exists. But `c` exists only **12%** of
the time, and the reason kills it: if `8 ∣ sᵢ` then `c·sᵢ ≡ 0 (mod 8)` for every `c`, so the form
only ever covers Branch A, which is already proved. `(1,2,3,4,6,8,24)` admits no `c`, yet `A = 41`
is a witness.

## Two categories refuted — and a sampling failure recorded

An earlier pass reported three categories closed by `sₖ = s_max`. Two were **artefacts of range
bias** and are withdrawn:

| category | first (biased) result | exhaustive result |
|---|---|---|
| collider is the largest reading | 47,367 profiles, **0** fails | 4,000,001 profiles, **408** fails |
| all readings share a factor with `s_max` | 13,703 profiles, **0** fails | 3,000,001 profiles, **177** fails |

The cause: the sampler drew non-collider readings from `[2,500)`, so it essentially never produced a
profile with all readings small — and the known counterexample to the `s_max` rule,
`(1,2,3,4,5,7,8)`, is exactly of that shape. A control on that single profile would have caught it
immediately, and is now the first line of the script. Recorded because the manufactured `0` was
convincing.
