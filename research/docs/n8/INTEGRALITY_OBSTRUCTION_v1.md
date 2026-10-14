# Attacking the exact statement: what works, what does not, and why

Continues `NATIVE_EXACT_v1.md`. Target: turn the verified divisor-closed result into a proof. **Not
achieved.** Two constructions refuted, and one structural obstruction identified that explains why
the obvious tool cannot finish.

## The target, restated

A divisor-closed profile is clear iff some integer `q` satisfies `q mod bᵢ ∈ [⌈(bᵢ−1)/8⌉,
⌊(7bᵢ−1)/8⌋]` for each quotient `bᵢ = m/sᵢ`, including `bᵢ = m`. Equivalently `‖q·sᵢ/m‖ ≳ 1/8`:

> **the exact problem is our own order-8 problem with six speeds `{1, s₁..s₅}` instead of seven,
> plus the integrality constraint `q = m·x/8 ∈ ℤ`.**

Six speeds at threshold `1/8` is strictly weaker than order 7 at `1/7`, so real witnesses are
plentiful. **Everything hinges on integrality.**

## Refuted — the centre construction

`m/2` sits dead centre of the clear interval for every `b` with `m/b` odd, and lands on `0` (worst
possible) when `m/b` is even. So try `q = m/2 + δ`.

Measured: the required `δ` is **not bounded**. Max offset 25 for `m < 200`, but 7,962 at
`m = 99,078`. The ratio does fall — `0.208, 0.133, 0.126, 0.089, 0.080` across increasing ranges —
and the worst case says why: `m = 99078` has `b = 49539 = m/2`, quotient 2, so `m/2 ≡ 0` there and
one must shift by about `b/8 = m/16 ≈ 0.0625m`. **The binding constraint is the largest
even-quotient modulus.** A bounded-offset proof is not available.

## The integrality dichotomy

`ReachRule.witness_normalised` gives the witness as `x = 1` or `x = (8k+1)/s`. Converting with
`q = m·x/8`:

- `x = u` odd — `q = u·m/8`, integral **iff `8 ∣ m`**;
- `x = (8k+1)/s` — `q = b(8k+1)/8` with `b = m/s`, integral **iff `8 ∣ b`**.

Integrality is therefore governed by the *same collision criterion*, one level up. Exhaustive over
51,295 profiles (`m < 320`):

| `8 ∣ m` | some `8 ∣ bᵢ` | covered by these two constructions | share |
|---|---|---|---|
| yes | yes | **yes** | 38.15% |
| yes | yes | no | 11.16% |
| yes | no | yes | 0.68% |
| yes | no | no | 6.11% |
| **no** | **no** | **no** | **43.91%** |

Total covered: **38.83%.**

## The obstruction

In the 43.91% where `8 ∤ m` and no `bᵢ ≡ 0 (mod 8)`, neither construction can apply — and this is a
*consequence* of `witness_normalised`, not a coincidence. Since the leftmost witness must have the
normalised form, and integrality of `q = m·x/8` then forces `8 ∣ m` or `8 ∣ b`, it follows that

> **every integral witness there is non-extremal.** The leftmost witness of the six-speed instance
> is never of the form `q/m`.

**Verified: 0 of 14,586** such profiles have an integral leftmost witness.

So `witness_normalised` — the tool this whole line was built on — is structurally unable to finish
on nearly half the category. It locates the *extremal* witness; integrality admits only *interior*
ones. Any proof of this category must produce an interior witness, which normalisation by
construction does not do.

## What stands

- `Involution.clear_reflect` / `reflect_fails_zero` / `reflect_fails_one` — proved, axiom-clean: the
  reflection `r ↦ b − r` preserves clearing exactly on the band `b mod 8 ∈ [2,7]`, obstructed at
  `b ≡ 0` (collision) and `b ≡ 1` (guard).
- The native exact formulation, with 0 failures in 51,295 exhaustive profiles and a minimum solution
  count of 2.
- Divisor-closed remains **`[VERIFIED]`, not proved**, and the reason is now named rather than
  guessed.
