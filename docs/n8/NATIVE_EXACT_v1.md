# Dropping the rounding: the problem is exact, and the reflection is obstructed by two residues

Answering the owner's question — *is rounding needed, when everything else is exact?* **No.** Rounding
was the only inexact step, it was never native, and it is the step that produced every error in this
thread.

## The exact formulation

The candidate is `τ = (8q+1)/(8m)`; the clear test is an integer congruence
(`ArithForm.near_iff_int`); and `Rescale.divisor_reduces` turns each constraint into a condition on
`q mod bᵢ`. So a divisor-closed profile is clear **iff there is an integer `q` with**

> `bᵢ ≤ 8·(q mod bᵢ) + 1 ≤ 7bᵢ` for every quotient `bᵢ = m/sᵢ`, including `bᵢ = m`.

The `b = m` condition is exactly the admissible range, so nothing else is needed. All moduli divide
`m`, so everything is decided by `q mod m`. No reals appear anywhere.

**Verified natively:** 51,295 divisor-closed profiles, exhaustive over `m < 320`, **0 with no
solution**. Solution density: min `1/45`, median `0.179`, max `0.319` (the naive independent estimate
is `(3/4)⁵ = 0.237`). **The smallest number of solutions over all profiles is 2 — never 1, never 0.**

Where rounding had gone wrong: it introduced the `1/8` offset that produced 603 phantom failures, the
false `b = 2` "facet" built on them, and a `35`-vs-`28` threshold confusion. None of it was in the
mathematics.

## The reflection, and the two residues that obstruct it

"Never exactly 1" suggests an involution, and there is one: `r ↦ b − r`.

Clearing at `r` says `8r ∈ [b−1, 7b−1]`; clearing at `b−r` says `8r ∈ [b+1, 7b+1]`. These differ only
if a multiple of `8` lands in `{b−1, b}` or `{7b, 7b+1}` — that is, iff `b ≡ 0` or `b ≡ 1 (mod 8)`.

> **`Involution.clear_reflect`** — for `b mod 8 ∈ [2,7]`, clearing is invariant under `r ↦ b − r`.
> **`Involution.reflect_fails_zero`** — at `b ≡ 0`, `r = b/8` clears and its reflection does not.
> **`Involution.reflect_fails_one`** — at `b ≡ 1`, `r = (b−1)/8` clears and its reflection does not.

All three Lean, axiom-clean. Exact for all `b < 5000` by direct computation.

**The two obstructing residues are the framework's own.** `b ≡ 0 (mod 8)` is the collision condition
that splits Branch A from Branch B. `b ≡ 1 (mod 8)` is the guard relation `s·R ≡ 1 (mod 8)`. The
reflection survives on the band `b mod 8 ∈ [2,7]` and nowhere else — the same band as `R mod 8`.

## Corrections made in reaching this

- A first guess that the obstruction was `8 ∣ b` alone was **wrong** — 500 exceptions and 5,195
  prediction mismatches. The hand algebra for `b = 8j+1` was simply miscomputed. The obstruction is
  `b ≡ 0` **or** `b ≡ 1`, and it was found by computing the symmetric set rather than guessing it.
- The `5/8` floor on the widest clear component, measured earlier in this thread, is a statement
  about the **real** clear set. In the exact formulation that is the wrong object and it is not used.

## What this does not do

The reflection does not prove non-emptiness. A free involution forces an even count, which is
consistent with zero. It explains the absence of *singleton* solution sets, not the absence of empty
ones. Divisor-closed remains verified, not proved.
