# Every candidate family is a divisor system

Taken from a parallel reading that proposed composing §14.2, §14.3 and §14.20–14.23. The composition
it points at is real, and it corrects a misconception of mine that has shaped several weeks of work.

## What composes

`gcd_covariant` and `divisor_reduces` were used separately — the first to strip common factors, the
second only for profiles whose readings all divide the largest. Composed:

For **any** two readings, with `g` any common divisor,

> **`Rescale.common_factor_reduces`** — `blocks sⱼ A sᵢ ↔ blocks (sⱼ/g) A (sᵢ/g)`;
> **`Rescale.reduced_modulus_dvd`** — `(sᵢ/g) ∣ sᵢ`.

Both Lean, axiom-clean. Taking `g = gcd(sⱼ, sᵢ)` gives the coprime parts, and the reduced modulus
still divides `sᵢ`.

> **The constraints on a candidate family always sit at moduli dividing `sᵢ`. The divisor-closed
> setting is not a special case — it is the per-family structure of an arbitrary profile.**

**Verified: 12,372,192 instances over all 6-subsets of `[2,22)`, 0 failures on both halves.** Distinct
reduced moduli per family: 1 to 5.

## Why this matters to me specifically

I studied "divisor-closed profiles" as a restricted sub-category — profiles whose readings happen to
divide the largest — and reported results scoped to it: the reduction to unit constraints, the
small-modulus law and its `n−1` break, the reflection and its two centres, the unique degenerate
modulus, and the exhaustive verification over 185,729 profiles.

**All of that applies to every candidate family of every profile.** The scoping was mine, not the
mathematics'. `divisor_reduces` needed `s ∣ m`; after the common-factor reduction that hypothesis is
free.

## A second usable item from the same reading

`Rescale.rescaled_residue` says a multiple `c·sᵢ` sits at `sᵢ·(c mod 8)` at **every** candidate of
`sᵢ`, independent of the opening. So multiples of `sᵢ` are **constant on the family**: they block all
of it or none.

**Confirmed: 655,310/655,310 checks.** The dichotomy per family: dead outright if some multiple has
quotient `≡ 0 (mod 8)`; otherwise those readings never block it.

As a filter it is weak — it kills 1–3 families per profile out of 7, never all (trivially: `s_max` has
no multiples in the profile), and surviving families still face about six varying blockers. Recorded
as proved and weak, not as a route.

## One correction to the proposal

The parallel reading writes the obligation as a single covering problem on `ℤ/sᵢℤ` with one modulus
`b`. But `b` depends on the blocker: `bⱼ = sᵢ/gcd(sⱼ, sᵢ)`. The family is therefore a system at
**several** moduli, all dividing `sᵢ` — which is what makes it a divisor system rather than a single
congruence. That is the stronger reading, not a weaker one: it is exactly the object the
divisor-closed apparatus was built for.

## Status

**`[PROVED]`**: the two composition theorems, axiom-clean; witness file now 58 declarations.
**`[VERIFIED]`**: the 12.4M-instance check, and the constancy of multiples.
**Not proved**: Existence. What changes is scope — the divisor apparatus is universal per-family, so
every result scoped to "divisor-closed profiles" should be re-read as scoped to "one candidate
family", which is every profile.
