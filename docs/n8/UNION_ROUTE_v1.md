# The union route: what is measured, and the product argument refuted

Continues `INTEGRALITY_OBSTRUCTION_v1.md`. Target: an *interior*-witness argument, since
normalisation provably cannot supply one on 43.91% of the category. **Not achieved.** One proposed
argument is refuted here, and the direction of its failure is itself informative.

All objects used are the framework's own: the clear intervals `I(b)` of `Rescale.small_b_blocks_iff`,
the quotients of `Rescale.divisor_reduces`, and the exact `ℤ` formulation. No external inequality is
imported; the one previously tried (Hunter–Kounias) stays withdrawn.

## Measured facts

**Bad-set union on chain profiles.** With `Bad(b) = {q : q mod b ∉ I(b)}`, each has density ≈ `1/4`,
so six would give `1.5` if disjoint. On chain profiles (`b₁ ∣ b₂ ∣ … ∣ b₅ ∣ m`), 2,066 profiles with
`m < 700`:

- union density **max `323/360 = 0.8972`**, median `0.8102`, min `0.6964`;
- the union is **never** all of `ℤ/m`.

It stays below 1 essentially because independence would already give it: `1 − (3/4)⁶ = 0.822`.

**The density floor does not decay.** Minimum solution density by range of `m`:
`1/26` (m<320), `1/21` (320–1200), `0.064` (1200–5000), `0.070` (5000–20000). The worst cases sit at
**small `m`**, which is a finite region, and the density grows with `m`.

**The conditional density floor.** If `b ∣ b'` then `q mod b = (q mod b') mod b`, so
`P[q mod b ∈ I(b) | q mod b' ∈ I(b')]` is a pure two-modulus count. Over 8,532 divisor pairs with
`b'` up to 60,000:

> **minimum exactly `3/7 ≈ 0.4286`, attained at `b = 2, b' = 10`; never zero.**

Asymptotically each conditional tends to `|I(b)|/b ≈ 3/4`, so the floor is a small-`b'` phenomenon.

## Refuted — the product bound

The tempting step: chain the conditionals to get
`density ≥ (|I(m)|/m) · ∏ᵢ cond(bᵢ, bᵢ₊₁)`, which with the `3/7` floor would give
`≥ (3/4)(3/7)⁵ = 0.0108 > 0` and hence existence for chain profiles.

**The inequality is false.** Tested on 3,000 chain profiles with `m < 800`: **violated in 2,594 of
them**, tightest ratio `density/product = 0.716` at `m = 360`, chain `(2,6,12,60,180)` — density
`49/360` against a product of `77/405`.

The reason is structural, not incidental: along a chain `q mod b₅` **determines** `q mod b₄, …,
q mod b₁`, so these are not independent conditionals and nothing telescopes.

**And the direction matters.** The joint density is systematically **below** the product — the
constraints reinforce one another's badness rather than behaving independently. So no
independence-flavoured argument, and no bound built from pairwise conditionals, can close this. That
is worth knowing in advance rather than rediscovering.

## Standing

- `Involution.clear_reflect` / `reflect_fails_zero` / `reflect_fails_one` — proved, axiom-clean.
- The native exact formulation: 0 failures in 51,295 exhaustive profiles, minimum solution count 2.
- `[VERIFIED]`, not proved. Three routes now closed with reasons: bounded centre offset (offset grows
  with `m`), normalisation (supplies extremal witnesses only), product of conditionals (inequality
  false, and adversely so).
