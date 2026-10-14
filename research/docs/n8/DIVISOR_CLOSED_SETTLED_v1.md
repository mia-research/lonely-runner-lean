# Divisor-closed: settled by rule, and why it had not been

Supersedes the failure analysis in `BAND_FACET_v1.md`. **The 603 failures were mine, not the
category's.**

## The rule

For a divisor-closed profile (every reading divides `m = s_max`), take `sₖ = m`. Then:

1. Enumerate the normalised witnesses of the order-7 instance (speeds `{1, s₁..s₅}`) and the order-6
   instance (speeds `s₁..s₅`) — `t = A/(n·s)`, `A ≡ 1 (mod n)`.
2. For each, take `q = round(t·m − 1/8)` and its neighbours `q ± 1`.
3. The witness is `A = 8q+1`.

**Result: 103,060 divisor-closed profiles, exhaustive over `m < 400` and every 7-subset containing
`1` and `m` — 0 not settled.** The previous route left 603.

## Why it had not followed — the `1/8` offset

The candidate is `τ = (8q+1)/(8m)`, **not** `q/m`. They differ by `1/(8m)`. Rounding `t·m` lands on
`q/m` and carries an extra `sᵢ/(8m) = 1/(8bᵢ)` of error on top of the `1/(2bᵢ)` from rounding — total
`5/(8bᵢ)`, which needs `bᵢ ≥ 35`, not 28. Worse, the excess is largest exactly where `bᵢ` is
smallest, which is why **100% of the 603 failures carried `b = 2`**.

So `b = 2` was never a mathematical obstruction. It was where a systematic offset in my own rounding
bit hardest. Asking *why it did not follow* is what found it.

The admissible `τ` are spaced exactly `1/m` apart, so the nearest one satisfies `|τ − t| ≤ 1/(2m)`
and the margin is `1/(2bᵢ)` — recovering `bᵢ ≥ 28` as the derived sufficient threshold.

## Status, stated carefully

- **`[VERIFIED — exhaustive]`** the rule settles every divisor-closed profile with `m < 400`.
- **`[PROVED, not formalised]`** the margin argument for `bᵢ ≥ 28`: an order-7 witness exists
  (`intLRC_seven`, **our own** axiom-clean Lean theorem — in-house, not an import); rounding to the
  nearest admissible `τ` costs at most `1/(2bᵢ) ≤ 1/56`; the order-7 margin is `1/7 − 1/8 = 1/56`.
- **`[OPEN]`** `8 ≤ bᵢ ≤ 27` has no proof. The rule works there empirically at every threshold tested
  on both halves (`lcm(bᵢ) = m` and not), 0 failures — but that is the *rule* succeeding, not the
  margin argument, which is what a proof needs. The gap between "works" and "proved" is exactly the
  20 values of `bᵢ`.
- **`[PROVED]`** the all-`bᵢ ≤ 7` sub-category, via `small_b_blocks_iff` + `g(210) = 10`. **Narrow**:
  it needs `m` divisible by five of `{2..7}`, giving 240 profiles under `m = 6000`.

## Refuted: extending the primorial

Proposal: extend `210` to `P₅ = 2310` so that `q` coprime to `2310` also clears `bᵢ = 11, 22`, since
`g(2310) = 14`.

The Jacobsthal values are right — `g(210) = 10`, `g(2310) = 14`, both recomputed. The reasoning is
not. Coprimality to `2310` gives `q mod 11 ∈ {1..10}`; **but the clear set at `b = 11` is `[2,9]`.**
`q ≡ 1 (mod 11)` is coprime to `2310` and blocked. Likewise `b = 22`, whose clear set is `[3,19]`.

The step being borrowed is "nonzero residue ⟹ clear", which is exactly what `small_b_blocks_iff`
says **fails at `b = 8`**. Enlarging the modulus extends coprimality, not the law. The `b ≤ 7`
boundary is a property of the `n − 1` constant, not of the choice of `210`.

## Also corrected

`R ≈ 11.9657` is a rounded figure; the reproducible witness is `44856/3749 = 11.964791`, and the
rounded profile gives `6.32`. Any argument keyed to the rounded value is keyed to a profile that does
not exist.

**Unchecked:** the claim `s₇·R ≤ 89` giving `R ≤ 89/S`, and the regime split at `S = 7.45`. Not
verified here, and not relied on anywhere above.
