# The anchor, and one category closed

Method used, at the owner's direction: take an empirically verified result, find **why** it holds,
and use that as an analytical anchor to close the category. Applied to divisor-closed profiles
(1,662,240 exhaustive, 0 failures — `DIVISOR_CLOSED_v1.md`).

## The anchor — `[PROVED]`

`Rescale.divisor_reduces` leaves unit constraints `blocks 1 (8q+1) b`. Computing the clear set of
`q mod b` exactly:

```
 b    clear residues of q mod b
 2    1
 3    1 2
 ...
 7    1 2 3 4 5 6         <- ALL nonzero residues
 8    1 2 3 4 5 6         <- 7 dropped; the pattern breaks
```

**`Rescale.small_b_blocks_iff`** (Lean, axiom-clean): for `2 ≤ b ≤ 7`,
`blocks 1 (8q+1) b ↔ b ∣ b q`. The constraint degenerates to bare non-divisibility.

It breaks at `b = 8` — one past `n − 1`, where Theorem 4.8's constant sits, and for the same reason:
`8r+1 ≥ 9 > b` needs `b ≤ 7`, and `8b − 8r − 1 ≥ b` at `r = b−1` needs `8b − 7 ≤ 7b`, again `b ≤ 7`.
**The `n−1` constant is why the category holds.**

## Category closed: every middle quotient `≤ 7`

Divisor-closed, with `m/sᵢ ≤ 7` for all five middle readings. Every constraint is then `bᵢ ∤ q` with
`bᵢ ∈ {2..7}`, so **any `q` coprime to `210` clears all five**. `q` must lie in
`[(m−1)/8, (7m−1)/8]`, of length `3m/4`; the category forces `m` divisible by five of `{2..7}`, so
`m ≥ 60` and the range exceeds 10. Every 10 consecutive integers contain one coprime to `210`
(Jacobsthal `g(210) = 10`), so such a `q` exists.

**Rule:** take the least `q ≥ ⌈(m−1)/8⌉` coprime to `210`; the witness is `A = 8q+1`.
**Verified:** 240 profiles, exhaustive over `m < 6000` and all 5-subsets — 0 failures, largest offset
needed **9**, just inside the bound.

Narrow, and stated as narrow. It is the first category closed by an argument rather than a sweep.

## Route derived for large quotients — `[VERIFIED, not formalised]`

Since `‖q/bᵢ‖ = ‖sᵢ·(q/m)‖`, the constraints are LRC in the six integer speeds `{1, s₁..s₅}` at
`t = q/m`. That is **order 7 — proved in our own tree** (`intLRC_seven`, axiom-clean), threshold
`1/7`. Rounding a real witness `t` to a multiple of `1/m` perturbs `‖sᵢt‖` by at most
`sᵢ/(2m) = 1/(2bᵢ)`, so the margin `1/7 − 1/8 = 1/56` survives exactly when

> **`bᵢ ≥ 28`.**

Including the speed `1` is what supplies the range condition `q ∈ [(m−1)/8, (7m−1)/8]`; it is not
optional.

**The threshold was derived first, then tested.** 903 profiles per arm: `bᵢ ≥ 28` → **0** failures;
`bᵢ ≥ 12` → **40**; `bᵢ ≥ 8` → **121**. The derivation predicted where it breaks.

## What remains in this category

Divisor-closed profiles with a middle quotient in `8 ≤ b ≤ 27`, and mixed profiles spanning both
regimes. Neither route covers them: the small-`b` law has failed by `b = 8`, and the rounding margin
is gone below `b = 28`. That band is the whole remaining gap for divisor-closed profiles, and it is
finite in `b` — which is the reason to think it is reachable.
