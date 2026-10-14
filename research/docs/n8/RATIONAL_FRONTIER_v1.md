# The rational frontier, characterised — and Branch B resists named rules

Two results, one negative and one positive, both on live frontiers.

## Negative: no named-candidate rule closes Branch B

Branch A's proof is a **group orbit**: at `x = u` odd, `8 ∤ su` for every unit `u` at once, so all
four spine points clear together (`Guard.odd_clear_of_not_dvd`). The unit group `{1,3,5,7}` is the
Klein four-group, every element self-inverse (`Guard.klein_self_inverse`) — the same inversion
structure that recurs in the guard relation `sR ≡ 1 (mod 8)` and in `clear_reflect`'s `r ↦ b − r`.

Tested whether a single **named** candidate closes any Branch B sub-category, exhaustively over
80,332 profiles with readings in `[2,25]`:

| rule | all Branch B | collider = `s_max` | pairwise coprime |
|---|---|---|---|
| first candidate of the collider | 32.00% | 37.05% | 22.55% |
| first candidate of `s_max` | 19.61% | 23.47% | 24.02% |
| first candidate of 2nd largest | 29.31% | 28.93% | 33.82% |
| first candidate of largest odd | 16.34% | 19.86% | 25.49% |
| **any of the four** | **59.49%** | 59.45% | 62.99% |

No sub-category reaches 100%, under any rule or their union. The spine rule correctly gives **0%**
throughout — the collider kills every spine point, exactly as the theory says. **Branch B does not
fall to a rule of this shape.**

*(A first version of this scan reported 100% everywhere. Its "endpoint" rule searched every reading
and every level — that is the entire candidate set, so it was restating `finite_check`, not testing a
mechanism. Recorded because the circularity was not obvious from the output.)*

## Positive: what the rational frontier actually is

Readings `sᵢ = dᵢ/d_min` are **ratios**, hence scale-invariant — scaling the speeds cannot make them
integers. But clearing denominators moves the question into the speeds: with `Q` the lcm of the
readings' denominators, `sᵢ = aᵢ/Q` and

    ‖sᵢ·t‖ ≥ 1/8   ⟺   ‖aᵢ·τ‖ ≥ 1/8,   τ = t/Q

— an identity. Since `s₁ = 1`, `a₁ = Q`, and `sᵢ ≥ 1` gives `aᵢ ≥ Q`. Hence:

> **Integer readings ⟺ the reduced integer speed set contains `1`.**
> **The rational-reading frontier is exactly: speed sets with no unit speed.**

**Verified: 200,000 random 7-element speed sets, 0 mismatches.**

So the map's two branches — "integer readings" and "rational readings" — are not two kinds of
mathematics. They are one question split by whether `1` survives reduction.

## What the rational side costs — exactly one theorem

Of the theorems this work rests on, **only one mentions the unit**:

| theorem | survives without a unit speed? |
|---|---|
| `BlockerCount.unit_never_blocks` | **no** |
| `BlockerCount.self_never_blocks` | yes |
| `Rescale.gcd_covariant` | yes |
| `Rescale.rescaled_blocks_iff` | yes |
| `Rescale.divisor_reduces` | yes |
| `Rescale.small_b_blocks_iff` | yes |
| `Involution.clear_reflect` | yes |
| `Involution.reflect_fails_zero` / `_one` | yes |

And the loss is real, not formal: **a minimum speed `> 1` blocks 21.94% of candidates** (measured
over 10.5 million candidate/speed pairs). It is a genuine blocker, so the blocker count rises from
`n − 3` back to `n − 2`.

**That is the whole cost of the rational frontier**, stated precisely: one theorem, and the blocker
count. Everything else transfers unchanged, including the entire reflection apparatus.

## Correction

An equivalence check in the first pass reported 2,248 mismatches out of 2,261. That was a coding
fault — one search ran in `t`-space and the other in `τ`-space, and they were compared directly. The
reduction is an algebraic identity and cannot fail.
