# Every percentage explained, and density dropped

Answering two challenges from the owner: **is density the object we need**, and **does every stated
fraction have its complement explained, rather than accepted as failure**. Answers: no, and it does
now.

## Density was the wrong object

We need **one** `q`, not many. Density measures abundance, and `UNION_ROUTE_v1.md` established that
abundance fights us here: the joint density sits **below** the product of conditionals (ratio as low
as `0.716`), so the constraints reinforce one another's badness. An abundance argument is therefore
the worst available frame, not the natural one. Density was reached for because it is the shape a
counting proof takes, not because the problem asks for it.

Dropped. The object is the witness. Every density figure previously quoted stands as a measurement
and is load-bearing for nothing.

## The complement, fully accounted

Three constructions produce **extremal** witnesses, via `q = m·x/8`:

| construction | `x` | integral iff | coverage |
|---|---|---|---|
| spine | `u` odd in `{1,3,5,7}` | `8 ∣ m` | 6.51% |
| right endpoints | `(8k+1)/s` | `8 ∣ b` | 38.15% |
| left endpoints | `(8k−1)/s` | `8 ∣ b` | **0.00%** |
| any of the three | | | **38.83%** |
| none | | | **61.17%** |

**The 0% is a theorem, not a shortfall.** The two endpoint families give
`q mod b = b/8` and `q mod b = b − b/8` respectively (verified: 0 exceptions in 3,744 cases). Both
need `8 ∣ b` to be integral. And `Involution.reflect_fails_zero` says precisely that at `b ≡ 0
(mod 8)`, `r = b/8` clears while `b − b/8` does not — verified `624/624` and `0/624`. So the
left-endpoint family is integral **only** where it is blocked by its own modulus. It can never
contribute.

**The 61.17% is one phenomenon, not three.** It was previously split into 43.91% (`8 ∤ m`, no
`8 ∣ bᵢ`), 11.16% and 6.11%, with only the first explained. Checked directly on the other two: in
1,500 class-A and 1,392 class-B profiles, the witness is **never** of the form `(8k+1)/s` for any
speed. So:

> The three constructions succeed exactly when an integral witness of **extremal** form exists. In
> all 61.17% where they fail, every integral witness is **interior** — and that is forced, not
> incidental.

Nothing is left as an accepted failure.

## What this says about the target

Extremal witnesses are now **exhausted**: spine, right endpoints and left endpoints are the complete
extremal supply, they are integral only under `8 ∣ m` or `8 ∣ b`, and one of the three is foreclosed
by the reflection obstruction. 38.83% is the ceiling for that entire family.

So any proof of this category must produce an **interior** witness by some means that is not an
endpoint of a bad interval and not a counting bound. Both of those families are now closed with
reasons:

- **extremal witnesses** — exhausted at 38.83%, by the table above;
- **counting / abundance** — adverse correlation, `UNION_ROUTE_v1.md`;
- **bounded centre offset** — offset grows with `m`, `INTEGRALITY_OBSTRUCTION_v1.md`.

The reflection remains the only proved tool acting on the whole solution set. It has now been used
once as an *obstruction* (explaining the 0%); it has not been used constructively.
