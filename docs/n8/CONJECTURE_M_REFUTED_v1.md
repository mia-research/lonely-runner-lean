# Conjecture M is false — the least witnessing modulus is not absolutely bounded

2026-09-12. Refutes `PROOF_CANDIDATE_v2.md` §3. n = 8, individual isolation.

## 1. What was conjectured

> **Conjecture M.** There is an absolute `M₀` such that every runner in every 8-set has a
> witness at some modulus `m ≤ M₀`. Evidence put `M₀` at 29.

v2 §1 showed Conjecture M would make LRC(8) a finite condition on `u mod lcm(1..M₀)`.
The conjecture was supported there by three probes: random sets to `10⁹`, the `lcm(1..k)`
adversary to `k = 18`, and exhaustive boxes to `[0..18]`. All three capped at 29.

## 2. Counterexample  `[VERIFIED — exact integer arithmetic]`

    V = (0, 49920, 60375, 76415, 86086, 86184, 156251, 220174)

Eight distinct speeds. Runner 1 (speed 0) has constraint set

    D = (49920, 60375, 76415, 86086, 86184, 156251, 220174),   gcd(D) = 1

Checking **every** rational `a/m` in lowest terms with `m ≤ 43` — all `a`, not only units:

> **witnesses at any denominator `m ≤ 43`: 0.**

First witness is `t = 5/44`. So runner 1 is lonely — LRC is not threatened — but at no
denominator below 44. `M₀ = 29` is refuted, and so is any `M₀ ≤ 43`.

The set is otherwise unremarkable: its other seven runners have least witnessing moduli
`9, 6, 13, 10, 11, 7, 13`. The difficulty is carried by one runner.

## 3. Why the three probes missed it

A random primitive `D` fails every `m ≤ M` with probability roughly
`(1 − (3/4)⁷)^{Σ_{m≤M} φ(m)} ≈ 0.867^{256} ≈ 3 × 10⁻¹⁷` at `M = 29`. Uniform sampling at
300 sets per scale cannot reach that. The counterexample was found by hill-climbing on
`mmin` directly, and only once the search range was widened past `[1..400]` — the apparent
ceiling at 29 was a property of the search box, not of the problem.

## 4. Growth with scale  `[VERIFIED — search, not proof]`

Hill-climb on `mmin`, `D` drawn from increasing ranges:

| `D` drawn from | restarts | best `mmin` |
|---|---|---|
| `[1..400]` | 250 | 31 |
| `[1..3000]` | 250 | 33 |
| `[1..30000]` | 200 | 39 |
| `[1..300000]` | 150 | 44 |
| `[1..3×10⁶]` | 120 | 43 |

Monotone apart from the last row, where the search is weakest relative to the space.
This indicates `mmin` is unbounded, and is not a proof of it.

## 5. The structural reason  `[PROVED]`

A single constraint `d` has good-set components of length exactly `3/(4d)`. Hence

> the largest component of `G_D` is at most `3/(4·max D)`.

As the speeds grow, every component of the good set shrinks to zero. The Farey gap bound —
an interval of length `L` contains a rational of denominator `≤ ⌈1/L⌉` — therefore yields
only `M₀ ≤ ⌈4·max(D)/3⌉`, which is unbounded. **Component length cannot bound the
witnessing modulus**, and any route to a bounded `M₀` would have had to argue about where
the thin components sit rather than how wide they are.

This is a one-line obstruction and it was available before any search was run.

## 6. Consequence for the proof candidate

`PROOF_CANDIDATE_v2` §3 reduced the whole remaining gap to Conjecture M. That reduction was
sound; the conjecture is false. So the v2 architecture does not close, and the finite-state
observation of v2 §1 — true as stated — has no bounded `M` to apply to.

What survives unaffected:

- v2 §1's correction of the dimensionality framing: loneliness reads the speeds only through
  `u mod m`, so there is no unbounded base to induct over. Still true, still the right frame.
- S1–S6 of the architecture, all still proved. Their measured coverage (94.13%, or 96.51%
  with an unproved constant) is unchanged.
- `WN_reference_collapse` §2: thin good sets collapse onto the reference. Unaffected.

What is retracted: v2 §3, and the claim that the remaining gap is a single statement about
one bounded quantity.

## 7. Status

n = 8 is **not proved**. §2 and §5 are exact. §4 is a search result reported as such.
No grade moves up; v2 §3 moves down to refuted.
