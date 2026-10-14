# Running the framework forward from the reference — the mechanism, and its provable core

2026-09-12. n = 8, individual isolation. Complement to `CASE_B_MAP_v1.md`, which classified
configurations backward. This note starts at the reference and asks what a move *does*.

## 1. The question

At the reference `{0,…,7}` every runner is lonely at `t = p/8`, `p` odd. Apply single moves.
Track a **specific witness** rather than a statistic:

- does it survive the move?
- if not, does the replacement appear nearby (local refinement) or somewhere unrelated?

Only the first answer matters for LRC; the second is what would let the mechanism be iterated.

## 2. What a move does  `[VERIFIED]`

1,197 single moves, from arbitrary configurations in grids `{0..11}`, `{0..15}`, `{0..21}`,
witness held by a runner that does **not** move:

| outcome | count | share |
|---|---|---|
| witness survives the move | 873 | **72.9%** |
| witness lost | 324 | 27.1% |
| good set became **empty** | **0** | 0% |

When lost, distance from the old witness to the nearest new one:

| min | median | mean | max |
|---|---|---|---|
| 0.00038 | 0.02170 | 0.03854 | 0.28259 |

77.5% of jumps are below `1/16`, 95.1% below `1/8`. Of the 324 losses, 171 landed in Case B
(the move created a difference `≡ 0 mod 8`).

Traced along explicit paths from the reference, the pattern is visible directly: `1/8`
survives move after move until a difference divisible by 8 appears, then refines —
`1/8 → 3/16 → 17/88`, jumps `1/16` then `0.0057`.

**So the mechanism is: a move either preserves the witness or displaces it a short distance,
and it never empties the good set.**

## 3. The provable core, and its size  `[PROVED, but nearly vacuous]`

A move changes exactly one constraint, `d → d'`. The old witness `t` still satisfies the six
unchanged constraints, so `t ∈ A = G_F`. Inside the component of `A` containing `t`, the bad
set `B_{d'}` consists of intervals of width `1/(4d')` spaced `1/d'` apart, so it leaves gaps
of length `3/(4d')` every `1/d'`. Hence

> **if the component of `A` containing `t` has length ≥ `1/d'`, a replacement exists in that
> same component, within `1/d'` of `t`.** The move cannot kill the runner.

Sound — but it almost never applies. Over 2,003 `(A, d')` pairs:

| | count | share |
|---|---|---|
| criterion fires | 3 | **0.1%** |
| fires and runner died anyway | **0** | — |
| criterion silent | 2,000 | 99.9% |
| silent and runner survived anyway | 2,000 | **100%** |

The reason is structural and already familiar. Components of `A` are at most `3/(4·max F)`
(`P3_P4_AUDIT_v1` §1), so the criterion needs `d' ≥ 4·max(F)/3` — the *new* constraint must
dominate the existing ones. That is the same condition under which P4 was sharp and outside
which P4 was vacuous (`MEASURE_LEMMA_ATTEMPT_v2` §1).

## 4. Reading

Running the framework forward reaches the same obstruction as running it backward, and the
obstruction is one inequality: **arguments of this shape need the new constraint to be large
relative to the old ones, and the hard configurations are exactly those where it is not.**

Three separate routes have now hit it — P4's count bound, the measure lemma, and this local
move criterion. That is worth recording as a property of the problem rather than of any one
attempt.

What the forward view does add over the backward one: the never-empty result here is about
*moves* (1,197 of them, 0 empties) rather than configurations, and the jump distribution is
new — it says the witness does not merely exist after a move, it exists **close by**, 95% of
the time within `1/8`. No argument yet explains that locality.

## 5. Status

`[PROVED]` §3's criterion, with derivation; 0 counterexamples in 2,003 pairs.
`[VERIFIED]` §2's 1,197 moves and jump distribution; §3's coverage figures.
`[OPEN]` why the replacement is local. The observed jump bound has no proof.

**n = 8 is not proved.**
