# Why the replacement witness is local

2026-09-12. n = 8, individual isolation. Follows `FORWARD_MECHANISM_v1.md` §4, which observed
that when a move destroys a witness the replacement appears **close by** (95% within `1/8`)
and noted that nothing explained it.

## 1. Two regimes

A move changes one constraint `d → d'`. The old witness `t` still satisfies the other six, so
`t ∈ A = G_F`, and it fails only `d'` — meaning `t` sits **inside a bad interval of `B_{d'}`**,
which has width exactly `1/(4d')`.

**Regime 1 — escape the bad interval.** Reaching its nearer edge costs at most `1/(8d')`. If
`A`'s component containing `t` extends that far, the replacement is within `1/(8d')`.
`[PROVED]`

**Regime 2 — leave the component.** If `A`'s component is shorter than the bad interval, the
witness must move to a different component of `A`, and `1/(8d')` no longer bounds anything.

Measured over 3,107 cases where a witness was killed by the new constraint:

| bound | coverage |
|---|---|
| `jump ≤ 1/(8d')` — regime 1 | **57.0%** |
| `jump ≤ 1/max(F)` — spacing of `A`'s components | 88.9% |
| `jump ≤ max` of the two | **92.3%** |

Median ratio of the jump to `1/(8d')` is **0.818** — in regime 1 the jump is about
eight-tenths of a half-width, exactly as the picture predicts. The 238 violations of
`max(B1,B2)` reach ratio 4 and cluster at **small** `d'` (4, 8, 13), where the new
constraint's bad intervals are wide and widely spaced.

## 2. The governing quantity is the maximum gap

Regime 2 is really a statement about `G_D` having no long empty stretches: a killed witness is
never further from a replacement than the largest gap in the new good set.

Testing `gap × d_max` — the parameter P3/P4 use — it is **not** bounded:

| box | `[1..12]` | `[1..18]` | `[1..26]` | `[1..40]` | `[1..80]` |
|---|---|---|---|---|---|
| max `gap × d_max` | 7.25 | 10.40 | 9.29 | 11.35 | **18.59** |

The extremal sets there all begin with small elements — `(2,5,16,40,45,59,70)`,
`(2,12,23,55,61,63,77)`. The gaps are made by the *small* constraints, whose bad intervals are
widest (`1/(4d)`), not by the large ones.

Testing `gap × d_min` instead:

| box | `[1..12]` | `[1..20]` | `[1..40]` | `[1..80]` | `[1..160]` |
|---|---|---|---|---|---|
| max `gap × d_min` | 1.562 | 1.803 | 1.986 | 2.179 | **2.394** |
| `gap ≤ 1/d_min` | 94.5% | 95.2% | 95.1% | 92.3% | 89.7% |

Bounded, and growing slowly — roughly like `log` of the box rather than linearly. So

> **max gap of `G_D` ≈ `C/d_min`, with `C ≈ 2.4` over these ranges.**

The extremal sets are **dense clusters of near-equal constraints**:
`(2,3,4,5,6,7,8)`, `(7,8,9,11,12,15,19)`, `(22,27,28,29,34,35,36)`,
`(52,53,58,60,63,66,73)`, `(109,112,131,134,141,143,148)`. When all seven constraints are
close together their bad sets nearly coincide and merge into one wide stretch — that is what
makes a long gap.

## 3. The answer

The replacement is local because **`G_D` has no gap longer than about `2.4/d_min`**, and a
killed witness is at most one gap from a component. Decomposed:

- 57% of the time the witness never leaves its component — it escapes the new bad interval, a
  distance of at most `1/(8d')`. This part is proved.
- The rest is governed by the gap bound, which is measured, not proved, and whose constant
  drifts upward with the range.

This also explains the `1/8` figure from `FORWARD_MECHANISM_v1`: `1/8` is roughly `C/d_min`
for the small `d_min` typical of the sampled boxes, not a universal constant.

## 4. What is not established

`C ≈ 2.4` is a measurement over boxes to `[1..160]`, and it rose monotonically across every
box tested (1.56 → 2.39). It may be unbounded; nothing here excludes that. The dense-cluster
structure of the extremal sets suggests where to look — the same dense region that carries the
count-2 minimisers (`PINNED_SET_v1`).

For `d_min = 1` the bound is vacuous, and `d_min = 1` is common among the hard configurations.

## 5. Status

`[PROVED]` §1's regime-1 bound `1/(8d')`, with derivation.
`[VERIFIED]` §1's coverage table, 3,107 cases; §2's two parameter tables, ~4,000 sets.
`[OPEN]` whether `gap × d_min` is bounded at all; the constant is drifting.

**n = 8 is not proved.**
