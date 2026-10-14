# The vacancy frame — deviation from the reference as a combinatorial object

2026-09-12. n = 8, individual isolation. No moduli, no witnesses, no measure bounds.

Prompted by the observation that previous notes kept reaching for modulus machinery to
carry an argument the reference/transit frame was supposed to carry itself.

## 1. The parametrisation

Every 8-set of integer speeds is, after translation and division by the gcd, a subset of a
grid `{0, 1, …, M−1}` for some `M ≥ 8`. So

> **an arrangement = a grid, plus the set of grid points left vacant.**

`M = 8` and no vacancies is the reference (the AP / complete residue system). Deviation from
the reference **is** the vacancy pattern. This is the owner's "any arrangement is a
permutation/deviation from AP or grid" as a finite combinatorial object rather than a
coordinate change.

The isolation invariant is the event count — the number of components of `G_D` — which by
the palindrome (`WN_count_parity` Step 2) is even whenever any constraint is even, so it
counts **mirror pairs**.

## 2. The reference and the first vacancy

Reference `{0..7}`: counts `[4, 8, 8, 6, 6, 8, 8, 4]`, total 52. The extremes sit at
`φ(8) = 4` — two mirror pairs.

One vacancy, from the 9-grid `{0..8}` — drop each point in turn:

| vacancy at | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|---|
| total | 52 | 52 | **44** | 50 | 52 | 50 | **44** | 52 | 52 |
| worst runner | 4 | 2 | 2 | 4 | 4 | 4 | 2 | 2 | 4 |

Symmetric under `x → 8−x`, as it must be. Dropping an endpoint returns the reference.
The worst runner falls from 4 to 2 — **two mirror pairs to one**.

## 3. The cost saturates  `[VERIFIED — exhaustive, M ≤ 16]`

All 8-subsets of `{0..M−1}`, primitive, worst runner over the eight:

| `M` | vacancies | subsets | min worst-runner count | minimiser |
|---|---|---|---|---|
| 8 | 0 | 1 | 4 | `(0,…,7)` |
| 9 | 1 | 9 | **2** | `(0,1,2,3,4,5,6,8)` |
| 10 | 2 | 45 | **2** | `(0,1,2,3,4,5,6,8)` |
| 11 | 3 | 165 | **2** | `(0,1,2,3,4,5,6,8)` |
| 12 | 4 | 495 | **2** | `(0,1,2,3,4,5,6,8)` |
| 13 | 5 | 1,287 | **2** | `(0,1,2,3,4,5,6,8)` |
| 14 | 6 | 3,003 | **2** | `(0,1,2,3,4,5,6,8)` |
| 15 | 7 | 6,434 | **2** | `(0,1,2,3,4,5,6,8)` |
| 16 | 8 | 12,868 | **2** | `(0,1,2,3,4,5,6,8)` |

**The minimiser never changes.** Enlarging the grid — i.e. allowing more and wider deviation
— gives the adversary nothing. The first vacancy costs one mirror pair and subsequent
vacancies do not compound.

Distribution of the worst-runner count confirms the direction of travel:

| `M` | 9 | 10 | 11 | 12 | 13 | 14 | 15 |
|---|---|---|---|---|---|---|---|
| share at 2 | 44% | 24% | 15% | 11% | 9% | 8% | 7% |
| share at ≥ 6 | 0% | 16% | 29% | 38% | 42% | 46% | 53% |

Mass moves **up** as vacancies are added. More deviation makes almost every arrangement
easier while a shrinking minority stays pinned at the floor. This is the owner's
"a low point of individual isolation points, but it can't escape before getting better",
measured in the invariant that carries it.

## 4. What was wrong with the earlier reading

Two corrections to today's own work, both from over-reading a one-dimensional slice:

- *"The AP minimises the total event count."* False. Both transits in
  `MMIN_RETRACTION_v1` §4 bottom at 52 and the AP sits at 52, but `(0,1,2,3,4,5,7,8)` has
  total **44**. A transit moves one runner, so it never visits that set. Exhaustive over
  `[0..16]`, 24,300 sets: minimum total is 44, not 52.
- *`mmin` as a difficulty measure.* Retracted separately in `MMIN_RETRACTION_v1` §1.

## 5. The statement, in this frame

> **No vacancy pattern takes a runner to zero mirror pairs.**

That is LRC(8), expressed in the vacancy object rather than in moduli. It is not a
reduction. What the frame supplies that the modulus framing did not:

- a finite object per grid size (`C(M,8)` vacancy patterns) rather than a residue condition;
- a fixed extremal configuration, the same at every `M ≤ 16`;
- a direction — added vacancies push the distribution up, never down.

What it does not supply: any reason the floor cannot be 0 at some `M > 16`.

## 6. Status

`[VERIFIED — exhaustive]` §2's table; §3's nine rows and the distributions, `M ≤ 16`.
`[PROVED]` the palindrome / parity law it rests on (`WN_count_parity` Step 2).
`[RETRACTED]` "the AP minimises the total", asserted earlier this session from a transit.

n = 8 is **not proved**.
