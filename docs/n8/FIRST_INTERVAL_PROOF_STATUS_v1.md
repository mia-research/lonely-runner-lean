# The first-interval claim — reformulation, and why measure arguments are dead

2026-09-13. n = 8, individual isolation, threshold 1/8. Work on the one remaining unproved link
of `ANALYTIC_STATUS_v1`.

---

## 1. Reformulation — one relative revolution

For runner `i`, put `m = d_min(i)`, `u = m·t`, and `s_j = d_j/m` so that `s_1 = 1`. The interval
`I = [1/(8m), 7/(8m)]` becomes `u ∈ [1/8, 7/8]`, and the claim reads:

> **Given any `s_2, …, s_7 ≥ 1`, there is `u ∈ [1/8, 7/8]` with `‖s_j u‖ ≥ 1/8` for all `j`.**

Equivalently: **loneliness always arrives within the first relative revolution against the
nearest-in-speed runner.** The circle picture, as a theorem.

## 2. It has room  `[VERIFIED — 4,800 runner-instances]`

| | |
|---|---|
| minimum good measure inside `I` | `5/168 ≈ 0.0298` of `|I|` |
| median | 0.1831 |
| naive independence estimate `(3/4)⁶` | 0.1780 |
| zero-measure cases in the random population | 0 |

And the moment lands early:

| | min | median | 90th | **max** |
|---|---|---|---|---|
| `u = m·t*` | 0.1250 | **0.1250** | 0.1731 | **0.4464** |

Against an interval ending at `0.875`. The worst case found is
`(4,5,6,9,12,13,16,17)`, runner r5, `s = {1,3,4,5,6,7,8}`, with `u = 25/56`.

## 3. But measure arguments are impossible  `[PROVED]`

The AP is the extremal case, and there the good set inside `I` is

    { 1/8, 3/8, 5/8, 7/8 }        — four isolated points, total measure 0.

So **no bound of the form "the bad sets have too little measure to cover `I`" can work**, at any
strength. The union bound failing by `3/2` was not the obstacle; the obstacle is that the quantity
such a bound would bound below is **zero** in the case that matters. `AP × 2` in `s` is the same —
measure 0, six boundary points.

This is the zero-measure fragility of the φ(n) law reappearing as an obstruction to a proof
technique rather than as a property of a configuration.

**A proof must be pointwise: it must construct a witness `u`.**

## 4. Where the witness is  `[PROVED for the unblocked case]`

For integer `s`, take `u = p/8` with `gcd(p,8) = 1`. Then `s·p/8` has denominator dividing 8, and
`‖s p/8‖ ≥ 1/8` **unless `s ≡ 0 mod 8`**.

| case | witness | status |
|---|---|---|
| not blocked | `u = 1/8` (a spine point) | **proved** — this is the whole clean case |
| blocked | `1/8` fails; another point needed | **open** |

In the worst case found, `s = {1,3,4,5,6,7,8}`, the `s = 8` constraint kills every spine point and
the witness moves to `u = 25/56`, which sits on the boundary of the `s = 7` constraint
(`7 × 25/56 = 25/8`, `‖25/8‖ = 1/8` exactly).

So the open problem is now: **when the spine fails, construct the replacement.** A construction
question, not a counting one.

## 5. Status

`[PROVED — arithmetic]` §1's reformulation; §4's witness for the unblocked case; §3's obstruction.
`[VERIFIED — 4,800]` §2's measures and positions.
`[OPEN]` the claim itself, for blocked runners.

**Not established.** Any construction for the blocked case. Whether the maximum `u` is bounded
below `7/8` by more than the observed `0.4464`. The owner's conjecture that the iteration's step
count is governed by speed and spread through `mod n` — untested.

**n = 8 is not proved here.**
