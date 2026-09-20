# The grand return — the pack keeps its rigidity, and the displaced runner lives off it

2026-09-12. n = 8, individual isolation, threshold 1/8. Base AP `(1,…,8)`, one runner
displaced. Corrects the frame used in `FULL_SWEEP_v1` and `TRANSIT_PERIODS_v1`, where the cycle
was treated as a normalisation rather than as a structure.

---

## 1. Two rigid events, not one

A grid has **two** exactly-simultaneous events, and they are opposite extremes.

**Global isolation.** At `t = p/(ng)`, `gcd(p,n) = 1`, every runner is lonely at once — the
`φ(n)` spine.

**The grand return.** At `t` with every `v_i t ∈ ℤ`, every runner is back at 0 *together*. This
is maximum crowding, and no runner is lonely there at all.

For the AP `(1,…,8)` the grand return is `t ∈ ℤ` and the cycle is `[0,1)`. Within it sit the
eight eighth-lattice points; global isolation occupies the four odd ones:

| t | 0 | 1/8 | 1/4 | 3/8 | 1/2 | 5/8 | 3/4 | 7/8 | 1 |
|---|---|---|---|---|---|---|---|---|---|
| all at 0 | **yes** | | | | | | | | **yes** |
| globally isolated | | **yes** | | **yes** | | **yes** | | **yes** | |

The cycle runs from total collapse at 0, out through the four spine instants, back to total
collapse at 1. The grand return is as rigid as the spine, and it is the other end of the same
structure.

## 2. Displacing a runner does not break the pack's rigidity  `[VERIFIED — exact]`

This is the point the earlier work missed. With `r1 = 11/10`, the **seven unmoved runners keep
returning to 0 at every integer `t`** — their own rigidity is untouched. Only the displaced
runner fails to join, until the full cycle closes at `t = 10`.

So one full cycle contains many **partial grand returns**: the pack reassembles at 0 without
the mover, over and over.

| t | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| r2…r8 | all 0 | all 0 | all 0 | all 0 | all 0 | all 0 | all 0 | all 0 | all 0 | all 0 | all 0 |
| r1 position | 0 | 1/10 | 1/5 | 3/10 | 2/5 | 1/2 | 3/5 | 7/10 | 4/5 | 9/10 | 0 |
| **r1 lonely** | no | no | **yes** | **yes** | **yes** | **yes** | **yes** | **yes** | **yes** | no | no |

At the pack's reunion the mover sits at `εt mod 1`, walking through every multiple of `1/q` as
`t` advances. It is lonely exactly when `‖εt‖ ≥ 1/8`.

## 3. The displaced runner harvests the pack's reunions  `[VERIFIED — exact]`

| mover | speed | full cycle `T` | pack reunions | mover lonely at | share | any unmoved runner lonely |
|---|---|---|---|---|---|---|
| r1 | 11/10 | 10 | 10 | 7 | 0.70 | **0** |
| r1 | 13/10 | 10 | 10 | 7 | 0.70 | **0** |
| r1 | 17/10 | 10 | 10 | 7 | 0.70 | **0** |
| r1 | 101/100 | 100 | 100 | 75 | 0.75 | **0** |
| r1 | 3/2 | 2 | 2 | 1 | 0.50 | **0** |
| r4 | 43/10 | 10 | 10 | 7 | 0.70 | **0** |
| r8 | 87/10 | 10 | 10 | 7 | 0.70 | **0** |
| r8 | 17/2 | 2 | 2 | 1 | 0.50 | **0** |

Two things hold in every row.

**No unmoved runner is ever lonely at a pack reunion.** They are stacked on 0; the count is
exactly zero, not small.

**The mover's share approaches 3/4**, the measure of the lonely band `[1/8, 7/8]`: `0.50` at
`q = 2`, `0.70` at `q = 10`, `0.75` at `q = 100`. At an irrational displacement there is no
full grand return at all, the pack still reunites at every integer, and `εt mod 1`
equidistributes — so the share is exactly `3/4` by Weyl.

## 4. What this says about leaving the AP

The displaced runner **gains a family of isolation windows sitting exactly on the unmoved
pack's reunion times** — the moments of maximum crowding, when no other runner can be lonely at
all. The pack's rigidity, which is what made the AP hard, works *for* the runner that leaves it.

This is consistent with what was measured before and not understood: across every transit the
**mover is never the binding runner**. Its longest-window floor was `25/233 ≈ 0.107` against the
stationary runners' `1/48 ≈ 0.021` — a factor of five. §3 is why. The runner being displaced is
the safest runner in the configuration, because it is the only one not participating in the
pile-up.

It also reframes the spine/reserve exchange: a displaced runner loses the spine, and what it
receives is not generic reserve but this specific harvest.

## 5. Correction to the earlier frame

`FULL_SWEEP_v1` and `TRANSIT_PERIODS_v1` computed the period as `1/gcd(differences)` and used
it only to make durations comparable. That number **coincided** with the grand return in every
configuration in those sweeps — checked, `T = P` in all cases tested — so no reported quantity
is wrong. But the two are different notions and they separate elsewhere: speeds `(3,5)` have
grand return 1 and isolation period `1/2`. Treating the cycle as a normalisation hid the
structure in §2, which the same data contained all along.

## 6. Status and scope

`[VERIFIED — exact]` §1's AP table; §2's reunion table; §3's eight rows.
`[PROVED | Weyl]` the irrational limit of `3/4` in §3.
`[CORRECTED]` §5 — frame, not figures.

**Scope.** One base, the AP. Single displaced runner. Rational displacements with `q ∈
{2,10,100}` and three different movers. Not tested: several runners displaced at once, non-AP
grids, non-grid bases. §3's share is a count over reunion instants, not over the whole cycle,
and says nothing about the windows between them.

**Not established.** The width of the mover's windows at the reunions, as against merely
whether the reunion instant is inside one. How the harvest interacts with the reserve the mover
already had. Whether anything here extends to two movers, where the two would have separate
reunion structures.

**n = 8 is not proved here, and is not the target here.**
