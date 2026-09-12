# Workbook — window trajectories along a path

2026-09-12. n = 8, individual isolation. Tests the item left open in
`WB_interaction_structure_2026_09_12` §7: which individual windows slide, split or merge as a
speed varies continuously. BSM, exact.

## 0. An error in the first attempt

The first run reported window counts of 4, 158, 78, 50, 40, 160, 26, 160, 20, … as the speed
advanced in steps of `1/24` — apparently chaotic. **The chaos was the axis, not the
trajectory.** Windows were being printed in *scaled* time: reducing a configuration with
denominator 24 stretches its period by 24, so that row reports windows over a span 24× longer
than a denominator-1 row. This is the same cycle-versus-count confusion corrected earlier for
counts (`TRANSIT_FRACTIONAL_v1`), repeated here for windows. Everything below is in original
time on a fixed interval.

## 1. Design

Runner 1 of the AP has constraint set `{1,2,3,4,5,6,7}`. Varying only r8 changes exactly one
of these, so

    D(d) = {1,2,3,4,5,6} ∪ {7+d}

with the **fixed part** `A = G_{1,…,6}` constant throughout: 8 windows, measure 7/80 = 0.0875,

    [1/8,7/48] [9/32,7/24] [3/8,3/8] [17/40,7/16] [9/16,23/40] [5/8,5/8] [17/24,23/32] [41/48,7/8]

All motion comes from the single sliding constraint.

## 2. What happens  `[VERIFIED — exact]`

Tracking the window nearest `t = 1/8` as `7+d` increases:

| `7+d` | window | width |
|---|---|---|
| 7 | `[0.12500, 0.12500]` | 0 |
| 175/24 | `[0.29143, 0.29167]` | 0.00024 |
| 22/3 | `[0.28977, 0.29167]` | 0.00189 |
| 59/8 | `[0.28814, 0.29167]` | 0.00353 |
| 15/2 | `[0.28333, 0.29167]` | 0.00833 |
| 91/12 | `[0.28125, 0.29167]` | 0.01042 |
| 23/3 … 185/24 | `[0.28125, 0.29167]` | 0.01042 (clamped) |
| 31/4 | `[0.14516, 0.14583]` | 0.00067 (new window) |
| 8 | `[0.14062, 0.14583]` | 0.00521 |

> **A window is the intersection of a fixed `A`-component with a sliding bad interval.
> One endpoint is fixed, the other slides.**

- The right endpoint `0.29167 = 7/24` is a boundary of `A` and does not move.
- The left endpoint slides continuously as the moving constraint's bad interval retreats.
- Growth stops at `0.28125 = 9/32`, `A`'s own left boundary — the window **clamps** at the
  full `A`-component and cannot grow further.
- A new window then nucleates in a different `A`-component (at 31/4, near `7/48 = 0.14583`)
  and repeats the pattern.

Window counts over `t ∈ [0,1]` run 4, 3, 5, 6, 7, 7, 7, 7, 7, 7, 6, 6, 6 — windows appear and
vanish as the sliding interval enters and leaves `A`-components.

## 3. The measure jump at the AP, explained

At `7+d = 7` exactly, the four surviving windows are single **points**: `0.125, 0.375, 0.625,
0.875`. The moving constraint's bad interval abuts each `A`-component exactly, clipping it to
one endpoint. That is the "exact tiling" predicted in
`WB_interaction_structure_2026_09_12` §7, now confirmed: **at the AP the bad intervals close
`A`'s components down to points, and any perturbation reopens them**, which is why the measure
jumps from 0 to generic immediately (`AP_GRID_SUMMARY_v1` §2).

## 4. Status

`[VERIFIED — exact]` §2's trajectory and clamping; §3's tiling.
`[RECORDED]` §0's scaled-time error.

Both predictions in `WB_interaction_structure_2026_09_12` §7 held — continuous sliding with
appearance/disappearance, and the tiling account of the jump — but the mechanism is more
specific than predicted: one endpoint of every window is inherited from the fixed part and
never moves.

**n = 8 is not proved.**
