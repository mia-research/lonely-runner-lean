# Working note — the resolution law, and the transit reduced to a finite check

2026-09-12. n=8 only. Continues `WN_transit_periodicity_2026_09_12.md`.

## 1. Setup

Along a transit, runner `i`'s constraint set is a **fixed part** `F` (the six
differences among the seven stationary runners) plus **one moving difference** `e`.
Write

    G_F   = { t : ||f t|| >= 1/8 for all f in F }         the fixed good set
    G(e)  = { t : same, and ||e t|| >= 1/8 }              after the slider arrives
    N_F   = number of components of G_F

Resolution = the measure `|G(e)|`, and where that degenerates, the component count.

Script: `experiments/n8/resolution_law.py`.

## 2. The 3/4 law  [MEASURED, ratio 1.0000]

The bad set of `e` is `e+1` intervals of width `1/(4e)` centred at the points `k/e`.
As `e` grows these equidistribute against `G_F` and remove a quarter of it:

    |G(e)| -> (3/4)|G_F|

Measured tail ratio (`e` in 161..240) against `(3/4)|G_F|`:

| fixed part | `(3/4)|G_F|` | tail ratio |
|---|---|---|
| AP r1/r7 `{1,2,3,4,5,6}` | 0.065625 | 1.0005 |
| AP r2/r6 `{1,2,3,4,5}` | 0.109375 | 1.0001 |
| AP r3/r5 `{1,2,3,4}` | 0.250000 | 1.0000 |
| AP r4 `{1,2,3}` | 0.343750 | 1.0000 |
| E* r1 `{2,6,7,8,10,13}` | 0.032795 | 1.0004 |
| E* r7 `{3,5,6,7,11,13}` | 0.116040 | 0.9991 |
| E* r4 `{1,3,5,6,7}` | 0.151190 | 0.9997 |

## 3. The error bound  [PROVED]

Over a component of `G_F` of length `L`, the number of centres `k/e` lying in it is
`Le ± 1`, so the measure removed is `L/4 ± 1/(2e)`. Summing over the `N_F`
components:

> **|G(e)| >= (3/4)|G_F| - N_F/(2e).**

Check of the constant against the measured `sup_e e·| |G(e)| - (3/4)|G_F| |`
(`e ≤ 800`):

| fixed part | `N_F` | `C` measured | bound `N_F/2` | holds |
|---|---|---|---|---|
| AP r1/r7 | 8 | 0.7542 | 4.0 | yes |
| AP r2/r6 | 8 | 0.7812 | 4.0 | yes |
| AP r3/r5 | 6 | 0.6875 | 3.0 | yes |
| AP r4 | 4 | 0.5938 | 2.0 | yes |
| E* r1 | 12 | 1.1192 | 6.0 | yes |
| E* r7 | 10 | 1.0066 | 5.0 | yes |
| E* r4 | 8 | 0.7146 | 4.0 | yes |

The bound holds everywhere with roughly a factor of five to spare.

## 4. The finite reduction

`|G(e)| > 0` as soon as `(3/4)|G_F| > N_F/(2e)`, i.e.

    e > E0 := 2 N_F / (3 |G_F|)

and `|G(e)| > 0` means `G(e)` is nonempty, so runner `i` is lonely. Hence **the
transit splits into an unbounded tail that is settled by the inequality, and a
finite initial segment `e <= E0`.**

Over all 15,456 distinct 6-element fixed-parts arising from 7-runner sets in
`[1..18]`:

- `|G_F| = 0` in **0** cases — the 7-runner subproblem is never tight, so `E0` is
  always finite. Tightness appears only when the eighth constraint arrives.
- `min |G_F| = 29/1232 = 0.023539` at `F = (1,4,5,6,7,11)`, `N_F = 8`.
- `max E0 = 280.0` at `F = (2,4,6,8,10,14)`, `N_F = 12`, `|G_F| = 0.028571`.

So on that range the whole transit reduces to checking `e <= 280`.

## 5. Where the measure degenerates

`|G(e)| = 0` occurred exactly once in the sweep: `F = {1,2,3,4,5,6}`, `e = 7` —
constraint set `{1,…,7}`, which is AP `(1,…,8)` seen from runner 1. `G` there is
**not empty**: it is the single point `t = 1/8`. Measure zero, nonempty. This is
the tight instance, and it is why measure alone is not the resolution statistic.

The statistic that does not degenerate is the component count. Over all seven
fixed-parts and every `e <= 600`:

- `G(e)` was **empty 0 times**;
- the minimum component count was **4**, attained by AP r1/r7 and E* r1 — the same
  `phi(8) = 4` that `ISOLATION_COUNT_v1` found at the AP extremes.

## 6. Status

- §3 is a proof: the `N_F/(2e)` error bound follows from counting centres in an
  interval, and is verified against measurement in all seven cases.
- §2 and §4 are measurements over the stated ranges. §4's two inputs — that
  `|G_F| > 0` always, and the uniform `E0`— are measured over `[1..18]`, not proved.
- The open quantitative input is a **uniform positive lower bound on `|G_F|`** over
  all 6-element fixed parts. With such a bound, `E0` is uniform and the transit is a
  finite check; without it, `E0` is finite case by case but not bounded.
- §5 records that measure is the wrong statistic at tight instances; the component
  count held at `>= 4` everywhere tested.
