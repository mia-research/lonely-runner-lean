# Full sweep — every runner across its whole neighbour interval

2026-09-12. n = 8, individual isolation, threshold 1/8. Base AP `(1,…,8)`. Each runner in turn
varied across the **open interval between its two neighbours**, step `0.01`, with the other
seven holding their AP positions. Every runner's isolation times and durations recorded at
every position.

A data record. No law is proposed; §3's correspondence is an observation with a count attached.

Artifact: `experiments/n8/ok_full_transit_sweep_v1.py`.
Data: `experiments/n8/out_full_sweep_v1.csv` (12,736 rows — 8 sweeps × 199 positions ×
8 runners), `experiments/n8/out_full_sweep_windows_v1.csv` (158,008 individual windows).

| sweep | interval | positions | | sweep | interval | positions |
|---|---|---|---|---|---|---|
| r1 | 0.01 – 1.99 | 199 | | r5 | 4.01 – 5.99 | 199 |
| r2 | 1.01 – 2.99 | 199 | | r6 | 5.01 – 6.99 | 199 |
| r3 | 2.01 – 3.99 | 199 | | r7 | 6.01 – 7.99 | 199 |
| r4 | 3.01 – 4.99 | 199 | | r8 | 7.01 – 8.99 | 199 |

Speed 0 is excluded outright — translation is free, adjoining is not — and a speed equal to a
neighbour's is excluded as a duplicate runner.

## 0. What is recorded, and in what time

Per runner, per position: **times** — first isolation, every window's start and end, how many
windows sit on the eighth-lattice `{m/8}` and how many have drifted off it; **durations** —
longest window, shortest, mean, total isolated time per period, and density.

All durations are in **original time**. Reducing a configuration whose moved speed has
denominator `q` stretches the period by about `q`, so a duration read off the reduced
configuration is not comparable across positions. The period `P` is carried in every row.
Density and individual window widths are comparable across positions; total-per-period is not.

**Individual, not global.** Each runner's constraint set is its own seven differences. Global
isolation would use all 28 pairs and give all eight runners the identical good set; at the AP
they have four distinct good sets, counts `4,8,8,6,6,8,8,4`.

**Two engines.** An integer-scaled fast path and the exact `Fraction` path, checked against
each other before the sweep: **60 agreements, 0 disagreements**, 5 cases where the fast path's
overflow guard fired and the exact path took over. Disagreement is a hard stop in the script.

## 1. Duration collapses at exactly one position per sweep  `[VERIFIED — exact]`

| sweep | minimum duration over the sweep | where |
|---|---|---|
| r1 | 0 | `r1 = 1` |
| r2 | 0 | `r2 = 2` |
| r3 | 0 | `r3 = 3` |
| r4 | 0 | `r4 = 4` |
| r5 | 0 | `r5 = 5` |
| r6 | 0 | `r6 = 6` |
| r7 | 0 | `r7 = 7` |
| r8 | 0 | `r8 = 8` |

In every sweep the only position where some runner's longest isolation window has length zero
is the AP itself — the runner's own starting speed. At that position the count is still 4: the
end runners hold four isolation **instants** of zero length. Nowhere else in 1,592 positions
does any runner's duration reach zero. **See §1a — extending r8 past 9 breaks this pattern.**

## 1a. CORRECTION — "zero duration only at the AP" does not survive extension

§1's count is correct as scoped: over the 1,592 positions swept, zero duration occurs only at
each runner's own AP speed. **The pattern it suggests is false.**

`r8` is the only runner that can reach another grid without crossing a neighbour — every other
runner would have to pass its neighbours to land in its own residue class. The next *integer*
above 8 is 9, but `(1,…,7,9)` has residues `{1,2,3,4,5,6,7}` and is **not** a grid: r8 takes
r1's residue. The next speed at which the eight are a grid again is **16**, then 24, 32.

Extending r8 from 8 to 16 at step 0.1 (90 positions):

| r8 | grid | min count | min duration | runners at zero duration |
|---|---|---|---|---|
| **8** | **yes** | 4 | **0** | r1, r8 |
| 9 | no | **2** | 1/80 | — |
| 10 | no | 4 | 1/48 | — |
| 11 | no | 6 | 1/48 | — |
| 12 | no | 6 | 1/48 | — |
| 13 | no | 6 | 1/70 | — |
| **14** | no | 4 | **0** | **r7** |
| 15 | no | 6 | **1/112** | — |
| **16** | **yes** | 8 | 1/80 | **none** |

Two things this overturns:

- **Zero duration is not exclusive to the AP.** At `r8 = 14` (residues `1,2,3,4,5,6,7,6` — r8
  collides with r6) runner 7's entire good set is four isolated points, duration zero, count 4.
  The same state the AP's end runners are in, at a configuration that is not a grid.
- **The AP is not typical of grids.** At the next grid, `r8 = 16`, **no** runner has zero
  duration; the minimum is `1/80` and the minimum count is 8, double the AP's. The AP is the
  grid whose end runners have zero reserve, not the general case.

All 81 non-integer positions of this extension give min duration `1/48`, one value — consistent
with §2. The departures are at integers, and `r8 = 15` gives `1/112`, lower than any value in
the original eight sweeps.

## 2. Off the AP, the per-position minimum duration is one value per sweep  `[VERIFIED — exact]`

Over the 198 non-integer positions of each sweep, taking `min` over the eight runners of that
runner's longest window:

| sweep | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 |
|---|---|---|---|---|---|---|---|---|
| value | `1/48` | `1/70` | `1/48` | `1/48` | `1/48` | `1/48` | `1/70` | `1/48` |
| distinct values | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
| positions | 198/198 | 198/198 | 198/198 | 198/198 | 198/198 | 198/198 | 198/198 | 198/198 |

One value each, across the whole interval, on both sides of the AP. The `1/70` sweeps are r2
and r7, which are mirror images under `t → 1−t`.

## 2a. The step-0.1 view

The sweep was run at `0.01` and is banked at that resolution; the tables below subsample it to
`0.1` for legibility, 19 positions per sweep. **The coarse grid is not a neutral subsample** —
step `0.1` visits only `q ∈ {1,2,5,10}` against step `0.01`'s `{1,2,4,5,10,20,25,50,100}`, and
small denominators are the local minima (`TRANSIT_FRACTIONAL_v1` §1). Coarse is the
sharper-edged sample, not the milder one. The fine data is on disk for any close-up.

**Longest isolation window, r1 sweeping 0.1 → 1.9:**

| r1 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 |
|---|---|---|---|---|---|---|---|---|
| 0.1 | 0.09494 | 0.02083 | 0.05000 | 0.09375 | 0.15306 | 0.09375 | 0.05000 | 0.02083 |
| 0.5 | 0.10000 | 0.02083 | 0.05000 | 0.09375 | 0.15278 | 0.09375 | 0.05000 | 0.02083 |
| 0.9 | 0.10563 | 0.02083 | 0.05000 | 0.09375 | 0.16362 | 0.09375 | 0.05000 | 0.02083 |
| **1.0 (AP)** | **0** | 0.02083 | 0.05000 | 0.09375 | 0.09375 | 0.05000 | 0.02083 | **0** |
| 1.1 | 0.10870 | 0.02083 | 0.05000 | 0.09375 | 0.16667 | 0.09375 | 0.05000 | 0.02083 |
| 1.5 | 0.11538 | 0.02083 | 0.05000 | 0.09375 | **0.12500** | **0.07986** | 0.05000 | 0.02083 |
| 1.9 | 0.12295 | 0.02083 | 0.05000 | 0.09375 | 0.16667 | 0.09375 | 0.05000 | 0.02083 |

**Longest isolation window, r2 sweeping 1.1 → 2.9:**

| r2 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 |
|---|---|---|---|---|---|---|---|---|
| 1.1 | 0.06250 | 0.10870 | 0.05000 | 0.09375 | 0.09375 | 0.06667 | 0.06250 | 0.01429 |
| 1.5 | 0.06250 | 0.11538 | 0.05000 | 0.09375 | 0.09375 | 0.06667 | **0.05682** | 0.01429 |
| 1.9 | 0.06250 | 0.12295 | 0.05000 | 0.09375 | 0.09375 | 0.06667 | 0.06250 | 0.01429 |
| **2.0 (AP)** | **0** | 0.02083 | 0.05000 | 0.09375 | 0.09375 | 0.05000 | 0.02083 | **0** |
| 2.1 | 0.06250 | 0.12712 | 0.05000 | 0.09375 | 0.09375 | 0.06667 | 0.06250 | 0.01429 |
| 2.5 | 0.06250 | 0.13636 | 0.05000 | 0.09375 | 0.09375 | 0.06667 | 0.06250 | 0.01429 |
| 2.9 | 0.06250 | 0.14706 | 0.05000 | 0.09375 | 0.09375 | 0.06667 | 0.06250 | 0.01429 |

Three things visible here that the fine grid buried, recorded as observations:

- **In the r2 sweep, seven of the eight runners hold a constant longest window** across the
  whole interval 1.1 – 2.9. Only the mover changes. The r1 sweep has five of eight constant.
- **The mover's longest window increases monotonically with its own speed** in both sweeps —
  r1: `0.09494 → 0.12295`, r2: `0.10870 → 0.14706` — with no reversal at any sampled point.
- **The exceptions sit at half-integers and at the AP.** `r1 = 1.5` is where r5 and r6 drop
  below their otherwise-constant values; `r2 = 1.5` is where r7 does. Every other departure in
  these two tables is at an integer.

One coincidence, noted and unexplained: a mover at speed `1.9` has longest window `0.12295` in
**both** sweeps, although its constraint sets differ (`{0.1,1.1,…,6.1}` against
`{0.9,1.1,…,6.1}`). Not investigated.

## 3. Which runner carries it  `[VERIFIED — 10/10 carrier rows]`

The carrier is the runner whose longest window equals the sweep minimum. Each **non-moving**
runner keeps six of its seven differences; call that its fixed set `S`, and `A(S)` the set
`{t : ‖k t‖ ≥ 1/8 for all k ∈ S}`.

| sweep | floor | carried by | its six fixed differences | longest `A(S)` component | equal |
|---|---|---|---|---|---|
| r1 | `1/48` | r2, r8 (198/198 each) | `{1,2,3,4,5,6}` | `1/48` | yes |
| r2 | `1/70` | r8 (198/198) | `{1,2,3,4,5,7}` | `1/70` | yes |
| r3 | `1/48` | r2 (198/198) | `{1,2,3,4,5,6}` | `1/48` | yes |
| r4 | `1/48` | r1 (198/198) | `{1,2,4,5,6,7}` | `1/48` | yes |
| r5 | `1/48` | r8 (198/198) | `{1,2,4,5,6,7}` | `1/48` | yes |
| r6 | `1/48` | r7 (198/198) | `{1,2,3,4,5,6}` | `1/48` | yes |
| r7 | `1/70` | r1 (198/198) | `{1,2,3,4,5,7}` | `1/70` | yes |
| r8 | `1/48` | r1, r7 (198/198 each) | `{1,2,3,4,5,6}` | `1/48` | yes |

The carrier is always r1, r2, r7 or r8 — never an interior runner — and the value always equals
the longest component of the carrier's fixed part. The containment half is forced: a runner's
good set lies inside its fixed part, so its longest window cannot exceed that component.
Equality is what is observed, and only on the carriers; §4 shows it fails elsewhere.

**Not claimed.** That this predicts an untested sweep, a non-AP base, or a multi-runner
displacement. Two different fixed sets — `{1,2,3,4,5,6}` and `{1,2,4,5,6,7}` — both give
`1/48`, and nothing here explains why.

## 4. Per-runner durations, r1 sweeping 0.01 – 1.99  `[VERIFIED — exact]`

Non-integer positions only:

| runner | longest window (min – max) | density (min – max) | constant? |
|---|---|---|---|
| 1 (moving) | `75/799` – `75/601` | 0.11364 – 0.14204 | no |
| 2 | `1/48` – `1/48` | 0.06125 – 0.07708 | **yes** |
| 3 | `1/20` – `1/20` | 0.10361 – 0.13542 | **yes** |
| 4 | `3/32` – `3/32` | 0.20208 – 0.25238 | **yes** |
| 5 | `1/8` – `1/6` | 0.31845 – 0.36806 | no |
| 6 | `23/288` – `3/32` | 0.24769 – 0.27431 | no |
| 7 | `1/20` – `1/20` | 0.10417 – 0.11383 | **yes** |
| 8 | `1/48` – `1/48` | 0.06318 – 0.07308 | **yes** |

Four of the seven stationary runners hold their longest window **exactly constant** across the
entire interval, r1 moving from 0.01 to 1.99 — a 200-fold change in its speed. Their density
moves over the same range while their longest window does not.

r5 and r6 are the two stationary runners whose longest window varies; both have wide
`A(S)`-components, and both dip below them at particular positions.

## 5. Status and scope

`[VERIFIED — exact]` §1, §2, §3, §4, at the stated scope.
`[control]` two engines, 60 agreements, 0 disagreements.

**Scope.** One base, the AP. One runner moving at a time. Step `0.01`, so only denominators
dividing 100 are visited — `q ∈ {1,2,4,5,10,20,25,50,100}`, and 40% of positions are `q = 100`.
No prime denominator above 5 is sampled anywhere in this sweep. A separate Farey-order-16 sweep
covering every `q ≤ 16` returned the same `1/48` on the r8 transit, but that is one transit.

**Not covered.** Multi-runner displacement, non-AP bases, speeds outside a neighbour interval,
and irrational speeds — where a count is undefined and only the density survives.

**Not established.** Anything about why. §3 is a correspondence with a count, not a mechanism,
and no claim is made that it extends past the ten rows shown.

**n = 8 is not proved here, and is not the target here.**
