# Do the others get multiple isolations while one runner waits?

2026-09-12. n = 8, individual isolation, threshold 1/8. Base AP `(1,…,8)`, one runner displaced.

Question: run the clock until the delayed runner is finally lonely. How many turns have the
others had by then?

Artifact: `experiments/n8/ok_full_transit_sweep_v1.py` (engine); counts taken over `[0, t*]` with
window repetition across the period.

---

## 1. Answer: yes, by up to 101 to 1  `[VERIFIED — exact]`

Running until **r1** is lonely:

| configuration | `t*` (r1's first) | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 |
|---|---|---|---|---|---|---|---|---|---|
| **AP** | 1/8 | **1** | **1** | **1** | **1** | **1** | **1** | **1** | **1** |
| r1 = 1.1 | 0.4529 | 1 | 4 | 4 | 3 | 3 | 4 | 4 | 2 |
| r1 = 1.9 | 1.2500 | 1 | **0** | 8 | 7 | 5 | 6 | 8 | **9** |
| r2 = 1.01 | 12.625 | 1 | 1 | 90 | 67 | 67 | 82 | **101** | 61 |

At `r2 = 1.01`, r7 is lonely **101 times** before r1 is lonely once. At `r1 = 1.9`, r8 has had
nine turns and **r2 has had none** — r2 is served even later than r1, at 1.2812.

## 2. Running until everyone has been served  `[VERIFIED — exact]`

Tallies at the coverage time — the first moment every runner has been lonely at least once:

| r1 | coverage `t*` | tallies (r1…r8) | max : min |
|---|---|---|---|
| **1.0 (AP)** | **0.1250** | **1,1,1,1,1,1,1,1** | **1 : 1** |
| 0.1 | 0.1424 | 1,1,1,1,1,1,1,1 | 1 : 1 |
| 0.5 | 0.2833 | 2,2,2,1,2,3,3,1 | 3 : 1 |
| 0.9 | 0.3750 | 2,3,3,3,3,2,3,1 | 3 : 1 |
| 1.1 | 0.4529 | 1,4,4,3,3,4,4,2 | 4 : 1 |
| 1.5 | 0.2812 | 1,1,2,2,1,2,2,2 | 2 : 1 |
| 1.9 | 1.2812 | 1,1,9,8,5,7,9,**10** | **10 : 1** |

## 3. What is special about the AP here

**At the AP all eight are served at the same instant.** Not merely "each within one cycle" —
every runner's *first* isolation is `t = 1/8`, the same moment, one turn each, nobody waiting
while anybody else is served.

The reason is the `d_min` bound again. Every AP runner has a speed-neighbour at distance 1, so
`t ≥ 1/(8 · 1) = 1/8` for all eight, and the first spine instant delivers it to all eight at
once. Both halves are needed: the bound makes `1/8` the earliest possible, and the grid makes it
simultaneously achievable.

**`r1 = 0.1` also gives 1 : 1, but not by simultaneity.** Its first isolations are staggered
(r1 at 0.0658, most at 0.125, r8 at 0.1424); the ratio is 1 : 1 only because the coverage time
arrives before anybody gets a second turn. Equal service and simultaneous service are different
properties, and only the AP has the second.

**Other grids do not have it either.** At `r8 = 16` — a grid — r8's first isolation precedes
`1/8`, because its `d_min` exceeds 1. Simultaneous first isolation needs every runner to have
`d_min = 1`, which the AP has and a spread grid does not.

## 4. Status and scope

`[VERIFIED — exact]` §1's four configurations; §2's eleven.
`[PROVED — arithmetic]` the bound `t ≥ 1/(8 · d_min)` underlying §3.

**Scope.** One base, the AP. Single displacements, r1 and r2 only in §1; §2 is the r1 transit at
step 0.1. The 101 : 1 figure is one configuration, not a maximum — by the `1/(8g)` bound a
smaller gap pushes it arbitrarily high, so no maximum is claimed or approached here.

**Not established.** Whether the disparity has any bound in terms of the displacement; whether
the runner that accumulates the most turns is predictable; whether simultaneous first isolation
characterises the AP among all configurations or only among those tested.

**n = 8 is not proved here, and is not the target here.**
