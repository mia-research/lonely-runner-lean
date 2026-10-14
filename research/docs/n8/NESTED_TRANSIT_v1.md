# Moment and distance to isolation, under nested transits

2026-09-12. n = 8, individual isolation, threshold 1/8. Base AP `(1,…,8)`.

**Stage A** — r1 transits `0.1 → 1.9`, r2…r8 held at AP positions.
**Stage B** — r1 frozen at each of those values, r2 then transits its own range `(r1, 3)`.

Step 0.1 throughout, ordering kept strict. Two observables per runner:

- **moment** `t*` — the time at which that runner *first* becomes isolated;
- **distance** `L = v_i · t*` — how far that runner has run by then, in laps.

Artifact: `experiments/n8/ok_nested_transit_v1.py`.
Data: `experiments/n8/out_nested_transit_v1.csv` (19 + 361 configurations, 3,040 rows).

---

## 1. Stage A — moment  `[VERIFIED — exact]`

| r1 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 |
|---|---|---|---|---|---|---|---|---|
| 0.1 | **0.0658** | .1250 | .1250 | .1250 | .1250 | .1250 | .1250 | **0.1424** |
| 0.5 | **0.0833** | .1250 | .1250 | .1250 | .1250 | .1250 | .1250 | **0.2833** |
| 0.9 | 0.1136 | .1250 | .1250 | .1250 | .1250 | .1250 | .1250 | **0.3750** |
| **1.0 (AP)** | **.1250** | .1250 | .1250 | .1250 | .1250 | .1250 | .1250 | **.1250** |
| 1.1 | **0.4529** | 0.1389 | .1250 | .1250 | .1250 | .1250 | .1250 | .1250 |
| 1.5 | 0.2500 | 0.2812 | .1250 | .1250 | .1250 | .1250 | .1250 | .1250 |
| 1.9 | **1.2500** | **1.2812** | .1250 | .1250 | .1250 | .1250 | .1250 | .1250 |

**The effect is one-sided, and it swaps at the AP.** Moving r1 **down** delays **r8** (0.125 →
0.375) and leaves r2 alone. Moving r1 **up** delays **r2** (0.125 → 1.28) and leaves r8 alone.
Runners r3–r7 sit at 0.1250 throughout, both directions, every position.

**A slow r1 is isolated sooner than at the AP.** At `r1 = 0.1` its moment is 0.0658, half the
AP's. It is nearly stationary while the field runs away from it.

**At `r1 = 1.9` both r1 and r2 fall into the second cycle** (1.2500, 1.2812) — the near-collision
effect, `t ≥ 1/(8g)` with `g = 0.1` giving 1.25.

## 2. Stage A — distance  `[VERIFIED — exact]`

| r1 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 |
|---|---|---|---|---|---|---|---|---|
| 0.1 | 0.0066 | .2500 | **.3750** | **.5000** | **.6250** | **.7500** | **.8750** | 1.1392 |
| 0.5 | 0.0417 | .2500 | **.3750** | **.5000** | **.6250** | **.7500** | **.8750** | 2.2667 |
| **1.0 (AP)** | .1250 | .2500 | **.3750** | **.5000** | **.6250** | **.7500** | **.8750** | 1.0000 |
| 1.5 | 0.3750 | 0.5625 | **.3750** | **.5000** | **.6250** | **.7500** | **.8750** | 1.0000 |
| 1.9 | 2.3750 | 2.5625 | **.3750** | **.5000** | **.6250** | **.7500** | **.8750** | 1.0000 |

**Runners 3 to 7 run exactly `i/8` laps to their first isolation, at every position of the
transit.** `3/8, 4/8, 5/8, 6/8, 7/8` — unchanged from 0.1 to 1.9. Their moment is pinned at 1/8
and their speed is fixed, so the distance is pinned too.

At the AP every runner runs `i/8` laps, r1 through r8 giving `1/8 … 8/8`. The whole field
reaches its first isolation having covered a lap between them.

**The extremes are where the distance moves.** `r1 = 0.1` reaches isolation after 0.0066 of a
lap; `r1 = 1.9` needs 2.375 laps, and r2 needs 2.5625.

## 3. Stage B — freeze r1, transit r2  `[VERIFIED — exact]`

Across all **361** stage-B configurations:

| | |
|---|---|
| earliest full coverage | **0.1250, at `r1 = 1, r2 = 2`** — the AP |
| latest full coverage | 1.4718, at `r1 = 1.8, r2 = 1.9` |
| median | 0.3750 |
| beyond cycle 0 | 38 of 361 |

**The AP is the unique minimum over the whole two-runner family.** No combination of displaced
r1 and r2 covers the field sooner than the undisturbed AP, and the median configuration takes
three times as long.

**r4–r7 never move.** Their moment is 0.1250 in every stage-B row, for every frozen r1 and every
r2. Displacing r1 and r2 reaches r1, r2, r3 and — when r1 drops below 1 — r8, and nothing else.

**Freezing produces flat runs.** With r1 frozen at 1.1, r1's own moment sits at **0.4529** for
every r2 from 1.4 through 2.0, then drops to 0.1250 at `r2 = 2.1`. The second transit does not
move the first runner at all until it crosses a threshold, and then moves it all at once.

## 4. Status and scope

`[VERIFIED — exact]` §1, §2, §3, at the stated scope.

**Scope.** One base, the AP. Stage A is 19 configurations, stage B is 361. Step 0.1, so only
denominators `q ∈ {1,2,5,10}` — the small-denominator points, which are the local minima. No
third-stage transit (freeze r1 and r2, move r3) has been run.

**Not established.** Why the effect is one-sided about the AP (down delays r8, up delays r2);
why r4–r7 are untouched; where the thresholds in §3's flat runs fall, or what sets them. The
near-collision delays in §1 are the forced bound `t ≥ 1/(8g)` from `DELAYED_ISOLATION_v1` §2 and
are not new.

**n = 8 is not proved here, and is not the target here.**
