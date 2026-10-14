# r8 from the AP to the next grid

2026-09-12. n = 8, individual isolation, threshold 1/8. Base AP `(1,…,8)`, r8 transited from 8
up to 16 and beyond. r8 is the only runner that can reach another grid without crossing a
neighbour, since every other runner would have to pass its neighbours to land in its own residue
class.

Artifact: `experiments/n8/ok_service_disparity_v1.py` (tally engine).

---

## 1. This transit is unlike all the others  `[VERIFIED — exact]`

Every earlier transit moved a runner **toward** a neighbour and immediately created a service
queue. r8 moving up moves **away** from everyone: its smallest speed difference grows from 1 at
the AP to 9 at `r8 = 16`. There is no near-collision anywhere in the range.

The result is that service stays equal almost throughout:

| r8 | grid | `d_min(r8)` | coverage | tallies r1…r8 | ratio | last served |
|---|---|---|---|---|---|---|
| **8** | **GRID** | 1 | 0.1250 | 1,1,1,1,1,1,1,1 | **1** | **all eight at once** |
| 8.5 | | 3/2 | 0.2833 | 1,3,3,2,1,2,2,2 | **3** | r1 |
| 9 | | 2 | 0.1406 | 1,1,1,1,1,1,1,1 | 1 | r1 |
| 10 | | 3 | 0.1406 | 1,1,1,1,1,1,1,1 | 1 | r2 |
| 12 | | 5 | 0.1406 | 1,1,1,1,1,1,1,1 | 1 | r4 |
| 14 | | 7 | 0.1406 | 1,1,1,1,1,1,1,1 | 1 | r6 |
| 14.5 | | 15/2 | 0.2833 | 2,3,3,2,2,2,1,2 | **3** | r7 |
| 15 | | 8 | 0.1406 | 1,1,1,1,1,1,1,1 | 1 | r7 |
| **16** | **GRID** | 9 | **0.1250** | 1,1,1,1,1,1,1,**2** | 2 | r1…r7 |

Ratio 1 at nearly every sampled position, against 2–11 on every other transit. Two exceptions at
`8.5` and `14.5`, both ratio 3; the other half-integers in the range do not spike, and I have no
account of why those two do.

## 2. The last-served runner is the residue-collision partner  `[VERIFIED — exact]`

At integer speeds:

| r8 | `r8 mod 8` | shares residue with | tallies | last served |
|---|---|---|---|---|
| 9 | 1 | r1 | 1×8 | **r1** |
| 10 | 2 | r2 | 1×8 | **r2** |
| 11 | 3 | r3 | 1×8 | **r3** |
| 12 | 4 | r4 | 1×8 | **r4** |
| 13 | 5 | r5 | 1×8 | **r5** |
| 14 | 6 | r6 | 1×8 | **r6** |
| 15 | 7 | r7 | 1×8 | **r7** |
| **16** | **0** | **none — GRID** | 1×7, r8:**2** | r1…r7 |
| 17 | 1 | r1 | 1×7, r8:2 | r1 |
| … | | | | |
| **24** | **0** | **none — GRID** | 1×7, r8:**3** | r1…r7 |

Each unit step advances the collision one place, and the runner served last advances with it. The
residue partner is the one whose loneliness r8 is stealing, and it is the one left waiting.

## 3. Reaching the next grid does not restore simultaneity

At `r8 = 16` the configuration is a grid again — residues complete mod 8 — and coverage returns
to `1/8`, the AP's value. But service is **not** equal: r8 has been lonely **twice** by then, the
others once.

The reason is `d_min`. Every AP runner has a speed-neighbour at distance 1, so no runner can be
lonely before `t = 1/8` and the first spine instant serves all eight at once. At `r8 = 16`,
r8's `d_min` is 9, so it can be lonely from `t = 1/72` — long before the pack. It takes an extra
turn while the others are still waiting for `1/8`.

The surplus grows with speed: r8 takes **1** extra turn at 16, **2** at 24.

**Simultaneous service needs every runner to have `d_min = 1`.** The AP has that; a spread grid
does not. Being a grid buys global isolation and the earliest coverage; it does not buy equal
service.

## 4. Note on `r8 = 14`

`FULL_SWEEP_v1` §1a records that at `r8 = 14` runner 7's entire good set is four isolated points
— duration zero. Its service tally here is nevertheless 1, and the ratio is 1. An instant of
zero length still counts as being served. Duration and service are different observables and
disagree here.

## 5. Status and scope

`[VERIFIED — exact]` §1's table; §2's residue correspondence over `r8 ∈ [9,24]`; §3's surplus.

**Scope.** One base, the AP. Only r8 moved. Step 0.1 up to 16, integers to 24. Nothing beyond 24,
and no test of whether the residue correspondence survives a non-AP base or a different mover
(no other runner can reach a second grid without crossing, so the question may not transfer).

**Not established.** Why `8.5` and `14.5` spike to ratio 3 while the other half-integers do not.
Whether the surplus at `r8 = 8k` is exactly `k − 1`, which the two data points 16 and 24 are
consistent with and do not establish.

**n = 8 is not proved here, and is not the target here.**
