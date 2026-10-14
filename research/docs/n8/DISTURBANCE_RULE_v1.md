# Who is disturbed when one runner leaves the AP

2026-09-12. n = 8, individual isolation, threshold 1/8. Base AP `(1,…,8)`, each runner in turn
displaced across its whole neighbour interval, all others returned to AP positions. Step 0.01,
1,592 configurations, all eight runners recorded at each.

Observable: **moment** — the time at which a runner first becomes isolated. At the AP every
runner's moment is `t = 1/8`, all eight simultaneously. A displacement can move a runner's
moment **later** (delayed) or **earlier** (improved).

Data: `experiments/n8/out_full_sweep_v1.csv`. Artifact: `experiments/n8/ok_full_transit_sweep_v1.py`.

---

## 1. Exactly two runners are disturbed  `[VERIFIED — exhaustive over this sweep]`

| delayed | improved | untouched | configurations |
|---|---|---|---|
| 2 | 0 | 6 | 1,188 |
| 2 | 1 | 5 | 198 |
| 1 | 1 | 6 | 199 |

**No configuration in the sweep disturbs more than three runners, and the other five or six are
untouched — exactly `t = 1/8`, not approximately.**

## 2. Which two, and why  `[VERIFIED — 1.00 of positions in every cell]`

| mover | direction | delayed | improved |
|---|---|---|---|
| r1 | down | r8 | **r1** |
| r1 | up | r1, r2 | — |
| r2 | down | r1, r2 | — |
| r2 | up | r2, r3 | **r1** |
| r3 | down | r2, r3 | — |
| r3 | up | r3, r4 | — |
| r4 | down | r3, r4 | — |
| r4 | up | r4, r5 | — |
| r5 | down | r4, r5 | — |
| r5 | up | r5, r6 | — |
| r6 | down | r5, r6 | — |
| r6 | up | r6, r7 | — |
| r7 | down | r6, r7 | **r8** |
| r7 | up | r7, r8 | — |
| r8 | down | r7, r8 | — |
| r8 | up | r1 | **r8** |

Every cell holds at **1.00** of its 199 positions — the pattern does not depend on how far the
runner is displaced, only on which way.

**The delayed pair is the mover and the neighbour it moves toward.** Moving away from a
neighbour cannot hurt that neighbour; the gap only opens.

**A caution on reading the flat columns.** They are direction-specific and they are about the
*moment*, not the position. r2 holds `t = 1/8` only while r1 moves **down**, away from it. Going
**up**, r2 loses it outright: at `r1 = 1.9`, r1 sits at `0.2375` and r2 at `0.2500` when
`t = 1/8` — a gap of `0.0125`, nowhere near the threshold.

| r2's first loneliness | AP | `r1 = 1.9` |
|---|---|---|
| moment | 0.1250 | **1.2812** |
| position on the track | 0.2500 of a lap | **0.5625 of a lap** |
| window length | 0.020833 | 0.010417 |

Both the moment and the position move. What is fixed is only that r2's position *at a given
time* `t` is `2t` regardless of r1 — which says nothing about *when* it is lonely, and therefore
nothing about where. An earlier draft of this file conflated the two.

The two inequalities for the AP's end pair:

| | keeps `t = 1/8` iff |
|---|---|
| r2 | `(2 − r1)/8 ≥ 1/8` ⟺ `r1 ≤ 1` |
| r8 | `r1/8 ≥ 1/8` ⟺ `r1 ≥ 1` |

At `r1 = 1` both hold with equality, which is the knife-edge that gives the AP's end runners
their zero-width windows.

**Only r1 and r8 are ever improved.** A runner's first isolation cannot precede
`t = 1/(8 · d_min)`, `d_min` its smallest speed difference. At the AP every runner has
`d_min = 1`, giving `t ≥ 1/8`, attained. Interior runners have a distance-1 neighbour on *both*
sides, so moving one away leaves `d_min = 1` and the bound unmoved. **r1 and r8 have only one
distance-1 neighbour each** — r2 and r7 — so when that one recedes, `d_min` grows and the bound
relaxes. At `r1 = 0.1` its `d_min` is 1.9 and its moment is `1/(8 × 1.9) = 0.0658`, exactly the
measured value.

So the end runners are the only ones that can get *better*, and they are also the only ones that
were at zero duration at the AP. Same two runners, both ends of the same asymmetry.

## 3. The wrap at the ends

r1 moving **down** and r8 moving **up** each disturb the *other* end — r1 down delays r8, r8 up
delays r1 — with no intervening runner involved. The pack's two ends are coupled through the
difference `|8 − r1|`, which is the largest difference in the configuration and the one whose
residue mod 1 moves fastest as a speed changes.

## 4. Status and scope

`[VERIFIED — exhaustive over this sweep]` §1's tally; §2's table at 1.00 per cell.
`[PROVED — arithmetic]` the bound `t ≥ 1/(8 · d_min)` and the two inequalities in §2.

**Scope.** One base, the AP. One runner displaced at a time, always with the others returned to
AP positions. Step 0.01 — denominators dividing 100 only. Nothing here covers two runners
displaced at once; the nested sweep in `NESTED_TRANSIT_v1` §3 shows r4–r7 still untouched there,
but that is 361 configurations of one pair, not a test of the rule.

**Not established.** Whether the rule survives a non-AP base, where `d_min = 1` need not hold for
every runner. Whether "the neighbour it moves toward" remains the right description once the
displacement passes a neighbour — no sweep crosses, so this is untested by construction.

**n = 8 is not proved here, and is not the target here.**
