# A prediction on the spread grid, and what refuted it

2026-09-13. n = 8, individual isolation, threshold 1/8. Base `(1,2,3,4,5,6,159,160)` — a grid
that behaves exactly like the AP on moment and service (`R7_R8_PAIR_LAW_v1` §1). One of r1…r6 is
displaced, r7 and r8 held at 159 and 160.

Predictions were written down before the test.

---

## 1. The predictions

Derived from `DISTURBANCE_RULE_v1` and the `d_min` rule:

- **P1** displacing `r_m` disturbs exactly `{r_m, the neighbour it moves toward}`.
- **P2** every undisturbed runner sits at `1/(8·d_min)`.
- **P3** r6 moving up is improved, because its single distance-1 neighbour r5 recedes.
- **P4** the 153-wide gap insulates r7 and r8 from anything r6 does.

P1, P3 and P4 rested on a claim that this configuration has **four** end-like runners — r1, r6,
r7, r8 — each with only one neighbour at speed-distance 1, against the AP's two.

## 2. Results

**P2 — confirmed, every row.** Undisturbed runners sit at `1/(8·d_min)` without exception.

**P3 — confirmed exactly.** r6 moved up, away from r5:

| r6 | `d_min` | moment | `1/(8·d_min)` | vs `1/8` |
|---|---|---|---|---|
| 6.1 | 11/10 | 5/44 | 5/44 | 0.909× |
| 6.5 | 3/2 | 1/12 | 1/12 | 0.667× |
| 7 | 2 | 1/16 | 1/16 | 0.500× |
| 10 | 5 | 1/40 | 1/40 | 0.200× |
| 80 | 75 | 1/600 | 1/600 | **0.013×** |

**P1 — refuted as stated.** `r2 → 2.1` disturbs `{r1, r2, r3}`, not `{r2, r3}`. `r5 → 4.9`
disturbs `{r4, r5, r6}`. `r1 → 0.9` disturbs `{r1, r8}`.

**P4 — refuted.** `r6 → 6.1` disturbs **r7**, across the 153-wide gap.

## 3. Why P4 failed — distance is not the relevant notion

    |159 − 6| = 153,   153 mod 8 = 1,   so  ‖153/8‖ = 1/8  exactly.

**r6 and r7 sit on precisely the same knife-edge as two consecutive runners.** The gap between
them is 153 units wide and buys nothing at all.

| pair | difference | mod 8 | `‖d/8‖` | knife-edge |
|---|---|---|---|---|
| r1–r2 | 1 | 1 | 1/8 | **yes** |
| r6–r7 | **153** | **1** | **1/8** | **yes** |
| r7–r8 | 1 | 1 | 1/8 | **yes** |
| r1–r8 | **159** | **7** | **1/8** | **yes** |
| r2–r6 | 4 | 4 | 1/2 | no |

So the configuration has **no end-like runners at all**. Mod 8 it is a closed cycle
`r1–r2–…–r6–r7–r8–r1`, every consecutive pair at residue difference `±1` — which is exactly what
being a grid means. My "four end-like runners" was an artefact of measuring adjacency in speed
rather than in residue.

**The corrected rule.** A runner keeps `t = 1/8` iff none of its differences is `≡ 0 mod 8`; a
displacement breaks it for exactly those runners whose difference residue leaves `[1,7]`.
Checked against the observed disturbed sets on eight displacements — **matches every one**,
including the three that refuted P1.

## 4. What this separates

The AP conflates two structures that a spread grid pulls apart:

| | governs | in the AP | in `(1,…,6,159,160)` |
|---|---|---|---|
| **`d_min`** — nearest in *speed* | the earliest possible moment, `t ≥ 1/(8·d_min)` | r6's is r5, at 1 | r6's is r5, at 1 |
| **residue mod 8** — nearest in *residue* | whether `t = 1/8` is available at all | r6's is r5 and r7, at 1 | r6's is r5 **and r7, at 153** |

In the AP the two coincide for every runner, so nothing distinguishes them and either description
fits. Spreading the grid separates them, and the two observables then answer to different
neighbours: r6's *earliest* time is set by r5 at distance 1, while its *knife-edge* is shared
with r7 at distance 153.

That is why P3 held and P4 did not — P3 is a `d_min` claim and P3's neighbour is r5; P4 is a
knife-edge claim and its neighbour is r7.

## 5. Status and scope

`[VERIFIED — exact]` §2's tables; §3's corrected rule on eight displacements.
`[REFUTED]` P1 as stated, and P4.
`[CONFIRMED]` P2, P3.

**Scope.** One base, `(1,2,3,4,5,6,159,160)`. Eight displacements, single mover, r7 and r8 fixed.
The corrected rule in §3 is checked on those eight, not swept.

**Not established.** Whether the corrected rule holds across a full sweep of this base, or on
other spread grids. Whether "improved" runners are always covered by `1/(8·d_min)` when the
mover is one of the pair r7/r8 rather than one of r1…r6.

**n = 8 is not proved here, and is not the target here.**
