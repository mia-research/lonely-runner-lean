# The scale rule — time to isolation, and what spreading the grid does (v2)

2026-09-13. n = 8, individual isolation, threshold 1/8.

**Change in v2**: **C4** of `SKETCH_DEBTS_v2` §4 — the disturbed-runner attainment rate is a step-size artefact, not a constant near one half. Recorded inline where the figures appear; no other claim is altered and no grade moves.

---

## 1. The bound is forced  `[PROVED — arithmetic]`

Every runner starts at gap 0 from its nearest neighbour, so it needs `‖d_min · t‖ ≥ 1/8`:

    t*  >=  1 / (8 · d_min)          d_min = that runner's smallest speed difference
    coverage  >=  1 / (8 · δ)        δ = the smallest pairwise gap in the configuration

**Time to isolation is inversely proportional to the gap.** Halving the closest approach doubles
the wait:

| `ε` | r1 = 2 − ε | `t* = 1/(8ε)` | in laps of r1 |
|---|---|---|---|
| 1/10 | 1.9 | 5/4 | 2.4 |
| 1/100 | 1.99 | 25/2 | 24.9 |
| 1/1000 | 1.999 | 125 | 249.9 |
| 1/100000 | 1.99999 | 12500 | 24999.9 |

Moving a runner **away** shortens its wait, and is bounded: r1 → 0 puts its nearest neighbour at
distance 2, so `t* ≥ 1/16`. The AP's `1/8` can be at best halved by displacing one runner.

## 2. Attainment, and the O(n) test  `[PROVED — arithmetic]`

The bound is attained iff the runner is actually lonely at `t = 1/(8 · d_min)`:

> **`t* = 1/(8·d_min)` iff `‖ d / (8·d_min) ‖ ≥ 1/8` for every other difference `d`.**

Checking it costs `n` comparisons at a single time — no window construction. `DMIN_RULE_SCOPE_v1`
§3 gives the worked failures (primes base: `d = 16` against `d_min = 2` gives `16/2 = 8 ≡ 0
mod 8`, so the runner is blocked at its own bound).

## 3. Deviations from the AP: attainment is exact  `[VERIFIED — exhaustive]`

For a runner disturbed by **none** of the movers, starting from the AP:

| movers | test | cases | attained | rate |
|---|---|---|---|---|
| 1 | full sweep, step 0.01 | — | — | 1.0000 |
| 2 | all 28 pairs, step 0.1 | 42,092 | 42,092 | **1.0000** |
| 3 | **all 56 triples**, step 0.25 | **58,318** | **58,318** | **1.0000** |
| 1–3 | randomised, denominators to 20 | 10,167 | 10,167 | **1.0000** |

Disturbed runners attain in 0.43–0.54 across every population and every mover count — stable,

**C4 — the rate is a step-size artefact.**  `[CORRECTED 2026-09-15]` The attainment rate for
disturbed runners is not a constant near one half. It falls monotonically as the displacement step
is refined:

| step | 1/10 | 1/100 | 1/1000 | 1/10000 |
|---|---|---|---|---|
| rate | 0.4641 | 0.4135 | 0.3800 | 0.3735 |

The figures reported in this file are the two coarsest points of that curve. The cause is the
small-denominator bias recorded at handover 2026-09-12 §2 item 12: a coarse step lands
disproportionately on displacements with small denominators, which are exactly the ones that keep
the spine instant. **The "near one half" reading, and any question asking why the rate sits near
one half, are withdrawn** — the rate has no limit near one half and the question is about the
sampling grid, not about the runners.

and unexplained.

## 4. Spreading the grid  `[VERIFIED — exact]`

**Dilates.** `(k, 2k, …, 8k)` is the AP times `k`: `δ = k` and coverage is exactly `1/(8k)`,
verified for `k = 1,2,3,4,8,16`. Scale invariance, as expected — `(8,16,…,64)` is the AP with
every time divided by 8.

**Partial spreading does nothing.** Pushing the later runners to larger grid points
(`u_i = i + 8 q_i`) leaves coverage at `1/8` for every `q` tested, because some pair remains at
distance 1 and `δ` stays 1:

| `q` | speeds | δ | coverage |
|---|---|---|---|
| `(0,…,0,1)` | `1,…,7,16` | 1 | 1/8 |
| `(0,0,0,0,1,1,1,1)` | `1,2,3,4,13,14,15,16` | 1 | 1/8 |
| `(0,0,1,1,2,2,3,3)` | `1,2,11,12,21,22,31,32` | 1 | 1/8 |
| `(0,0,0,0,0,0,2,4)` | `1,…,6,23,40` | 1 | 1/8 |
| **`(0,1,2,3,4,5,6,7)`** | `1,10,19,28,37,46,55,64` | **9** | **1/72** |

Only the last changes anything, and it is the AP of common difference 9 — spreading *every*
runner, not the later ones. **`δ` is a minimum over all pairs, so it is governed by the closest
pair and indifferent to how far the rest are spread.**

## 5. A hypothesis, refuted  `[REFUTED]`

> Coverage attains `1/(8·δ)` **iff** the configuration is a grid.

Over 700 random 8-subsets of `[1,60)`:

| | attains | does not |
|---|---|---|
| grid | 4 | **2** |
| not a grid | **57** | 637 |

Both directions fail. Non-grids attain the bound and grids miss it. Gridness is not the
criterion; §2's `O(n)` test is. Recorded because the hypothesis was natural and wrong, and the
grid families in §4 all attaining would have made it look confirmed.

## 6. Status and scope

`[PROVED — arithmetic]` §1's bound, §2's criterion.
`[VERIFIED — exhaustive]` §3's three-mover row (all 56 triples), §4's tables.
`[REFUTED]` §5.

**Scope.** §3 is the AP base only. §4 is 6 dilates and 10 spread vectors. §5 is 700 random
subsets of `[1,60)` containing only 6 grids, so its grid row is thin and the 2 misses are not
characterised.

**Not established.** ~~Why disturbed runners attain near one half everywhere.~~ **Struck** — the rate is not near one half; see the C4 note in §3. Whether §2's `O(n)`
test predicts attainment for *disturbed* runners as well as undisturbed ones — a run at
denominators up to 1000 was launched and had not returned.

**n = 8 is not proved here, and is not the target here.**
