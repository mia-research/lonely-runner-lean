# Workbook — interaction structure: simultaneous loneliness off the AP/grid

2026-09-12. n = 8, individual isolation. Every prior note in this series measured runners
**separately**. This one measures how they **interact**: how many can be lonely at the same
instant, and which sets of them. BSM, exact.

Factual record. Nothing is concluded.

---

## 1. The quantity

`S(t)` = number of runners lonely at time `t`. Global isolation is `S(t) = 8`, so

**`[PROVED]`** `max S = 8` ⟺ the configuration is a grid (`WHICH_GRIDS_ISOLATE_v1` §1).

**`[PROVED]`** `max S ≥ (number of spine holders)`. All spine holders are lonely
simultaneously at `t = p/(8g)`, `p` odd, so `S` at that instant equals the spine count.

## 2. `max S` by grid distance  `[VERIFIED — exhaustive, 6,434 primitive 8-sets in [0..14]]`

| `k` | configs | `max S` distribution |
|---|---|---|
| 0 | 128 | `{8: 128}` |
| 1 | 1,792 | `{6: 1792}` |
| 2 | 3,360 | `{4: 2482, 5: 416, 6: 462}` |
| 3 | 1,120 | `{3: 54, 4: 650, 5: 182, 6: 234}` |
| 4 | 34 | `{4: 22, 6: 12}` |

- `k = 0`: 8, always.
- `k = 1`: **6, always** — 1,792 of 1,792. Never 7 (a collision costs the spine to *both*
  members of the pair, so 8 − 2 = 6) and never more than 6 (no non-spine instant beats it).
- `k ≥ 2`: spread.

## 3. `max S` by spine count  `[VERIFIED]`

| spine holders | `max S` distribution | `max S ≥ spine`? |
|---|---|---|
| 0 | `{4: 22, 6: 12}` | yes |
| 2 | `{3: 54, 4: 650, 5: 182, 6: 234}` | yes |
| 4 | `{4: 2482, 5: 416, 6: 462}` | yes |
| 6 | `{6: 1792}` | yes |
| 8 | `{8: 128}` | yes |

The bound of §1 holds everywhere, with equality at spine counts 6 and 8 and slack below. At
spine count 4 the excess reaches 6 — **two runners join at a non-spine instant**. At spine
count 0, `max S` is still 4 or 6: runners with no eighth-lattice point at all still synchronise
elsewhere.

## 4. Which sets are simultaneously lonely  `[VERIFIED — exact]`

Maximal subsets of runners that share a lonely instant:

| configuration | distinct lonely-sets | maximal sets |
|---|---|---|
| AP grid `(1..8)` | 4 | **1**: all eight |
| spread grid `(1..7,16)` | 22 | **1**: all eight |
| one move, `r2 → 9` | 9 | 3: `{2,3,4,5,6,7}`, `{3,4,5,6,7,8}`, `{1}` |
| E* | 20 | 7, largest size 4: `{1,3,6,8}`, `{2,3,5,8}`, … |

Two observations.

**A grid has exactly one maximal set.** Both grids — tight and spread — yield a single maximal
set containing every runner, though they differ hugely in how many distinct lonely-sets occur
(4 against 22). The tight AP is the more rigid: only four distinct sets occur at all.

**The crashed runner becomes a singleton.** After `r2 → 9`, runner 1 appears as a maximal set
**by itself** — it is never lonely at the same instant as any other runner. Losing the spine
removed it from every shared instant, not merely from the four.

E* fragments furthest: 7 maximal sets, none larger than 4.

## 4a. The max-S coalition usually is NOT the spine set  `[VERIFIED — exhaustive [0..14]]`

`max S ≥ spine count` is proved (§1), so it is natural to expect the maximum to be the spine
set plus extras. It usually is not. Of **2,032** configurations with `k ≥ 2` in which `max S`
exceeds the spine count:

| max-S set is… | count |
|---|---|
| **not** a superset of the spine set | **1,760 (87%)** |
| a superset of the spine set | 272 (13%) |

Worked examples, all with spine count 4 and `max S` 6:

    V = (0,1,2,3,4,5,8,13)   spine holders {2,3,4,5} at t = 1/8
                             max-S coalition {1,3,4,5,6,8} at t = 237/1664
                             drops runner 2, adds 1, 6, 8

    V = (0,1,2,3,4,5,9,13)   spine {1,3,4,5}   max-S {1,2,4,5,6,8}, drops 3, adds 2, 6, 8
    V = (0,1,2,3,4,5,10,13)  spine {1,2,4,5}   max-S {1,2,3,5,6,8}, drops 4, adds 3, 6, 8

> **The spine set is replaced, not extended.** The maximum occurs at a different instant
> (`237/1664`, denominator `2⁷·13`) and involves a different coalition — one spine-holder
> drops out and three non-holders join.

So the spine is a guaranteed *floor* on simultaneity, not the mechanism producing the maximum.
Off-grid, runners re-group at finer times.

## 4b. Structure of the maximal-set system  `[VERIFIED — exhaustive [0..13]]`

`(number of maximal sets, size of the largest)` by grid distance, four most common per row:

| `k` | most common `(count, largest)` |
|---|---|
| 0 | `(1, 8): 64` — **every** grid, without variation |
| 1 | `(5,6): 288`, `(4,6): 240`, `(3,6): 232`, `(6,6): 64` |
| 2 | `(5,4): 406`, `(6,4): 376`, `(4,4): 221`, `(7,4): 124` |
| 3 | `(6,4): 112`, `(5,4): 108`, `(5,5): 56`, `(7,4): 50` |
| 4 | `(2,6): 4`, `(6,4): 4`, `(7,4): 2`, `(3,4): 2` |

- `k = 0`: exactly **one** maximal set, of size 8, in all 64 grids. No variation at all.
- `k = 1`: the largest is **always 6**; only the number of maximal sets varies (3 to 6).
- `k ≥ 2`: both quantities vary.

So the system is rigid at `k = 0`, half-rigid at `k = 1` (size fixed, count free), and free
beyond. The count of maximal sets rises from 1 to typically 5–7 as `k` grows: **the single
all-runner coalition of a grid fragments into several smaller ones.**

## 4c. `max S` at `k = 5`  `[VERIFIED — [0..21]]`

    (k=5, max S=4): 110      (k=5, max S=5): 4      (k=5, max S=6): 72

`max S` is **not** monotone in `k`: `k = 5` reaches 6, the same as `k = 1`, while `k = 2,3,4`
often sit at 4. Grid distance bounds `max S` at the two extremes (8 only at `k=0`, exactly 6
at `k=1`) and does not control it in between.

## 5. S(t) = 0 occurs everywhere

Every configuration examined has instants at which **no** runner is lonely (5 cells for the AP
grid, 7 after one move, 13 for the spread grid, 19 for E*, 27 for two clusters). Nothing here
depends on that; it is recorded because it was checked.

## 6. Related result from the summary

`AP_GRID_SUMMARY_v1` §2: the **measure** of a runner's good set is a popcorn-type function —
generic (≈ 0.1302) almost everywhere, discontinuous at every rational, the jump shrinking with
the denominator, with the AP the deepest downward jump (to zero). Leaving the AP is a jump,
not a slide.

## 7. Not tested

- Which individual **windows** slide, split or merge along a continuous path. §6 gives the
  density along a path; the trajectory of individual windows is unmeasured. The expected
  behaviour is continuous sliding with splits/merges as bad intervals cross, and the measure
  jump at commensurate points explained by exact tiling of the bad intervals — neither
  checked.
- Whether the maximal-set system is a known combinatorial object; §4b gives its coarse
  statistics only.
- `max S` for `k ≥ 6`.

## 8. Status

`[PROVED]` §1's two statements.
`[VERIFIED — exhaustive]` §2, §3 over 6,434 primitive 8-sets in `[0..14]`.
`[VERIFIED — exhaustive]` §4a over `[0..14]`, 2,032 qualifying configurations; §4b over
`[0..13]`; §4c over `[0..21]`.
`[VERIFIED — exact]` §4, §4a's examples, §5 on the named configurations.

**n = 8 is not proved.** Nothing here bounds any individual count below.
