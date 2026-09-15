# The near-extreme cases, and the flank lemmas in Lean

2026-09-15. Follows `T4_FLANKS_v3.md` §4, next actions 1 and 3. Scripts in `experiments/n8/` (outputs `.out`), exact integer
arithmetic: `flank_near_extreme_v1.py`, `flank_one_free_v1.py`, `flank_sharer_free_v1.py`.

---

## 1. How the shadowed flanks are shadowed, where free flanks run out  `[VERIFIED — exhaustive in range]`

Runners with at most two free flanks at order 8 (every 8-subset of `[1, 20]`: 4,538 with two, 16 with one), and with one free
flank at order 5 (every 5-subset of `[1, 30]`: 4,086). For each shadowed flank, the smallest set of runners holding all its
openings:

| kind | order 8 | order 5 | most common denominators of the smallest set |
|---|---|---|---|
| **dead**: one exact slot-sharer | 4,064 | 5,972 | `(1)` |
| **small**: 2 or 3 runners | 8,638 | 5,068 | order 8: `(3,3,3)` 4,010, `(2,2)` 2,234, `(2,4,4)` 2,184, `(5,5,5)` 208; order 5: `(2,2)`, `(3,3,3)`, `(5,5,5)`, `(7,7,7)` |
| **wide**: 4 or more runners | 8,564 | 0 | `(5,5,5,5)` 2,184, `(2,8,8,8,8)` 2,172, `(2,3,6,6)` 1,575, `(7,7,7,7,7,7)` 792, `(2,4,8,8)` 260, `(3,9,9,9,9)` 254 |

**Reading.** Even the wide shadows are not generic. Their runners' ratios to the flank share one small denominator, the flank's
own lattice at a coarse size, so the openings behave as a small cyclic group that a handful of runners fill. With integer speeds
every ratio to a flank `e` has denominator dividing `e`, and in this range those are at most 20. At order 5 a flank has only three
other runners, so wide shadows cannot occur.

## 2. The one-free-flank runners at order 8 are one arrangement  `[VERIFIED — exhaustive in range]`

All 16 have the difference set **`{2, 3, 4, 5, 6, 7, 16}`**: the consecutive progression 2–7, plus `16 = 8·2`, an exact slot-sharer
of the nearest runner. (They are the translates and reflections of one arrangement within `[1, 20]`.)

| flank | shadowed by |
|---|---|
| 2 | dead: 16 |
| 3 | small `(3,3,3)` |
| 4 | small `(2,4,4)` |
| 5, 6, 7 | wide `(5,5,5,5)`, `(2,3,6,6)` or `(2,3,3,6)`, `(7,7,7,7,7,7)` |
| **16** | **free**: lonely at its first opening `k = 1`, `t = 9/128` |

**The mirror of Theorem 4.8 at the fastest flank** `[DERIVED — band identity at a flank opening]`. At flank `e`'s `k`-th opening,
runner `j` is clear iff `(d_j/e)·(nk + 1)` is at least 1 from every multiple of `n`, i.e.

    d_j/e  ∈  ⋃_M [ (nM + 1)/(nk + 1),  (nM + n − 1)/(nk + 1) ].

- `e = d_min`, `k = 0`: every ratio in `[1, n − 1]`, which is Theorem 4.8.
- `e = d_max`, `k = 1`: every other difference in `[d_max/(n + 1), (n − 1)·d_max/(n + 1)]`. At order 8 that is
  `[d_max/9, 7·d_max/9]`.

The extreme arrangement satisfies the second with room to spare (`16/9 ≤ 2`, `7 ≤ 112/9`). So in this range, where free flanks run
out, the one that remains is the fastest flank, and it is decided at its first opening.

## 3. A hypothesis refuted  `[VERIFIED — exact]`

*"A runner that is an exact slot-sharer of some flank has its own flank free."* It held in 317,686 cases and failed in 24,656 at
order 8, e.g. `(1, 2, 3, 4, 5, 6, 8, 9)`, subject 1, sharer 8. At order 5: 148,510 held, 6,788 failed. Among runners with at most
two free flanks, the free flanks are neither mostly sharers nor mostly the largest difference.

## 4. In Lean: the flank lemma and the one-runner lemma  `[PROVED-LEAN — Cascade/Flanks.lean]`

| declaration | statement |
|---|---|
| `lonely_iff_exists_flank` | lonely at some positive instant ⟺ some flank has a lonely opening `(k + 1/n)/e` |
| `position_at_flank` | at a flank opening only the ratio `d/e` enters |
| `integer_ratio_clear_iff` | an integer ratio `A` is clear at every opening iff `n ∤ A` |
| `fractional_ratio_circDist` | otherwise only the fractional part moves: circle distance at opening `k` is that of `k·f + (d/e)/n` |
| `exists_clear_step` | for `n ≥ 4` and `0 < f < 1`, some `k·f + c` is at least `1/n` from every integer — proved by following the nearest integer, no counting |
| `lonely_opening_of_one_fractional`, `stops_of_one_fractional` | a flank with one fractional ratio, all others integers not divisible by `n`, has a lonely opening, and the cascade stops |

Gate `scripts/cascade/gate.sh`: build 3,352 jobs, 0 `sorry`, **161 of 161** theorems axiom-clean. The count rose from 152 as it
should.

**Not yet in Lean:** the flank sum criterion (`T4_FLANKS_v3` §3(d)) and the order-8 half-integer pair result (§3(b)). They need a
pigeonhole for simultaneous approximation and a count of multiples of `1/c` in an arc. That is substantially more formal work
than §4, and it waits on the owner's ruling on whether counting sits inside the framework.
