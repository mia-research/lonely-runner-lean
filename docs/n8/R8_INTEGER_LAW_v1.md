# `(1,2,3,4,5,6,7,x)` for integer x — a closed form

2026-09-13. n = 8, individual isolation, threshold 1/8. r1 through r7 never move; r8 takes every
integer value from 8 to 160. The grid structure lives at integers, so nothing else is tested.

Artifact: `experiments/n8/ok_r8_integer_law_v1.py`.
Data: `experiments/n8/out_r8_integer_law_v1.csv`.

---

## 1. Four rules, exact  `[VERIFIED — 153 of 153, 0 violations]`

Write `k = ⌊x/8⌋` and `r = x mod 8`.

| | rule |
|---|---|
| **R1** | r8's first isolation `= 1 / (8(x − 7))` |
| **R2** | r8's tally at coverage `= k` |
| **R3** | coverage `= 1/8` if `r = 0` (a grid); `= 1/8 + 1/(64k)` otherwise |
| **R4** | the only delayed runner is `r_r`, the residue partner; r1…r7 are otherwise at `1/8` |

Tested for every integer `x` from 8 to 160. **No violations.**

R1 is the `d_min` rule: r8's nearest neighbour is r7, at distance `x − 7`. It is attained at
every single value of x, grid or not.

## 2. The table

| x | x mod 8 | grid | `d_min(r8)` | r8 moment | coverage | r8 tally | delayed |
|---|---|---|---|---|---|---|---|
| **8** | 0 | **GRID** | 1 | 1/8 | **1/8** | 1 | none |
| 9 | 1 | | 2 | 1/16 | 9/64 | 1 | r1 |
| 12 | 4 | | 5 | 1/40 | 9/64 | 1 | r4 |
| 15 | 7 | | 8 | 1/64 | 9/64 | 1 | r7 |
| **16** | 0 | **GRID** | 9 | 1/72 | **1/8** | 2 | none |
| 23 | 7 | | 16 | 1/128 | 17/128 | 2 | r7 |
| **24** | 0 | **GRID** | 17 | 1/136 | **1/8** | 3 | none |
| **64** | 0 | **GRID** | 57 | 1/456 | **1/8** | 8 | none |
| **160** | 0 | **GRID** | 153 | 1/1224 | **1/8** | **20** | none |

## 3. What the rules say

**Grid points are exactly the multiples of 8, and at each one nothing is delayed.** Coverage
returns to `1/8`, every one of r1…r7 is lonely at that instant, and no runner waits. The
configuration is a grid precisely when `8 | x`.

**Off a grid point, exactly one runner is delayed, and it is the residue partner.** `x = 12`
delays r4 and nobody else; `x = 23` delays r7 and nobody else. This is `R8_TO_NEXT_GRID_v1` §2
now with the penalty attached.

**The penalty shrinks as r8 is pushed further out.**

| x | coverage | |
|---|---|---|
| 9 | `1/8 + 1/64` | 0.14062500 |
| 17 | `1/8 + 1/128` | 0.13281250 |
| 33 | `1/8 + 1/256` | 0.12890625 |
| 65 | `1/8 + 1/512` | 0.12695312 |
| 129 | `1/8 + 1/1024` | 0.12597656 |

`1/(64k) → 0`, so **coverage tends to `1/8` from above**. Pushing r8 away makes the residue
collision asymptotically harmless: in the limit the pack behaves as though r8 were not there, and
the seven of them cover at the AP's own time.

**r8 collects `k` turns while the pack collects one.** At `x = 160` it is lonely twenty times
before r1…r7 have been lonely once — because its `d_min` is 153, so it is free from `t = 1/1224`
onward while the pack must wait for `1/8`.

## 4. Status and scope

`[VERIFIED — exact, 153 of 153]` all four rules.
`[PROVED — arithmetic]` R1 is the forced bound `t ≥ 1/(8·d_min)`, attained here at every x.

**Scope.** One family: r1…r7 fixed at `1..7`, r8 integer in `[8,160]`. Nothing above 160. No
other runner moved, and no non-integer x — deliberately, since the grid structure is an integer
phenomenon. R3's `1/(64k)` form is fitted to this family and verified on it; it is not derived.

**Not established.** Why the penalty is exactly `1/(64k)`. Whether an analogous closed form
exists when a middle runner is pushed out instead of the end one — it cannot be tested the same
way, because a middle runner would have to cross its neighbours.

**n = 8 is not proved here, and is not the target here.**
