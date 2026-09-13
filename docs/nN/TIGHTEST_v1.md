# The tightest configurations: a clear set of one instant

2026-09-13. Scripts `experiments/nN/margin_count_v1.py`, `experiments/nN/tightest_v1.py`
(outputs `.out` beside each). Lean: `ConstructionN.near_ap_top_returns`.

**RING-FENCE.** General-`n` line. `LRC/Construction8/` untouched, digest
`578022e0296ce565ec601655747d1e5cdc614a9efa2cced6540162e698f43b9d`.

`EXHAUSTIVE_OTHER_ORDERS_v1.md` answers *does the procedure return*. This asks *by how
much*, and the answer locates where part 7 is tightest.

---

## 0. The first attempt measured the wrong thing

The natural quantity is the **length** of the clear set. It is uninformative, and the
manuscript already says why: §6.1's ground is that the arithmetic progression's clear set is
a **finite set of points**, so its length is `0`. The minimum over any family containing an
AP is `0`, attained, and carries no information.

The informative quantity is the **count** of clear components. Counting is not measuring,
and nothing here is a route to part 7 — §6.1 closes that to size arguments at any strength.
This locates where the procedure is tightest, which is a different question.

---

## 1. The clear set can be a single instant

Exhaustive, `n` distinct positive integer speeds with gcd `1`, no runner pinned at `0`,
exact arithmetic, open zones never merged.

| `n` | `φ(n)` | speeds in | instances | failures | fewest clear components |
|---|---|---|---|---|---|
| 5 | 4 | `[1,26]` | 322,180 | 0 | **1** |
| 6 | 2 | `[1,22]` | 444,864 | 0 | **1** |
| 7 | 6 | `[1,18]` | 222,768 | 0 | **1** |
| 8 | 4 | `[1,17]` | 194,480 | 0 | **1** |
| 9 | 6 | `[1,15]` | 45,045 | 0 | **1** |

**The arithmetic progression is not the tightest case.** It has `φ(n)` clear instants — four
at `n = 8`. There are configurations with **one**: a single instant in the entire window at
which the runner is lonely, and nothing else.

They are not rare. At `n = 8`, speeds `≤ 17`: 2,794 runner-instances out of 194,480.

---

## 2. Where the single instant sits

Two positions, and no others in the range tested.

| `n` | single-instant runners | at `u = 1/n` | elsewhere |
|---|---|---|---|
| 5 | 3,845 (`V=18`) | 3,653 | 192 |
| 6 | 2,488 (`V=16`) | 2,400 | 88 |
| 7 | 4,708 (`V=18`) | 4,692 | 16, all at `8/49` |
| 8 | 2,794 (`V=17`) | 2,792 | 2, both at `9/64` |

**`u = 1/n`** is the `k = 0` opening of the reading `s = 1` — the nearest runner's own zone.

**`8/49` at `n = 7` and `9/64` at `n = 8`** are both `(n+1)/n²`: the **`k = 1` opening of
the reading `s = n`**. That is §6.3's fragmenting reading, the one that cuts the window into
`n−1` zones and `n−2` gaps. Every exception in the range tested is at that one place —
checked individually, not inferred from the totals.

Both positions have the form `(nk+1)/(ns)`, so §7.2's statement — the first instant is
always an **opening** — holds in the tightest cases too, and there it is the *only* instant.

**Which runner.** Top, middle and bottom all occur, middle most often. The first extremal
examples were all the top speed and that was misleading; the pattern does not hold.

---

## 3. A scope correction worth recording

At `V = 14` and `V = 13` the figure for `n = 7` and `n = 8` was **528 of 528** and **128 of
128** at `u = 1/n` — an apparently exceptionless law. Raising the bound to 18 and 17 found
the exceptions. Had the smaller bound been reported, "always at `u = 1/n`" would have gone
out as a law and been false.

---

## 4. What is proved

The extremal family is `(1, 2, …, n−1, n+1)`, its displaced top runner. Its differences are
`2, 3, …, n`, so `d_min = 2` and its readings are `k/2` for `k = 3, …, n`.

> **`ConstructionN.near_ap_top_returns`.** For every `n > 1` and every reading `k/2` with
> `3 ≤ k ≤ n`, that reading is clear at `u = 1/n`.

Proved from `band_identity`: the nearest multiples of `n` to `k/2` are `0` and `n`, at
distances `k/2 ≥ 3/2` and `n − k/2 ≥ n/2 ≥ 1`. So **the tightest observed family returns at
every `n`**, machine-checked.

**What is not proved.** That its clear set is a *single* point. That is the empirical
finding of §1, at the orders and bounds stated, and it is not claimed beyond them.

---

## 5. Scope

Exhaustive over the stated bounds and nothing beyond them; the bounds are small and fall as
`n` rises. Integer speeds only. All `[EMPIRICAL]` except §4. Nothing here bears on whether
LRC holds at any order, and part 7 is neither stated nor approached.
