# The doors on arrangements, v2 — four corrections from the author, checked

**Date:** 2026-09-18. Supersedes `DOORS_ON_ARRANGEMENTS_v1` (same day).
**Lean:** `LRC/Cascade/Arrangement.lean`, `LRC/Spec/Doors.lean`. Zero `sorry`, all axiom-clean.
**Scripts:** `experiments/n8/doors_v2/`.

v1 made four statements the author corrected. Each is dealt with below by running the check, not by
restating. **Three of the four corrections stand and v1 was wrong; the fourth is confirmed and now
has a ceiling.**

---

## C1. "First reading?" — v1 printed statements containing opaque terms and called it a frame check

**v1 was wrong, and the error was structural, not cosmetic.** v1 printed

```
DoorArrives v k  ∃ N, move 8 (diffSet v k) (move^[N] firstReading) = move^[N] firstReading
```

and said "so that is the test". A reader cannot check a frame through `firstReading`, `diffSet` or
`move`. The whole chain is now printed by Lean itself in
`experiments/n8/v9_6_door_dependency_audit_v1.out`:

```
sep v k i t          = v i * t − v k * t
InWay v k i t        = circDist (sep v k i t) < 8⁻¹
circDist x           = min (Int.fract x) (1 − Int.fract x)
flankOpening n e j   = (j + n⁻¹) / e
diffSet v k          = image (fun i => |v i − v k|) (univ.erase k)
leastDisp v k        = (diffSet v k).min'
firstReading v k     = 1 / (8 * leastDisp v k)
inWay n d t          = circDist (d * t) < n⁻¹
nextOpening n d t    = (⌈d*t − n⁻¹⌉ + n⁻¹) / d
move n ds t          = fold max t (fun d => if inWay n d t then nextOpening n d t else t) ds
```

**And `j` is a lap count.** `flankOpening 8 e j = (j + 1/8)/e` is the instant at which the runner of
disparity `e` has gone `j` whole laps past the subject and then a further `1/8` — the `j`-th time it
steps out of the subject's zone ahead. `j = 0` is the first such instant, `1/(8e)`. So "which
`(i, j)`" means: **which runner's disparity to read the opening off, and how many of its laps to wait**.
v1's table row said "no rule names which `(i, j)` for `j > 0`" without ever saying that, which made
the row unreadable.

---

## C2. Door 2 — "nothing bounds the number of moves" was wrong

The author's position: this is resolved by the scale difference between the subject and its
neighbour. v1 recorded it as open. **The check says the author is right about the object; what is
missing is only the proof.**

**The move count does not run away.** Max moves by speed range, random plus targeted at the shape
that maximised moves (tiny least disparity, everything else clustered high):

| range | sets | max moves |
|---|---|---|
| `[1,25]` | 66,717 | 19 |
| `[1,40]` | 79,011 | 16 |
| `[1,60]` | 79,461 | 18 |
| `[1,90]` | 79,459 | 16 |
| `[1,140]` | 79,389 | 16 |
| `[1,200]` | 79,436 | 21 |

Flat, while `max/min` runs to 200. It is not a function of the overall spread.

**The scale statement, measured.** Read the arrival instant in the **nearest runner's own laps**,
`τ = e·t` for `e` the least disparity. Exhaustively — every primitive 7-subset, not a sample:

| sweep | primitive 7-sets | non-arrivals | max `τ` |
|---|---|---|---|
| all of `[1,18]` | 31,788 | 0 | `33/56 = 0.58929` |
| all of `[1,20]` | 77,400 | 0 | `33/56` |
| all of `[1,22]` | 170,213 | 0 | `33/56` |

Same constant all three times, attained at `(2, 6, 8, 9, 11, 14, 15)`. And `33/56 = (4 + 1/8)/7`.

**So: the cascade arrives inside the nearest runner's first lap.** The nearest disparity sets the
clock; however far out of scale the other six are, the cascade is finished before that clock
completes one turn. That is the author's scale statement, and it is a far sharper thing than "the
instants are capped".

**In Lean.** `DoorFirstLap v k : ∀ N, move^[N] (firstReading v k) ≤ 1 / leastDisp v k`, with
`doorCapped_of_doorFirstLap` and `lonelyRunnerAt8_of_doorFirstLap`. `[EMPIRICAL — exhaustive on
[1,22]; the cap is NOT proved]`. The Lean proves only that the cap **suffices**.

**What door 2 now needs** is no longer "something that bounds the moves". It is: **prove the cascade
never passes `t = 1/e`.** Measured headroom is large — it never passes `0.59/e`.

---

## C3. Door 3 — "eight gaps, because there is a gap between r1 and r8"

**v1 was wrong, and in the way that matters: it quoted a number from the wrong frame.**

v1 said "7 runners × 1/4 = 7/4 > 1". That arithmetic is correct *in the time frame* — each of the
seven other runners blocks a set of instants of density `1/4`, so the union bound gives `7/4` and is
useless. But it was quoted beside a discussion of runners and gaps, where the object is different and
the count is different.

**The gap frame.** At an instant the eight runners cut the circle into **eight** gaps summing to `1`
— eight, not seven, because the circle closes and there is a gap between the last runner and the
first. The subject owns two of them, and

> the subject is lonely **exactly when** its gap ahead and its gap behind each reach `1/8`.

**Checked:** 30,267 random instants, `0` disagreements with `LonelyAt`, and the eight-gaps-sum-to-one
identity asserted on every one of them. 116 of the lonely cases were exactly tight.

**In Lean:** `gapAhead`, `gapBehind`, `lonelyAt_iff_gaps`, `gapAhead_add_gapBehind_le_one`,
`gapAhead_nonneg`, `gapBehind_nonneg`.

**What the count actually is.** The subject needs `1/8 + 1/8 = 1/4` of the circle sitting in its own
two gaps, out of the `1` available across all eight. That is **feasible**, with equality throughout
being the arithmetic progression. There is no `7/4` here and no wall. The `7/4` belongs to the
union-bound-on-time argument and should only ever be quoted as a statement about *that* method.

---

## C4. Door 5 — "let's see if we can prove the other direction, I think it inverts"

**Confirmed, and now with a ceiling and a refuted strengthening.**

Rank the subject's disparities from the large end, `1` = largest. For each set, the best rank at which
a lonely opening exists (searching `j < e`, which `exists_lonelyAt_iff_bounded` proves exhaustive):

| best available rank | count |
|---|---|
| 1 (the largest disparity) | 35,785 |
| 2 | 84 |
| 3 | 3 |
| **4 or worse** | **0** |

35,872 sets: random 7-subsets of `[1,20]`, `[1,30]`, `[1,45]`, `[1,70]`, **plus every primitive
arithmetic progression** `a + d·i` with `a ≤ 39`, `d ≤ 24`. Zero sets with no lonely opening anywhere.

**So it inverts, as predicted: the largest disparity is the flank in 99.76% of cases.** And three is
the right number — rank 3 is attained, so `DoorThreeLargest` cannot be tightened to two.

**But "largest flank" alone is refuted.** `(2, 3, 5, 7, 8, 13, 16)` has **no** lonely opening at
flank `16` for any `j < 16`; it needs flank `13`, lap `1`, i.e. `t = 9/104`. Verified termwise:
residues `18, 27, 45, 63, 72, 13, 40` out of `104`, every one at circle distance `≥ 13/104 = 1/8`.

The three sets needing rank three: `(1,3,5,7,8,14,16)` at flank `8` lap `2`; `(1,4,5,6,7,8,14)` at
flank `7` lap `2`; `(1,3,4,5,7,12,16)` at flank `7` lap `3`.

**In Lean:** `DoorLargestFlank` is stated and `doorThreeLargest_of_doorLargestFlank` proves it is a
special case of door 5, so the refutation lands on the strengthening and not on door 5.

**Why the largest flank is the natural candidate** — a mechanism, not a fit. At the largest disparity
`b`, every other ratio `d/b` lies in `(0,1]`. So between consecutive openings of `b` no other runner
advances a full lap, and none can step over the clear band. That is exactly the hypothesis of
`Flanks.exists_clear_step` (`n ≥ 4`, `0 < f < 1`) for each runner separately. **What is missing is
simultaneity** — `exists_clear_step` clears one runner at a time, and nothing yet clears six at once.
That is the shape of a proof of door 5's converse, and the 87 sets where rank 1 fails are where the
six cannot be aligned.

---

## What is not claimed

Nothing here proves Existence. `DoorFirstLap`'s cap is `[EMPIRICAL]`, exhaustive only on `[1,22]`.
Door 5's converse is `[EMPIRICAL]` on 35,872 sets and is not proved in either direction beyond
`lonelyForSubject_of_threeLargest`. The `exists_clear_step` route to door 5 is a sketch with a named
gap, not an argument.
