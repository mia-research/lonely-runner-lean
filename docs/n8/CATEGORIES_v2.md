# The correct categories — v2, with v1's weighting withdrawn

`CATEGORIES_v1.md` gave the right *partition* and then attached a weighting that does not measure
what it was used to measure. **The weighting is withdrawn.** The partition stands.

## What was wrong

v1 sampled **uniform random 7-subsets of `[1,N]`** and reported that the proved categories hold
`0.06%` of instances, falling with `N`.

Two faults, and the second is fatal:

**1. Under that measure every structurally-defined family has share → 0.** "`d_min` divides every
disparity" is a structural condition, so of course its uniform-box density falls like `7/N`. The same
argument would report that the primes are `0%` of the integers. That is a fact about the measure, not
about the family. Branch A is proved for **every** integer-reading profile with no collider, at
**arbitrary magnitudes** and — since `GeneralOrder.spine_all_or_nothing` — at **arbitrary order**.
That is an infinite family closed under a structural description. Calling it `0.04%` says nothing
about it.

**2. The bulk that v1 called "open" is mostly trivial.** Measured, 12,000 random speed sets, difficulty
by `k` (the number of non-integer readings):

| `k` | instances | clears instantly at `R = 1` | median `R` | max `R` |
|---|---|---|---|---|
| 0 | 281 | 45.2% | 1.0043 | 1.3009 |
| 3 | 243 | 31.7% | 1.0236 | 1.8156 |
| 5 | 2,155 | 38.3% | 1.0465 | 3.6957 |
| **6** | **8,563** | **60.3%** | **1.0000** | 4.1480 |

`R = 1` means the profile clears at the first instant — no cascade, nothing to prove. **`k = 6` is the
*easiest* category by that measure**, and it is the one v1 weighted at 98.72%. A count of instances is
not a count of remaining work.

**What is true in the same table:** the hard tail also lives at high `k` — max `R` of `4.15` against
`1.30` at `k = 0`, and every deep case on file (`R ≈ 11.6–11.97`) has non-integer readings. So `k ≥ 3`
contains both the most trivial instances and the hardest ones. That is a reason to study it, and not
a reason to weight it.

## The partition, without the weighting

| `k` = number of non-integer readings | status |
|---|---|
| 0 — integer readings | **Branch A `[PROVED]`**: no collider ⟹ clears at `R = 1`, arbitrary magnitudes, **arbitrary order**. Branch B (some collider) **open**, verified exhaustively on readings `≤ 40` and on `[2,30]` |
| 1 | **`[PROVED]`** — nearest-integer walk, Thm 6.9 |
| 2 | **`[PROVED]`** — lattice crossing, Thm 6.18 |
| 3–6 | **open** |

Each row is a structural family, infinite, and closed under the description that defines it. No row
is a percentage of anything.

## Rows that should not appear (unchanged from v1)

- **"General real / irrational"** — reduces to integer speed sets; not a sibling category.
- **"`R < 16`"** — a property of `k ≥ 1`, and the same problem as the rational frontier.
- **"Finite middle band `8 ≤ bᵢ ≤ 27`"** — defined by a withdrawn threshold.
- **"`s₇·R ≤ 89`"** — not a bound: exceeded 410 times in 6,000 profiles, reaching 3001. True only as a
  description of the maximiser, where `s₇·R = 89` exactly on the two largest deep cases.

## The error, named

This is the project's recorded deflationary failure mode, in a new dress: an absence in the measure
became a deficiency in the result. The tell was reporting a **percentage** for a family that is
defined structurally rather than statistically, and then reading the percentage as progress. Any
future weighting of these categories needs a measure that tracks **difficulty** — `R`, margin, or
depth — not instance counts in a box.
