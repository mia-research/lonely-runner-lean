# The transit mapped over fractional speeds — correcting the integer-only sweeps

2026-09-12. n = 8, individual isolation. Corrects the transit tables in
`TRANSIT_MAP_FULL_v2.md` §1 and `MMIN_RETRACTION_v1.md` §4.

## 1. What was wrong

The owner asked for the transit of a runner's speed *between* its own and its neighbour's.
Every transit table in this session used the base `(0,8,16,…,56) = 8 × (0,1,…,7)` and moved
the runner over integer values `0..8`.

That base **does** encode fractional speeds — scaled value `v` is original speed `v/8`. So
fractional speeds were tested. But only at **resolution 1/8 of the gap**, and the tables
described the positions as "integers", which concealed it.

Worse, the sample was **biased**. In a finer picture — say steps of `1/48` — the points
`v/8` are exactly `v = 0, 6, 12, …, 48`, i.e. precisely the rationals of small denominator.
Those are the configurations whose reduced form has small speeds, and therefore the fewest
isolation events. **Every point the coarse sweep looked at was a local minimum.** The
in-between speeds were never sampled at all.

## 2. The transit, mapped  `[VERIFIED]`

Base `(0,120,240,…,840) = 120 × (0,…,7)`; r1 moves over every rational `p/120` in `(0,1]`.
119 positions, exact `Fraction`, counts taken after reducing by the gcd.

| denominator of r1 | positions | min count | max count |
|---|---|---|---|
| 2 | 1 | **8** | 8 |
| 3 | 2 | **8** | 10 |
| 4 | 2 | 9 | 11 |
| 5 | 4 | 10 | 14 |
| 6 | 2 | 19 | 21 |
| 8 | 4 | 19 | 23 |
| 10 | 4 | 27 | 31 |
| 12 | 4 | 27 | 35 |
| 15 | 8 | 32 | 44 |
| 20 | 8 | 43 | 57 |
| 24 | 8 | 53 | 69 |
| 30 | 8 | 71 | 89 |
| 40 | 16 | 89 | 113 |
| 60 | 16 | 131 | 173 |
| 120 | 32 | 263 | 345 |

> **The transit is governed by the denominator of the speed, not by distance travelled.**

The count grows close to linearly in the denominator: `r1 = p/q` makes the reduced
configuration roughly `q` times larger, and the event count scales with the size of the
reduced speeds. Sample row (`v` scaled by 48): `1/48 → [139,292,302,264,232,296,332,316]`,
`1/8 → [21,54,50,46,40,52,56,56]`, `1/2 → [9,14,12,10,8,12,12,14]`.

Minimum over the whole transit: **8**, at `r1 = 1/2` and `r1 = 2/3`.

## 3. Consequences

**The transit is not a smooth curve.** Adjacent positions differ by an order of magnitude —
`5/48` gives 137 while `1/8` gives 21. Any language about a runner "passing through a dip and
recovering" describes motion through *denominators*, not through distance.

**The danger is at simple fractions, not complex ones.** Low counts occur where the reduced
configuration is small. This is the same phenomenon as the floor of 2 living among small
integer sets (`PINNED_SET_v1`), seen from the other side.

**The coarse sweeps' floor values were not wrong, but they were not evidence.** Sampling only
small denominators finds the minima — which is why the floors reported earlier were right.
It gives no information about anything else on the transit, and the shape those tables
implied was an artefact.

**Scope.** The whole framework — `p/8` witnesses, Case A/B, the grid tower — is about the
**reduced integer** configuration and its own time scale. For a runner at speed 2.3 the
natural witness denominators are eighties, not eighths (`10V` at `1/80`, verified). The
condition for `t = 1/8` with real speeds is `d mod 8 ∈ [1,7]`, a band of width 3/4, not the
integer condition `d ≢ 0 mod 8`; 2.3 satisfies it, 0.1 and 7.9 and 8.1 do not.

## 4. Status

`[VERIFIED]` §2's table, 119 positions at resolution 1/120, exact arithmetic.
`[RETRACTED]` the transit shape implied by `TRANSIT_MAP_FULL_v2` §1 and `MMIN_RETRACTION_v1`
§4 — those sampled only denominators dividing 8, which are the minima. Their floor values
stand; their portrayal of the transit does not.

**n = 8 is not proved.**
