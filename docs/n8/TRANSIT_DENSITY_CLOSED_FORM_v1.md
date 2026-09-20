# The one-runner transit has an exact closed form — and the popcorn plateau is 25/192

2026-09-12. **`n = |V| = 8`** throughout: the speed set is `(0,1,2,3,4,5,6,r)`, eight runners,
threshold `1/8`, seven differences per runner. The `0` is a translation of an existing runner,
not an adjoined one ([[feedback_count_the_runners_given_2026_09_12]]).

Answers the open item at `AP_GRID_SUMMARY_v1` §8 ("whether the generic measure 0.1302 has a
closed form") and corrects the explanation at `AP_GRID_SUMMARY_v1:53`.

---

## 1. The mechanism: a one-runner transit is a 2-torus problem

Move one runner of the AP to speed `r`, leaving the other seven at `J`. For the **moved**
runner the seven constraints are `‖(r − j)t‖ ≥ 1/8`, `j ∈ J`. Put

    y = t mod 1,    x = r t mod 1     so    (r − j)t = x − j y.

For `r` irrational, `(x, y)` equidistributes on `T²` (Weyl; the region's boundary is a finite
union of segments, so it is a null set). Hence

> **density = area of `A_J = {(x,y) ∈ T² : ‖x − j y‖ ≥ 1/8 for all j ∈ J}`.** `[PROVED | Weyl]`

The seven constraints never become independent, however far the runner travels: the
differences `r − j` are pairwise separated by the **fixed integers** `j − k`. The system has
**two** degrees of freedom, not seven, for every `r`. That is the whole content of the
plateau.

## 2. The plateau value  `[PROVED — exact]`

`A_J` is computed exactly: for fixed `y` the admissible `x` are the complement of seven arcs
of length `1/4` centred at `j y`, so the integrand is piecewise linear in `y` with breakpoints
only where `‖(j−k)y‖ = 1/4` — multiples of `1/(4|j−k|)`. Integrated over that grid in exact
`Fraction`, with a per-cell linearity check (entry, exit, midpoint).

| moved runner | `J` | density | value |
|---|---|---|---|
| **7** (endpoint) | `0..6` | **`25/192`** | 0.1302083 |
| **1** (interior) | `0,2,3,4,5,6,7` | **`853/6720`** | 0.1269345 |
| **3** (interior) | `0,1,2,4,5,6,7` | **`941/6720`** | 0.1400298 |

Grid stable at `N = 240, 480, 720` (endpoint) and `N = 3360` (interior), 0 nonlinear cells.
**The control fires**: at `N = 24` the check reports 6 nonlinear cells and a wrong area
(`41/288`), so an insufficient grid is detected rather than silently averaged.

`25/192 = 0.130208333…` is the 0.13021 measured in `AP_GRID_SUMMARY_v1` §2.

**The plateau is not one number.** It depends on which runner leaves the grid, and moving an
interior runner (3) is *safer* than moving the endpoint (7), which is safer than moving
runner 1.

## 3. The other seven runners factorise exactly  `[PROVED]`

For a runner `i` that did **not** move, six constraints are fixed integers (functions of `y`
alone) and exactly one involves `r` (a function of `x` alone). The region is therefore a
**product**, and

> **density(`i`) = `(3/4) · |G_fixed(i)|`**,

where `G_fixed(i)` is runner `i`'s good set against the six other stationary runners. The
`3/4` is the moving runner's own contribution, and it is the same for every `i` and every `r`.

Endpoint transit (runner 7 moved), full profile — exact, and matched by direct computation at
`r = 7 + 1/401` to six decimals:

| runner | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 (moved) |
|---|---|---|---|---|---|---|---|---|
| density | `21/320` | `7/64` | `1/4` | `11/32` | `1/4` | `7/64` | `21/320` | `25/192` |
| | 0.0656 | 0.1094 | 0.2500 | 0.3438 | 0.2500 | 0.1094 | 0.0656 | 0.1302 |

A palindrome peaked at the centre. **The ends of the pack are five times more exposed than the
centre**, which is the measure-side statement of `OBSERVATIONS` item 23 (moving a runner toward
the centre costs more than moving it away).

## 4. Why the popcorn structure is real

The dichotomy is Weyl's, not an artefact of how the measure was taken:

- **`r` irrational** — the orbit `{(rt, t)}` equidistributes; density = area, exactly.
- **`r = p/q`** — the orbit closes onto a geodesic; density = average over that closed orbit,
  which deviates from the area, by more for small `q`.

`[VERIFIED — q ≤ 401]` Direct exact densities at `r = 7 + 1/q`: `q = 53 → 0.130128988`,
`101 → 0.130188542`, `211 → 0.130208920`, `401 → 0.130208525`, against `25/192 = 0.130208333`.
Never equal at finite `q`, approaching it as `q` grows. Small denominators sit far off:
`15/2 → 381/2860`, `29/4 → 36121/263900`, `8 → 3/32`.

This is the same fact as `TRANSIT_FRACTIONAL_v1`'s "the transit is governed by the denominator
of the speed, not by distance travelled" — stated on the measure side, where it has a limit.

## 5. Retraction

`[RETRACTED]` `AP_GRID_SUMMARY_v1:53`: "The generic value is 0.1302, not `(3/4)⁷ = 0.13348`;
the seven differences of eight speeds are not fully independent."

The measurement stands; the explanation does not, as stated. Any seven distinct positive
integers are the difference set of eight speeds, so the sentence claims something about eight
speeds in general. Over 60 generic difference sets drawn from `[900,4000]` the density has
**mean 0.13347, median 0.13346** — `(3/4)⁷ = 0.133484` to four figures. Dependence is a
property of the **transit family**, where six differences stay fixed while one slides, not of
eight speeds. `[VERIFIED — 60 sets]`

## 6. Scope, and what is not claimed

- §1–§3 are stated for `n = 8` and this base, but nothing in the derivation uses either: for
  any `n` and any fixed `J`, a one-runner transit has density = area of
  `{(x,y) : ‖x − jy‖ ≥ 1/n, j ∈ J}`, and non-moved runners factorise as `(1 − 2/n)·|G_fixed|`.
  The general statement has **not** been tested beyond the rows above.
- §4's convergence at rational `r` is verified to `q = 401`, **not proved**. A proof needs a
  discrepancy bound for the closed orbit; none is given here.
- Density is not count. All of this is measure, so it says nothing about the number of
  components, and **nothing here bounds any count below**.
- This concerns transits from the AP/grid backbone only. It is not a statement about
  configurations at grid distance `k ≥ 2` reached by other means.

## 7. Status

`[PROVED | Weyl]` §1's reduction to a `T²` area.
`[PROVED — exact]` §2's three areas; §3's factorisation and the eight-runner profile.
`[VERIFIED — q ≤ 401]` §4's convergence.
`[VERIFIED — 60 sets]` §5's generic value.
`[RETRACTED]` `AP_GRID_SUMMARY_v1:53`'s explanation.
`[OPEN]` The jump magnitude at `p/q` as a function of `q` (`OBSERVATIONS` item 41) — this note
gives the limit, not the rate.

**n = 8 is not proved.**
