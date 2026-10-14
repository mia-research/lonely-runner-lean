# Working note — BSM transits, every runner varied toward its neighbour

2026-09-12. n = 8, individual isolation. AP `(1,…,8)`. Each runner in turn varied upward in
steps of `1/10` toward the next grid point; every runner's loneliness windows recorded over
one full cycle. Boundary Set Method, exact `Fraction`.

Script: `experiments/n8/bsm_transit.py`.

## 1. Method

`bsm_good(D)` builds the boundary set `t = (8k ± 1)/(8d)` for each `d ∈ D`, then evaluates
**boundary points and open cells separately**. The bad set of a single `d` is the *open*
interval between its two boundaries, so an endpoint can be lonely while the cell interior is
not — e.g. `d = 4`, `t = 7/32`: `‖4·7/32‖ = ‖7/8‖ = 1/8` exactly, lonely, while all of
`(7/32, 9/32)` around `t = 1/4` is not.

Each open cell is probed at three interior points; disagreement would mean the boundary list
is incomplete. **0 cell anomalies across every run in this note.**

Controlled against the independent interval-merge construction: **0 disagreements over 300
constraint sets**.

A first implementation marked a cell lonely when its entry and exit values agreed, and so
swallowed those open bad intervals whole — 93 disagreements out of 120, reporting r4 with 2
windows instead of 6. Corrected before any transit below was run.

## 2. Comparability

Cycle length changes along a transit, because it is set by the denominator of the varied
speed: 1 at the AP, then 10 for `x.1, x.3, x.7, x.9`, 5 for `x.2, x.4, x.6, x.8`, 2 for `x.5`.
Raw window counts are therefore **not comparable across rows**. All tables below report
**windows per unit time** = count / cycle.

## 3. The AP

    r1  r2  r3  r4  r5  r6  r7  r8
   4.0 8.0 8.0 6.0 6.0 8.0 8.0 4.0      cycle 1

r1 and r8 are the scarcest, and their four windows are isolated **instants**
(`1/8, 3/8, 5/8, 7/8`, zero width), not intervals. Every other runner has intervals.

## 4. Per-transit minima

| runner varied | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 |
|---|---|---|---|---|---|---|---|---|
| worst rate over the transit | **2.0** | 2.4 | 2.4 | 2.4 | 2.8 | 2.8 | 2.8 | 3.2 |
| attained at | 1.8 | 2.8 | 3.6, 3.8 | 4.2, 4.8 | 5.2, 5.6, 5.8 | 6.4, 6.6 | 7.2 | 8.2, 8.4, 8.6 |

**Floor across all eight transits: 2.0.** Nothing approaches zero.

The gradient is monotone in position: moving r1 costs the most, moving r8 the least. That
matches the AP profile — the runner at the bottom of the range has the fewest ways to
separate itself, and displacing it makes that worse than displacing anyone else.

## 5. Structure

**The moved runner becomes the scarcest.** True in every transit, with one exception: varying
**r7** makes **r8** scarcer than r7 itself (at `r7 = 7.2`, r7 = 3.20 while r8 = 2.80). The two
top runners are coupled.

**The extremes are reciprocal.** r1 and r8 both sit at 4.0 at the AP and each is *released*
when any other runner moves — in the r8 transit r1 climbs 4.0 → 6.8; in the r1 transit r8
climbs 4.0 → 7.2. Whichever extreme stays put gains.

**`x.5` is the recovery point for most runners.** Best position in the transit for r3 (4.50),
r4 (4.00), r5 (4.50), r6 (4.00), r8 (5.00), and it carries the shortest cycle (2). It is
**not** best for r2 or r7.

**Middle runners start richest and fall furthest.** r4, r5 at 6.0 and r2, r3, r6, r7 at 8.0
at the AP; once moved, all land in the same 2.4–3.3 band regardless of where they started.

## 6. Scope

This is the integer-reduced picture at its own time scale. A varied speed `p/q` scales to an
integer configuration `q` times larger, which is why the cycle and the raw counts move with
the denominator (`TRANSIT_FRACTIONAL_v1`).

Ten sample points per transit, denominators dividing 10 only. Denominators coprime to 10 are
not represented, and by `TRANSIT_FRACTIONAL_v1` §2 the counts there would be larger, not
smaller — so the minima above are not expected to be beaten by finer sampling, but that is an
expectation, not a check.

## 7. Status

`[VERIFIED — exact]` §3–§5, BSM with 0 cell anomalies, controlled against an independent
construction over 300 sets.
`[RECORDED]` §1's implementation defect and its correction.

**n = 8 is not proved.**
