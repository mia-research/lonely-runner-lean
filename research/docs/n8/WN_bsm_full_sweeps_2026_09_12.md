# Working note — full-range BSM sweeps, every runner, both directions

2026-09-12. n = 8, individual isolation. Extends
`WN_bsm_transits_all_runners_2026_09_12.md` (upward only) to the complete range: each runner
swept from its **lower** neighbour to its **upper** neighbour in steps of `1/10`, with every
runner's loneliness recorded over one full cycle.

152 positions. Boundary Set Method, exact `Fraction`, **0 cell anomalies at every position**.
Script `experiments/n8/bsm_transit.py`. Rates are windows per unit time (count / cycle),
since cycle length tracks the denominator of the varied speed.

## 1. Mirror symmetry  `[VERIFIED — exact]`

`AP (1,…,8)` is symmetric under `s → 9−s`. The sweeps respect it exactly:

| pair | mirrors |
|---|---|
| r1 ↔ r8 | **yes** |
| r2 ↔ r7 | **yes** |
| r3 ↔ r6 | **yes** |
| r4 ↔ r5 | **yes** |

Every rate in the r`k` sweep at speed `s` equals the rate in the r`(9−k)` sweep at `9−s`,
for all four pairs across the whole range. So half the map is redundant, and any asymmetry
in a result is an error signal.

## 2. The directional law  `[VERIFIED — all eight runners]`

The centre of the pack is `4.5`. Splitting each sweep into motion **inward** (toward 4.5) and
**outward** (away from it):

| runner | AP rate | worst moving **inward** | worst moving **outward** | inward worse? |
|---|---|---|---|---|
| r1 | 4.00 | **2.00** at 1.8 | 3.20 at 0.4 | yes |
| r2 | 8.00 | 2.40 at 2.8 | 3.20 at 1.2 | yes |
| r3 | 8.00 | 2.40 at 3.6 | 2.80 at 2.4 | yes |
| r4 | 6.00 | 2.40 at 4.2 | 2.80 at 3.2 | yes |
| r5 | 6.00 | 2.40 at 4.2 | 2.80 at 5.2 | yes |
| r6 | 8.00 | 2.40 at 5.2 | 2.80 at 6.4 | yes |
| r7 | 8.00 | 2.40 at 6.2 | 3.20 at 7.2 | yes |
| r8 | 4.00 | **2.00** at 7.2 | 3.20 at 8.2 | yes |

> **Moving a runner toward the centre of the pack costs it more isolation than moving it the
> same distance away.** Eight runners, no exceptions.

The upward-only sweeps could not see this: for r1..r7 upward *is* inward, so every earlier
row was the expensive direction, and r8's upward row was the cheap one — which is why r8
looked anomalously robust (worst 3.2) in the previous note. It is not robust; it was being
measured in the other direction.

## 3. The floor

**Global minimum over all 152 positions: 2.00**, attained exactly twice —

    r1 at 1.8   and   r8 at 7.2

which are mirror images of each other under `s → 9−s`. Both are an **extreme runner displaced
inward toward its neighbour**. That is the worst configuration in the whole map, and the two
occurrences are the same configuration seen from opposite ends.

Nothing anywhere approaches zero.

## 4. Other structure

**`x.5` is a recovery point throughout.** The moved runner scores 4.50 at every half-integer,
rising to 5.50 at `0.5` and `8.5` (the outermost half-steps). These also carry the shortest
cycle, 2.

**The moved runner holds the minimum almost everywhere**, the exceptions being the `x.5`
points, where another runner takes over: at `r1 = 0.5` the minimum is 5.00 held by r4 and r5;
at `r4 = 4.5` it is 4.00 held by r1; at `r8 = 7.5` it is 4.00 held by r4.

**Middle runners start richest and fall furthest.** At the AP, r2/r3/r6/r7 sit at 8.00,
r4/r5 at 6.00, extremes at 4.00 — but every runner lands in the same 2.4–3.3 band once
displaced, regardless of starting rate.

## 5. What is still unmapped

- **Denominators coprime to 10.** All 152 positions have denominator dividing 10. By
  `TRANSIT_FRACTIONAL_v1` §2 the count grows with the denominator, so omitted positions
  should give *higher* rates — the minima above should survive finer sampling, but that is an
  expectation, not a check.
- **Two runners swept simultaneously** over full ranges. Single-move pair data exists
  (`RECOVERY_LAW_v2`) but not a 2-D sweep.
- **Excursions past a neighbour**, where the runner changes its order position.
- **Non-AP bases.** Every sweep here starts from the AP; the grid bases are unmapped.

## 6. Status

`[VERIFIED — exact]` §1's four mirror pairs; §2's eight rows; §3's floor; §4.
BSM with 0 cell anomalies at all 152 positions, method controlled against an independent
construction over 300 sets (`WN_bsm_transits_all_runners_2026_09_12` §1).

**n = 8 is not proved.**
