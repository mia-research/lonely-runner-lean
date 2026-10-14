# Turns per lap on `d_min = 1` grids — by speed, not by index

2026-09-13. n = 8, individual isolation, threshold 1/8. Answers the open item in
`PER_LAP_CORRECTION_v1` §5: whether the AP's turns-per-lap profile
`8, 4, 8/3, 2, 8/5, 4/3, 8/7, 1` — which is `8/i` by index — holds for every grid whose runners
keep `d_min = 1`.

---

## 1. Result  `[VERIFIED — 97 grids]`

Population: every grid of the form `u_i = i + 8·q_i` with `q` non-decreasing and every block of
equal `q` at least 2 long, so that each runner has a speed-neighbour at distance 1. Block gaps
1, 2 and 3. 97 such grids.

| claim | rate |
|---|---|
| coverage `= 1/8` | **97 of 97** |
| every runner's tally `= 1` at coverage | **97 of 97** |
| turns per lap `= 8 / v_i` (**speed**) | **97 of 97** |
| turns per lap `= 8 / i` (**index**) | **1 of 97** |

The single index match is the AP itself, where speed and index coincide.

`(1,2,11,12,21,22,31,32)` gives `8, 4, 8/11, 2/3, 8/21, 4/11, 8/31, 1/4` — which is
`8/1, 8/2, 8/11, 8/12, 8/21, 8/22, 8/31, 8/32`, exactly `8/v_i`.

## 2. And it is not really a law about laps

Once the first two rows hold, the third is arithmetic:

    turns per lap = tally / (v_i · coverage) = 1 / (v_i · 1/8) = 8 / v_i

So the substantive content is the **first two rows**, not the third:

> **On a grid with `d_min = 1` throughout, coverage is `1/8` and every runner is lonely exactly
> once by then.**

That is the claim worth holding. `8/v_i` follows from it and carries nothing extra.

## 3. What this retires

`PER_LAP_CORRECTION_v1` §4 noted the AP profile "is `8/i` by index" and asked whether it
generalised. It does not, and the observation was an artefact: in the AP the runner's speed *is*
its index, so `8/v` and `8/i` are the same numbers and nothing distinguishes them. Every other
grid separates them, and it is speed that governs.

This is the second time in this line of work that a pattern read off the AP turned out to be the
AP's coincidence rather than a structure — the first being the `d_min` / residue conflation in
`PREDICTION_SPREAD_GRID_v1` §4. The AP identifies speed with index, `d_min` with residue-distance,
and grand return with one lap of the slowest. Anything read from it alone risks being one of
those identifications rather than a law.

## 4. Status and scope

`[VERIFIED — 97 of 97]` §1's four rows.
`[PROVED — arithmetic]` §2's derivation of `8/v_i` from the first two rows.
`[REFUTED]` the `8/i`-by-index reading.

**Scope.** Grids of the block form `u_i = i + 8 q_i`, block gaps ≤ 3, all blocks ≥ 2 long. Grids
with `d_min = 1` that are not of this form are untested, as are grids where some runner has
`d_min > 1` — `(1,…,7,160)` is one of those and does **not** satisfy `8/v_i` (its r8 gives 1,
against `8/160 = 1/20`).

**n = 8 is not proved here, and is not the target here.**
