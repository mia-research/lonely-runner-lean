# The recovery law — a lost mirror pair is repaid by further deviation

2026-09-12. n = 8, individual isolation. Extends `TRANSIT_MAP_FULL_v2.md` §2 with the
per-runner question that the floor statistic hides. Invariant: event count = mirror pairs
(`WN_count_parity` Step 2).

## 1. The question

`TRANSIT_MAP_FULL_v2` §2 established that the first deviation drops the floor from 4 to 2
and no further deviation lowers it. That is a statement about the *minimum over all
arrangements*. It does not say what happens to the **particular runner** that lost a pair
when other runners subsequently move.

Owner's prediction: *"while one move takes away an isolation, movement of the others will
start to give it back."*

## 2. Test

Reference `{0,…,7}`, counts `[4,8,8,6,6,8,8,4]`. One move gives

    V = (0,1,2,3,4,5,6,8)   counts [6,6,8,8,6,8,8,2]

The runner at speed 8 is down to a single mirror pair. Now move **other** runners — never
the victim — to other grid points, and track the victim's own count. Grid `{0..13}`,
exhaustive:

| others moved | configs | victim min | victim mean | victim max | stuck at 2 |
|---|---|---|---|---|---|
| 0 | 1 | 2 | 2.00 | 2 | 100.0% |
| 1 | 42 | 2 | 4.52 | 8 | **19.0%** |
| 2 | 315 | 2 | 5.87 | 10 | **6.3%** |
| 3 | 700 | 2 | 6.46 | 10 | **3.1%** |
| 4 | 525 | 2 | 6.68 | 10 | **2.1%** |

> **The prediction holds.** A single further move restores the victim above one pair in 81%
> of arrangements; by four moves, 97.9%. The victim's mean climbs 2.00 → 6.68 and its
> maximum reaches 10 — five mirror pairs, more than the reference's two.

The minimum stays at 2 throughout: an adversarial arrangement keeping the victim pinned
always exists. But it is a shrinking fraction — `100% → 19.0% → 6.3% → 3.1% → 2.1%`.

## 3. Triplets

All 56 triplets of runners, each free to move anywhere in `{0..12}`, floor of the worst
runner:

    floor distribution over the 56 triplets: {2: 56}

Every triplet reaches 2, none goes below. This also resolves `TRANSIT_MAP_FULL_v2` §3's
loose end: the pairs `(r4,r6)` and `(r5,r6)` floored at 4, which looked like a structural
obstruction. At triplet level no such exception survives, so it was an artefact of the pair
restriction, not structure.

## 4. The mechanism, complete

1. **Reference**: every runner holds two mirror pairs (`φ(8) = 4` events).
2. **First deviation**: some runner drops to one pair. Floor 4 → 2.
3. **The toll is not repeated**: no number of simultaneous displacements reaches below one
   pair (`TRANSIT_MAP_FULL_v2` §2, exhaustive to `k = 5` on two grids; §3 here, all 56
   triplets).
4. **The toll is repaid**: further deviation actively returns the pair to the runner that
   lost it — 81% after one move, 97.9% after four — and can raise it well above the
   reference value.

So deviation from the reference is not a drain. It takes one pair once, and continued
deviation hands it back. The configurations that keep a runner at one pair are a shrinking
minority that requires the rest of the field to stay arranged just so.

## 5. What this does not establish

The floor of 2 is not proved. Every row above is exhaustive over a stated grid and a stated
number of movers; none bounds anything outside that. Step 4 is a statement about
proportions over these populations, not a theorem — "97.9% recover" is compatible with a
counterexample living in the remaining 2.1%, and the minimum column shows that the stuck
set is never empty at any `k` tested.

The recovery law explains *why* the floor is hard to breach. It does not show it cannot be.

n = 8 is **not proved**. Nothing here bears on the published proof (Rosenfeld 2025).

## 6. Status

`[VERIFIED — exhaustive]` §2's five rows, grid `{0..13}`; §3's 56 triplets, grid `{0..12}`.
`[PROVED]` the parity law making the count a count of mirror pairs.
`[RESOLVED]` `TRANSIT_MAP_FULL_v2` §3's unexplained pair exceptions — artefact of the pair
restriction.
