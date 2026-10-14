# Recovery law v2 — quadruplets, quintuplets, and the full recovery curve

2026-09-12. Extends `RECOVERY_LAW_v1.md` with `k = 4, 5` tuple floors and the victim curve
carried to all seven other runners. n = 8, individual isolation. Invariant: event count =
mirror pairs (`WN_count_parity` Step 2).

## 1. Tuple floors — flat at every size

Reference `{0,…,7}`. For each `k`-tuple of runners, all of them free to move to any other
grid point; entry is the floor of the worst runner over all such moves.

| grid | `k` | tuples | floor distribution | any above 2 |
|---|---|---|---|---|
| `{0..12}` | 3 | 56 | `{2: 56}` | none |
| `{0..12}` | 4 | 70 | `{2: 70}` | none |
| `{0..12}` | 5 | 56 | `{2: 56}` | none |
| `{0..14}` | 3 | 56 | `{2: 56}` | none |
| `{0..14}` | 4 | 70 | `{2: 70}` | none |
| `{0..14}` | 5 | 56 | `{2: 56}` | none |

**Every tuple at every size reaches exactly 2, and none goes below.** The floor is completely
insensitive to how many runners move and to the grid size. Together with
`TRANSIT_MAP_FULL_v2` §2 (`k ≤ 5`, floors `4,2,2,2,2,2`), the picture is: one move sets the
floor, and nothing after that moves it in either direction.

## 2. The full recovery curve

Victim = the runner at speed 8 in `V = (0,1,2,3,4,5,6,8)`, down to one mirror pair after a
single move. Other runners move to other grid points; the victim never moves. Grid
`{0..13}`, exhaustive at every level — 28,814 configurations in total.

| others moved | configs | min | mean | max | stuck at 2 | at or above reference (4) |
|---|---|---|---|---|---|---|
| 0 | 1 | 2 | 2.00 | 2 | 100.0% | 0.0% |
| 1 | 49 | 2 | 4.16 | 8 | 30.6% | 69.4% |
| 2 | 588 | 2 | 5.15 | 10 | 15.1% | 84.9% |
| 3 | 2,940 | 2 | 5.67 | 10 | 9.4% | 90.6% |
| 4 | 7,350 | 2 | 5.98 | 10 | 6.7% | 93.3% |
| 5 | 9,702 | 2 | 6.17 | 10 | 5.2% | 94.8% |
| 6 | 6,468 | 2 | 6.31 | 10 | 4.3% | 95.7% |
| 7 | 1,716 | 2 | 6.41 | 10 | **3.7%** | **96.3%** |

The victim's mean rises 2.00 → 6.41 and its maximum reaches 10 — five mirror pairs, well
above the reference's two. By the time all seven others have moved, 96.3% of arrangements
have the victim at or above its original reference value.

## 3. The stuck set plateaus — it does not vanish

The important qualification, and it is visible only with the full curve:

    stuck at 2:   100%  30.6%  15.1%   9.4%   6.7%   5.2%   4.3%   3.7%
    decay ratio:        0.31   0.49   0.62   0.71   0.78   0.83   0.86

The ratios rise steadily toward 1. The stuck fraction is **levelling off near 3.7%, not
decaying to zero**, and the `min` column is 2 at every single level. There is always a set
of arrangements that keeps the victim pinned at one mirror pair, and adding more movement
does not exhaust it.

This bounds what the recovery law can be asked to do. It is a statement about the typical
arrangement, and the typical arrangement is not where a counterexample would live.

## 4. The mechanism, and its limit

1. **Reference**: every runner holds two mirror pairs.
2. **First deviation**: some runner drops to one. Floor 4 → 2.
3. **No further toll**: no `k` up to 5, on two grids, and no tuple of any size, reaches below
   one pair.
4. **Repayment**: further deviation returns the pair to the runner that lost it — 69.4% after
   one move, 96.3% after seven — and often overshoots the reference.
5. **But the pinned set persists**: ~3.7% of arrangements hold the victim at one pair no
   matter how much the rest of the field moves, and that fraction is flattening rather than
   shrinking away.

Steps 1–4 explain why the floor is hard to breach. Step 5 is why they do not show it cannot
be: everything that would have to go wrong for a counterexample lives inside the pinned set,
which no amount of additional movement empties.

## 5. Status

`[VERIFIED — exhaustive]` §1's six rows; §2's eight rows, 28,814 configurations, grid
`{0..13}`.
`[PROVED]` the parity law making the count a count of mirror pairs.
`[NOT PROVED]` the floor of 2, at any `k` or grid size. §2 and §3 are proportions over
stated populations, not bounds.

n = 8 is **not proved**. Nothing here bears on the published proof (Rosenfeld 2025).
