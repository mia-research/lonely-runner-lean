# The pinned set — where a counterexample would have to live, and what is there

2026-09-12. Follows `RECOVERY_LAW_v2.md` §3, which found that ~3.7% of arrangements keep a
runner at one mirror pair no matter how the rest of the field moves, and that this fraction
plateaus rather than decaying. This note opens that set.

## 1. The pinned set is tiny and structured  `[VERIFIED — exhaustive]`

Victim = the runner at speed 8 in `V = (0,1,2,3,4,5,6,8)`. Over all 28,814 arrangements in
which the other seven runners move anywhere in `{0..13}`, the arrangements holding the victim
at one mirror pair number **64**, and they carry only **three** distinct difference-sets:

| victim's difference set | count | as a subset of `{1..8}` |
|---|---|---|
| `(1,2,3,4,5,7,8)` | 32 | `{1..8}` less **6** |
| `(2,3,4,5,6,7,8)` | 16 | `{1..8}` less **1** |
| `(1,3,4,5,6,7,8)` | 16 | `{1..8}` less **2** |

Max difference is exactly 8 in all 64. So *pinned* means the victim sees a **near-complete
consecutive run** — the hard region is dense configurations, not spread ones. Of the eight
ways to delete one element from `{1..8}`, only these three pin; deleting 3, 4, 5, 7 or 8 does
not.

`V = {0,1,2,3,4,5,7,8}` is the realisation of the first row, and it is the same set the
independent minimum-total search reached (`TRANSIT_MAP_FULL_v2` §3 / the `[0..20]` exhaustive
run). Two unrelated objectives land on it.

## 2. Exhaustive search of the dense region  `[VERIFIED — exhaustive]`

Since the pinned structure is "small span", search **all** 7-element difference sets in a
box — every 8-set with span `≤ N`, seen from one runner. `D` is realised by `V = {0} ∪ D`.

| `N` | primitive sets | min count | minimisers |
|---|---|---|---|
| 8 | 8 | 2 | the three above |
| 12 | 792 | 2 | + `(1,3,4,5,7,8,12)` |
| 16 | 11,440 | 2 | + `(1,2,3,4,5,7,16)` |
| 18 | 31,824 | 2 | same |
| 20 | 77,400 | 2 | `(1,2,3,4,5,7,8)`, `(1,2,3,4,5,7,16)`, `(1,3,4,5,6,7,8)`, `(1,3,4,5,6,7,16)` |
| 22 | 170,213 | 2 | same four |

**Minimum count is 2 at every box, never 0 and never 1.** `(1,2,3,4,5,7,8)` is minimal at
every `N` — enlarging the box never gives the adversary anything. The new minimisers that
appear are `8 → 16` substitutions, i.e. the same residue mod 8.

This is a stronger search than the annealed ones in `TRANSIT_MAP_FULL_v2` §4a: it is
exhaustive over the entire difference-set space of the region the pinned set identifies,
rather than sampled.

## 3. The sandwich

- **Dense region** (span `≤ 22`): exhaustive, 170,213 sets, floor 2.
- **Spread region**: counts grow with the speeds — `WN_floor_search` found the random
  `[1..500]` minimum to be 36, and the `Conjecture M` counterexample at speeds `~2×10⁵` has
  130,740 events with measure `0.1335 ≈ (3/4)⁷` (`MMIN_RETRACTION_v1` §1).

The difficulty is concentrated in a narrow band of small-span configurations, and that band
has now been enumerated exhaustively to span 22 with no count below 2.

## 4. What is still open

The two regions are not joined by an argument. "Counts grow with the speeds" is measured, not
bounded below — `WN_resolution_law` §3's bound `|G(e)| ≥ (3/4)|G_F| − N_F/(2e)` is proved but
fires on only 0.38% of instances with its proved constant. So there is no theorem saying
span `> 22` implies count `> 2`, and the exhaustive floor covers only span `≤ 22`.

A counterexample would need span above 22 while behaving like the dense minimisers. Nothing
found so far does both.

## 5. Status

`[VERIFIED — exhaustive]` §1's 28,814 arrangements; §2's six boxes, to 170,213 primitive sets
at `N = 22`.
`[PROVED]` the parity law making the count a count of mirror pairs (`WN_count_parity` Step 2),
which excludes count 1 — so the floor of 2 and a floor of 1 are the same statement.
`[NOT PROVED]` that the count is never 0, at any span. That is LRC(8).

n = 8 is **not proved**. Nothing here bears on the published proof (Rosenfeld 2025).
