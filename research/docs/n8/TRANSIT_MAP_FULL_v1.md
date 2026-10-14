# Full transit map — single runners, pairs, and the counterexample search

2026-09-12. n = 8, individual isolation. Invariant throughout is the **event count**
(components of `G_D`), which the palindrome makes a count of mirror pairs.

Base for the transits: `B = (0, 8, 16, 24, 32, 40, 48, 56)` — the reference scaled by 8, so
each runner has integer positions across its gap. `B` reduces to the AP.

## 1. Single-runner transits — the law

Slide runner `j` by `δ` from its grid point. The moved runner's own count, grouped by
`gcd(|δ|, 8)`:

| `gcd(δ,8)` | 1 | 2 | 4 | 8 |
|---|---|---|---|---|
| samples | 60 | 30 | 15 | 1 |
| min | 19 | 18 | **36** | — |
| max | 31 | 30 | **44** | — |
| mean | 25.10 | 24.53 | **36.53** | — |

`δ ≡ 4 (mod 8)` gives **exactly 36** in 14 of the 15 cases. On the reference (`δ = 0`) the
counts are `[32,64,64,48,48,64,64,32]` = 8× the unscaled AP's `[4,8,8,6,6,8,8,4]`.

> **Two safe harbours per period.** `δ = 0` is the 8-grid; `δ = 4` is the 4-sublattice.
> Between them the count dips to 18–31 and recovers. A runner crossing from one grid point
> to the next passes through a bounded dip and arrives at the half-grid point, where it
> recovers sharply.

This is the mechanism behind "there is a low point but it can't escape before getting
better", stated in the invariant rather than observed.

Parity behaves as `WN_count_parity` Step 2 requires: `δ` odd makes every difference odd, so
the count is odd (21, 19, 27, 25, …); `δ` even gives an even count.

## 2. Pair transits — the cost compounds

Moving a second runner **does** lower the floor. Over the same base:

| displaced runners | configs | worst-runner floor |
|---|---|---|
| 0 (reference) | 1 | 32 |
| 1 | 3,773 | 18 |
| 2 | 3,509 | 14 |
| 3 | 3,218 | 12 |
| 4 | 2,944 | 12 |
| 5 | 2,587 | 12 |
| 6 | 2,256 | 12 |
| 7 | 1,951 | 10 |
| 8 | 1,711 | 12 |

It falls 32 → 18 → 14 → 12 and then flattens. **This corrects `VACANCY_FRAME_v1` §3**, which
reported the cost as saturating after the first vacancy. The two are measured in different
regimes — the vacancy table used small grids (`M ≤ 16`, speeds ≤ 15) where counts are small,
this table uses the ×8 base (speeds ≤ 63) where they are large — so they do not contradict,
but the saturation claim was stated more broadly than the evidence supported.

## 3. Minimum total, exhaustive

| box | sets | min total | minimisers |
|---|---|---|---|
| `[0..16]` | 24,300 | 44 | — |
| `[0..18]` | 75,528 | 44 | 36 sets |
| `[0..20]` | 203,280 | 44 | 44 sets |

Every minimiser has its worst runner at exactly 2 and is near-grid:
`(0,1,2,3,4,5,7,8)`, `(0,1,3,4,5,6,7,8)`, `(0,1,3,4,5,7,8,12)`, `(0,4,5,7,8,9,11,12)`,
`(1,2,3,4,5,6,8,9)`, `(1,2,4,5,6,7,8,9)`.

## 4. The counterexample search

A counterexample to LRC(8) is a configuration whose worst runner has event count **0**. That
is the objective directly — not a proxy. Results:

| method | population | floor |
|---|---|---|
| exhaustive `[1..22]`, primitive | 319,605 | 2 |
| near-AP adversaries | 48,745 | 2 |
| hill-climb on the count | — | 2 |
| simulated annealing, 90 restarts | — | **2** (43 of 90 restarts) |

Annealing's local-optimum distribution: `{2: 43, 4: 25, 6: 8, 8: 8, 10: 4, 12: 1}`.
Example minimiser `(1,3,5,8,10,11,12,13)`, counts `[10,10,2,6,8,10,12,8]`.

Nothing below 2 in any population. By `WN_count_parity`, 1 is unreachable, so 2 and 1 are
the same floor — the live question is only whether 0 is reachable.

**What this search can and cannot do.** It is on the right objective, and it converges to 2
from exhaustive enumeration, greedy descent and annealing independently. It cannot establish
a floor: no search can. Two search-design failures earlier in this same session went the
same way — the `mmin` ceiling of 29 was an artefact of the search box and broke to 44 when
widened (`CONJECTURE_M_REFUTED_v1` §3), and "the AP minimises the total" was read off a
one-runner transit that could not reach the true minimiser (`VACANCY_FRAME_v1` §4). Both
produced false floors.

Context: n = 8 is proved in the literature (Rosenfeld 2025, his `k = 7`). A counterexample
would refute a published result. These searches locate extremal structure and validate the
machinery; they are not a live hunt.

## 5. Status

`[VERIFIED — exhaustive]` §1's transit table; §3's three boxes.
`[VERIFIED — searched]` §2's displacement floors; §4's four populations.
`[PROVED]` the parity law underlying the invariant (`WN_count_parity` Step 2).
`[CORRECTED]` `VACANCY_FRAME_v1` §3's saturation claim — see §2.

n = 8 is **not proved** here; nothing in this note bears on the published proof.
