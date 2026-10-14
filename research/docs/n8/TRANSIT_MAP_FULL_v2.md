# Full transit map v2 — the one-time cost of deviation

2026-09-12. Supersedes `TRANSIT_MAP_FULL_v1.md`, whose §2 was wrong. n = 8, individual
isolation. Invariant: the event count, which the palindrome (`WN_count_parity` Step 2) makes
a count of **mirror pairs**.

## 0. What v1 got wrong

v1 §2 reported that displacing more runners compounds the cost — floor falling
`32 → 18 → 14 → 12` — and on that basis "corrected" `VACANCY_FRAME_v1` §3's saturation claim.

**That was an artefact of the experimental design.** v1's base was the reference scaled by
8, `B = (0,8,…,56)`, chosen so runners had integer room to move. At `δ = 0` that set has
`gcd = 8` and *is* the AP, so its counts are 8× the AP's. The moment any runner moves off its
grid point the gcd drops to 1 and the counts are raw. The apparent collapse was the gcd
changing, not deviation compounding. Cross-`δ` totals in v1 §1–§2 are not comparable and the
"correction" to `VACANCY_FRAME_v1` is withdrawn — that note's saturation claim was right.

## 1. Clean design

Work inside a grid `{0, …, M−1}` with the reference `{0,…,7}` and move runners to **other
grid points**. The gcd stays 1 throughout, so counts are comparable across the whole family.

Reference counts `[4, 8, 8, 6, 6, 8, 8, 4]`, total 52. Extremes at `φ(8) = 4` — two mirror
pairs each.

## 2. The cost is paid once  `[VERIFIED — exhaustive]`

| grid | `k` moved | 0 | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|---|---|
| `M = 13` | configs | 1 | 41 | 321 | 881 | 1,231 | 1,287 |
| | **floor** | 4 | **2** | 2 | 2 | 2 | 2 |
| | mean worst runner | 4.00 | 4.68 | 4.74 | 4.78 | 4.76 | 4.74 |
| `M = 16` | configs | 1 | 65 | 849 | 3,985 | 8,883 | 12,019 |
| | **floor** | 4 | **2** | 2 | 2 | 2 | 2 |
| | mean worst runner | 4.00 | 4.71 | 5.00 | 5.24 | 5.35 | 5.34 |

> **The first move costs one mirror pair, from two to one. No further move costs anything.**

And the population moves the *other* way: the mean worst runner rises monotonically,
`4.00 → 5.35` at `M = 16`. More deviation makes the typical arrangement easier while the
floor stays put.

## 3. Which pairs reach the floor

Grid `{0..12}`, both named runners free to move anywhere. Entry = floor of the worst runner.

|  | r2 | r3 | r4 | r5 | r6 | r7 | r8 |
|---|---|---|---|---|---|---|---|
| **r1** | 2 | 2 | 2 | 2 | 2 | 2 | 2 |
| **r2** | | 2 | 2 | 2 | 2 | 2 | 2 |
| **r3** | | | 2 | 2 | 2 | 2 | 2 |
| **r4** | | | | 2 | **4** | 2 | 2 |
| **r5** | | | | | **4** | 2 | 2 |
| **r6** | | | | | | 2 | 2 |
| **r7** | | | | | | | 2 |

26 of 28 pairs reach 2. The two exceptions are `(r4, r6)` and `(r5, r6)`, which cannot get
below 4 — the only structural obstruction visible at pair level, and it is unexplained.

## 4. The mechanism

Putting §2 and §3 together, in the owner's terms:

1. **At the reference** every runner has two mirror pairs (`φ(8) = 4` events).
2. **Any deviation** — one runner to one other grid point — costs some runner one of its two
   pairs. Floor 4 → 2.
3. **That is the entire cost.** Two, three, four, five simultaneous displacements do not
   reach below one pair, at either grid size, over 12,019 configurations.
4. **Further deviation is net positive**: mean worst runner climbs `4.00 → 5.35`.

So deviation from the reference does not erode isolation progressively. It levies a single
bounded toll — one mirror pair — and then stops taking. That is why moving away from the AP
cannot drive a runner to zero: the mechanism that would have to do it is not cumulative.


## 4a. Counterexample search (carried forward from v1 §4, extended)

A counterexample to LRC(8) is a configuration whose worst runner has event count **0** —
the objective directly, not a proxy.

| method | population | floor |
|---|---|---|
| exhaustive `[1..22]`, primitive | 319,605 | 2 |
| near-AP adversaries | 48,745 | 2 |
| hill-climb on the count | — | 2 |
| annealing, 90 restarts | — | 2 (43 of 90) |
| **annealing, 300 restarts, unrestricted speeds** | — | **2 (95 of 300)** |

The 300-restart run: local-optimum distribution
`{2: 95, 4: 81, 6: 36, 8: 19, 10: 13, 12: 14, 14: 12, 16: 7}`, minimiser
`(2,3,7,9,12,13,14,17)` with counts `[12,10,8,2,8,14,8,8]`. Nothing below 2 in any
population. By `WN_count_parity`, 1 is unreachable, so 2 and 1 are the same floor and the
only live question is 0.

**What a search can and cannot do.** No search establishes a floor. Two search-design
failures in this same session produced false floors that looked solid from several angles:
the `mmin` ceiling of 29 was an artefact of the search box and broke to 44 when widened
(`CONJECTURE_M_REFUTED_v1` §3), and §0 above is a third. Context: n = 8 is proved in the
literature (Rosenfeld 2025, his `k = 7`), so a counterexample would refute a published
result — these searches locate extremal structure and validate machinery, they are not a
live hunt.

## 5. What this does not establish

The floor of 2 is not proved, here or anywhere in this project. §2 is exhaustive over the
stated grids and `k ≤ 5`; it does not cover `M > 16`, `k ≥ 6`, or speeds outside a grid of
that size. Step 4 of §4 is a statement about means over these populations, not a bound.

`(r4,r6)` and `(r5,r6)` flooring at 4 is unexplained and may be an artefact of `M = 13`.

n = 8 is **not proved**. Nothing here bears on the published proof (Rosenfeld 2025).

## 6. Status

`[VERIFIED — exhaustive]` §2's two grids; §3's pair matrix.
`[VERIFIED — searched]` §4a's five populations; the floor of 2 is not proved by any of them.
`[PROVED]` the parity law making the count a count of mirror pairs.
`[RETRACTED]` `TRANSIT_MAP_FULL_v1` §2 and its correction of `VACANCY_FRAME_v1` §3;
`VACANCY_FRAME_v1` §3 stands.
