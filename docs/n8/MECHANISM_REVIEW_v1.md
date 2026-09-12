# Review — the mechanisms the mapping revealed, and the claims it killed

2026-09-12. n = 8, individual isolation. Consolidates the mapping series and reports the
remaining tests from `RED_TEAM_PERMUTATION_v1` §5.

## 1. Claims killed

**"The worst permutation reconstitutes an AP."** False. Enumerating every assignment of 14
deviation multisets: only **4 of 14** have an AP anywhere among their worst assignments, and
where one exists it is 1 of 4, 1 of 9, 1 of 14, 1 of 16 equally-worst assignments. It was one
multiset's accident, stated from a single instance.

**"The worst assignments carry a long consecutive run."** The replacement candidate, also
weak: longest run in the worst ≥ longest run in the best in only **9 of 14**, means 5.43
against 4.64. Not a characterisation.

No structural description of *which* assignment is worst survives. What does survive is
quantitative: **the worst assignment reaches count 4 — the forced grid floor — in 13 of 14
multisets**, while best counts scatter from 8 to 18. Permutation freedom is almost always
enough to drive a grid to its floor; the deviations do not protect it.

**"Grid distance predicts what a move does."** False, and it was a standing candidate
mechanism. Over 3,000 random single moves:

| `Δk` | n | count down | same | up |
|---|---|---|---|---|
| −1 | 416 | 29.6% | 40.1% | 30.3% |
| 0 | 853 | 30.4% | 43.7% | 25.9% |
| +1 | 397 | 29.5% | 38.3% | 32.2% |

Indistinguishable. `k` classifies configurations but does not predict transitions.

## 2. The mechanism, as it now stands

**(M1) The spine.** `[PROVED]` At any grid the `φ(8) = 4` instants `t = p/(8g)`, `p` odd, lie
in every runner's good set at once. A runner holds all four or none, since `8 | dp ⟺ 8 | d`.
The eighth-lattice above it is strictly nested — half ⟹ quarters ⟹ odd-eighths — so the spine
is the *weakest* requirement and the last thing to go.

**(M2) Reserve accounting.** `[VERIFIED — 6,305 grid shapes, exact]`
`base min = 4 + (fewest extras)`, without exception. Shapes differ only in reserve.

**(M3) A move takes the spine, not the reserve.** `[VERIFIED]` A move removes the spine from
exactly the runners it puts into residue collision. For 3,657 runners that kept the spine
across a move, the reserve went up 30.4%, unchanged 40.8%, down 28.8% — mean 5.84 → 5.87.
**The reserve is conserved on average; only the spine is transferred.**

**(M4) Exactly one collision is dangerous.** `[VERIFIED — exhaustive, [0..16]]`

| runner shares its residue with | instances | min count |
|---|---|---|
| 0 others | 100,380 | **4** |
| 1 other | 88,032 | **2** |
| 2 others | 5,988 | **4** |

Zero collisions: the spine protects. Two collisions: fewer distinct residues means higher `k`,
which forces spread (`AWAY_FROM_GRID_v1` §2), which forces safety. **Only the single collision
sits in the gap between the two protections.**

**(M5) Both flanks are safe.** `[VERIFIED]` Near-collision explodes the reduced configuration
— count grows like `1/ε`, reaching 300 at `ε = 1/100`, rate converging to 3. High grid
distance requires large spread by a slot-counting argument. The danger band is `k = 1..4` with
a small reduced configuration.

**(M6) A crashed runner lands on a finer 2-power lattice.** `[VERIFIED]` Of 5,136 floor-of-2
runners in `[0..22]`, tower levels `{1: 1474, 2: 2056, 3: 1404, 4: 202}` — and **zero at level
0**, which is forced by (M1), against 49% of the general population. Reserve is largely those
finer lattices.

## 3. The picture

A configuration reaches the floor only in a narrow window, bracketed on four sides:

    too few collisions   -> the spine holds it at >= 4        (M1, M4)
    too many collisions  -> spread forces safety              (M4, M5)
    too commensurate     -> no room to place 8 speeds         (M5)
    too incommensurate   -> the reduced set explodes          (M5)

and within that window, whether a given runner falls depends on its reserve (M2), which a move
does not touch (M3).

## 4. Extra range does not change it

`q` entries drawn from `0..3` rather than `0..2` shift the base-min distribution upward (out
to 20) without adding anything below 4:

    q in 0..2:  {4:227, 6:971, 8:1520, 10:899, 12:315, 14:57, 16:11}
    q in 0..3:  {4:64, 6:360, 8:901, 10:1086, 12:872, 14:488, 16:184, 18:36, 20:9}

Wider deviations make grids safer, never more dangerous.

## 5. What none of this does

No result here bounds the count below. The mechanism explains why 2 is hard to reach and
where it lives; it does not show 2 cannot become 0. Every floor in the series is a
verification over a stated range.

Three claims in this series were killed by their own follow-up tests (§1), and three more were
retracted earlier on the same grounds — a bound read off a region the search could not reach.
The surviving statements are the ones that were tested against populations rather than
examples.

## 6. Status

`[PROVED]` M1, and the slot-counting half of M5.
`[VERIFIED — exhaustive]` M2 (6,305 shapes); M4 (`[0..16]`).
`[VERIFIED — sampled]` M3, M6, §1's `Δk` table, §4.
`[KILLED]` the AP claim, the run claim, the `Δk` predictor.

**n = 8 is not proved.**
