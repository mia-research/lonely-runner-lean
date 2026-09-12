# Summary — AP/grid and variances from them

2026-09-12. n = 8, individual isolation. Factual consolidation of the mapping series. No
conclusion is drawn; items are listed with their evidential status.

Writing this surfaced one untested question (§2), which was tested before the summary was
finished; that section is new here and appears nowhere else.

---

## 1. The reference

**Definition.** A *grid* is a set of 8 speeds whose reduced residues form a complete system
mod 8. The AP `(1,…,8)` is the case with all deviations zero. In coordinates
`u_i = π(i) + 8 q_i`, `π` is forced to be a complete residue system and the **shape is
entirely `q`**.

**`[PROVED]`** A grid is globally isolated at exactly `φ(8) = 4` instants `t = p/(8g)`,
`p` odd.

**`[PROVED]`** Those four instants lie in **every** runner's individual good set
simultaneously — the **spine**. A runner holds all four or none, because `8 | dp ⟺ 8 | d`
for odd `p`.

**`[PROVED]`** The eighth-lattice is strictly nested: `t = k/8` needs `dk ≢ 0 mod 8`, so
`k = 4` (all `d` odd) ⟹ `k = 2,6` (no `d ≡ 0 mod 4`) ⟹ `k` odd (no `d ≡ 0 mod 8`). The spine
is the weakest requirement, hence the last to go; a runner losing it holds no eighth-lattice
point at all.

## 2. The measure is a popcorn function  `[VERIFIED — new]`

Count-per-cycle is undefined at irrational speeds. The quantity defined everywhere is the
**measure** (density) of each runner's good set. Varying r1 continuously from the AP:

| `r1` | 0.999 | 1 | 1.001 | 1.01 | 1.05 | 1.1 |
|---|---|---|---|---|---|---|
| `\|G_{r1}\|` | 0.13021 | **0** | 0.13021 | 0.13019 | 0.13012 | 0.12795 |

The measure **jumps at every commensurate point**, in both directions:

| `x` | 1 | 4/3 | 3/2 | 9/5 | 13/10 | 5/4 | 7/4 |
|---|---|---|---|---|---|---|---|
| at `x` | **0** | 0.1129 | 0.1136 | 0.1293 | 0.1326 | 0.1333 | 0.1420 |
| either side | 0.1302 | 0.1302 | 0.1302 | 0.1302 | 0.1302 | 0.1302 | 0.1302 |

Between rationals it is flat to five figures (sweep 1.300→1.310: 0.130192–0.130219). So the
measure is generic almost everywhere with a discontinuity at each rational, the jump shrinking
with the denominator.

> **The AP is the extreme of this structure: the deepest downward jump, to zero.**
> Leaving it is not a slide but a jump — at `r1 = 1.001` the measure is already generic.

The generic value is **0.1302**, not `(3/4)⁷ = 0.13348`; the seven differences of eight speeds
are not fully independent.

## 3. Counts at a grid

**`[VERIFIED — exhaustive, 6,305 grid shapes]`** `base min = 4 + (fewest extras)`, without
exception. Every grid gives every runner the spine; shapes differ only in **reserve**.

Base-min distribution over `q ∈ {0,1,2}⁸`:
`{4: 311, 6: 1441, 8: 2467, 10: 1441, 12: 532, 14: 96, 16: 15, 18: 2}` — never below 4, which
§1 forces. With `q ∈ {0,…,3}` the distribution extends to 20 and still never falls below 4:
wider deviations make grids safer.

Reserve profiles: tight AP `0,4,4,2,2,4,4,0`; alternating `8,12,8,2,2,8,12,8`; two clusters
`6,14,12,8,8,12,14,6`; wide linear `10,14,10,14,12,10,18,10`. **The tight AP is the unique
worst grid because its two end runners have zero reserve.**

## 4. Leaving the reference

**What a move does `[VERIFIED]`.** It removes the spine from exactly the runners it puts into
residue collision — all four instants at once. Of 3,657 runners that kept the spine across a
move, reserve went up 30.4%, unchanged 40.8%, down 28.8%, mean 5.84 → 5.87. **The reserve is
conserved on average; only the spine transfers.**

**Exactly one collision is dangerous `[VERIFIED — exhaustive [0..16]]`.**

| shares residue with | instances | min count |
|---|---|---|
| 0 others | 100,380 | 4 |
| 1 other | 88,032 | **2** |
| 2 others | 5,988 | 4 |

**Where a crashed runner lands `[VERIFIED]`.** Of 5,136 floor-of-2 runners in `[0..22]`, tower
levels `{1: 1474, 2: 2056, 3: 1404, 4: 202}`, and **zero at level 0** — forced by §1, against
49% of the general population.

**Direction `[VERIFIED — all 8 runners]`.** Moving a runner toward the centre of the pack costs
more than moving it the same distance away. No exceptions.

**Permutation `[VERIFIED]`.** Holding the deviation multiset fixed and varying only which
residue each attaches to swings the floor up to **4×** (one multiset: 4 to 16 across 560
assignments). The worst assignment reaches the forced floor of 4 in 13 of 14 multisets.

## 5. Both flanks are safe

**Near-collision `[VERIFIED]`.** As two runners approach, the count grows like `1/ε` (300 at
`ε = 1/100`) and the rate converges to 3. A near-collision **enlarges** the reduced
configuration.

**High grid distance `[PROVED, slot-counting]`.** With `m` residue classes a box `[0..N]`
offers about `m(N/8+1)` slots, so small `m` forces large `N`. High `k` requires spread; `k=6`
examples give min counts 12, 19, 28, 56.

**Danger band `[VERIFIED — exhaustive [0..20]]`.** Floor by grid distance:
`k=0 → 4` (forced), `k=1..4 → 2`, `k=5 → 4`.

## 6. Floors observed

| population | floor |
|---|---|
| difference sets to span 38 (12,569,075) | 2 |
| AP displacement, `k` runners, exhaustive over half-integers | 2 |
| all grid shapes, one move | 2 (near-tight) / 4 (spread, span-stable to 150) |
| non-grid bases, one move | 2 |
| all transits, all runners, both directions | 2 |

Count 1 is impossible when any constraint is even (parity law), so 2 and 1 are the same floor.
**Nothing in the series reached 0.**

## 7. Claims killed by their own follow-up tests

- `mmin` as a difficulty measure, and Conjecture M's bound of 29 — search-box artefact.
- "The AP minimises the total event count" — read off a one-runner slice.
- "Displacement cost compounds" — gcd artefact of a scaled base.
- "Low counts occur only at small span" — `(1,4,5,6,7,11,32)`.
- "The adversary chooses halves" — true in one setting, reversed in another; the operative
  property is the size of the **reduced** configuration.
- "Crashed runners land on sixteenths" — generalised from one example; the mode is 32nds.
- "The worst permutation reconstitutes an AP" — 4 of 14 multisets, one multiset's accident.
- "Worst assignments carry a long run" — 9 of 14, not a characterisation.
- "Grid distance predicts what a move does" — flat: `Δk = −1,0,+1` all ~30/40/30.

## 8. Untested

- Path-dependence of individual **window trajectories** — §2 measures the density along a
  path, not which windows slide, split or merge.
- `q` entries beyond 3.
- Simultaneous two-runner continuous sweeps.
- Whether the generic measure 0.1302 has a closed form.
- Whether the jump size at `p/q` is a function of `q`.

## 9. Status

`[PROVED]` §1 throughout; the slot-counting argument in §5.
`[VERIFIED — exhaustive]` §3's identity and distributions; §4's collision table; §5's danger
band; §6's floors over the stated ranges.
`[VERIFIED — new, this note]` §2.
`[KILLED]` §7's nine claims.

**n = 8 is not proved.** Nothing here bounds any count below.
