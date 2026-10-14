# How it works away from AP/grid — the near-collision limit and the grid-distance band

2026-09-12. n = 8, individual isolation. Two regimes not previously tested, both suggested by
the observation that a runner cannot be sped up far without running inline with the next.

## 1. Near-collision is safe, not dangerous  `[VERIFIED — exact]`

Base `(1, x, 3, 4, 5, 6, 7, 8)` with `x = 1 + ε`, so two runners approach each other:

| gap `ε` | 1 | 1/2 | 1/5 | 1/10 | 1/20 | 1/50 | 1/100 |
|---|---|---|---|---|---|---|---|
| cycle | 1 | 2 | 5 | 10 | 20 | 50 | 100 |
| largest reduced speed | 7 | 14 | 35 | 70 | 140 | 350 | 700 |
| **min count** | 4 | 6 | 16 | 30 | 60 | 150 | **300** |
| rate = count/cycle | 4.0 | 3.0 | 3.2 | **3.0** | **3.0** | **3.0** | **3.0** |

As the gap closes the count **grows without bound** and the rate converges to exactly **3**.

The reason is that a near-collision does not shrink the configuration, it **explodes** it: the
small gap becomes 1 in reduced terms and every other difference scales up by `1/ε`. The
near-twin then acts as a single extra constraint: over a cycle of length `~1/ε` the condition
`‖εt‖ ≥ 1/8` excludes about a quarter, so the rate is the six-constraint rate times `3/4`.

Same in the middle of the pack (`r5` approaching `r4`): counts 4, 8, 6, 12, 31, 53, 133, rate
settling near 2.65.

> **Running inline is safe.** The danger is not at near-collisions but at the **commensurate**
> points, and the counts blow up between them.

## 2. The grid-distance band  `[VERIFIED — exhaustive over [0..20]]`

`k = 8 − #distinct residues mod 8` after reduction; `k = 0` is a grid.

| `k` | 0 | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|---|
| configs | 1,944 | 35,316 | **96,930** | 60,960 | 8,024 | 106 |
| floor | 4 | **2** | **2** | **2** | **2** | 4 |

- `k = 0`: floor 4, and this is **forced** — a grid is globally isolated at `φ(8) = 4`
  instants, so every runner holds at least those (`SPINE_AND_RESERVE_v1` §1).
- `k = 1..4`: floor 2. This is the danger band.
- `k = 5`: back to 4, on only 106 configurations.

Beyond the box, high `k` is uniformly safe:

| configuration | `k` | spread | min count |
|---|---|---|---|
| `(0,1,8,9,16,17,24,25)` | 6 | 25 | 12 |
| `(0,1,16,17,32,33,48,49)` | 6 | 49 | 28 |
| `(0,8,16,24,32,40,48,49)` | 6 | 49 | 19 |
| `(1,64,72,…,112)` | 6 | 111 | **56** |

**Why high `k` cannot be dangerous.** With only `m` distinct residues mod 8, a box `[0..N]`
offers about `m·(N/8 + 1)` slots, so placing 8 distinct speeds needs `m·(N/8+1) ≥ 8`. Keeping
`m` small therefore forces `N` large. High grid distance **requires** large spread, large
spread means a large reduced configuration, and large reduced configurations have many events.

## 3. The danger zone is narrow on both sides

Putting §1, §2 and `SPINE_AND_RESERVE_v1` together, a configuration reaches the floor of 2
only when **all** of the following hold:

1. **Some residues collide** — `k ≥ 1`, or the spine keeps every runner at ≥ 4.
2. **Not too many collide** — `k ≤ 4`; beyond that the required spread makes it safe.
3. **The reduced configuration is small** — near-collisions and large denominators both
   enlarge it and raise counts.
4. **Some runner has little reserve** — the collision must strike a runner whose good set was
   mostly spine.

Each condition fails in a different direction, and they bracket the dangerous region from
opposite sides: too few collisions and the spine saves you, too many and the spread saves
you; too commensurate and you have no room, too incommensurate and the count explodes.

## 4. What this does not settle

Nothing here bounds the floor below. It maps where the floor of 2 lives and shows the
surrounding regions are safe; it does not show 2 cannot become 0 inside the band. The four
conditions are descriptive, verified over the stated ranges, and are not a proof.

## 5. Status

`[VERIFIED — exact]` §1's two approach sequences.
`[VERIFIED — exhaustive]` §2's `[0..20]` table, 203,280 primitive configurations.
`[VERIFIED — exact]` §2's high-`k` examples.
`[PROVED]` `k = 0` floor of 4 (the `φ(8)` spine); §2's slot-counting argument for why small
`m` forces large `N`.

**n = 8 is not proved.**
