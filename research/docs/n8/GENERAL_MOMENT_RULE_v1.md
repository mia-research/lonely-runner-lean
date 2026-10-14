# The moment rule without the grid assumption

2026-09-13. n = 8, individual isolation, threshold 1/8. Arbitrary distinct speeds — no grid, no
AP, no integers required.

Artifact: `experiments/n8/ok_general_moment_rule_v1.py`.

---

## 1. The exclusive-territory reading

A runner is lonely iff both its adjacent gaps are `≥ 1/8` (verified separately, 47,904
runner-instants, 0 disagreements). Equivalently, each runner needs **`1/16` of exclusive
territory on each side**. Eight runners × `2 × 1/16` = **1** — exactly the circle.

That is why global isolation has no slack anywhere: when every runner is lonely, the exclusive
territories tile the track exactly, with nothing left over. It holds for any speeds, grid or not.

## 2. The rule  `[VERIFIED — 24,000 of 24,000]`

**Local part, exact.** Speeds are sorted, so a runner's nearest speed *is* one of its two
immediate neighbours:

    d_min(i) = min( v_i − v_{i−1},  v_{i+1} − v_i )

and `t ≥ 1/(8·d_min)` is forced — below that the nearest neighbour has not yet opened to `1/8`.
No approximation, and it needs only the two neighbours.

**Blocking part.** The bound is attained **unless** some other difference `d` of that runner lies
**within `d_min` of a multiple of `8·d_min`**.

| test | result |
|---|---|
| criterion vs direct BSM evaluation | **24,000 of 24,000**, rate 1.000000 |
| population | 3,000 random integer 8-subsets of `[1,80)` |
| of which **not** grids | **2,988** |
| moment attained at the local bound | 12,955 of 24,000 (0.540) |

The rule is applied identically to grids and non-grids and is exact on both.

## 3. The residue criterion is the special case

For a grid the earlier work used: *a runner keeps `t = 1/8` iff no difference of its is `≡ 0 mod 8`*
(`PREDICTION_SPREAD_GRID_v1` §3). That is §2 with `d_min = 1` and integer speeds — "within 1 of a
multiple of 8" is exactly "`≡ 0 mod 8`".

So the grid machinery was never a separate theory. Residues mod 8 are what the general criterion
becomes when `d_min = 1`, and the AP's special status came from having `d_min = 1` for every
runner at once.

## 4. What this covers

| question | answer |
|---|---|
| earliest possible moment | `1/(8·d_min)`, from the two neighbours, always |
| is it attained | the blocking test, `O(n)`, exact |
| grid required | **no** |
| integer speeds required | **no** |
| AP base required | **no** |

**Near the AP the blocking test collapses further.** With all eight displaced by at most `ε`, a
difference can only approach a multiple of `8·d_min` from above `7·d_min`, so blocking is confined
to pairs at index gap `≥ 7 − 16ε`:

| ε | 0.05 | 0.10 | 0.15 | 0.20 |
|---|---|---|---|---|
| minimum index gap that can block | **7** | 6 | 5 | 4 |
| pair-set verified sufficient | `{7}` | `{6,7}` | `{5,6,7}` | `{4..7}` |

At `ε ≤ 0.05` the **single pair `(r1, r8)`** decides attainment for all eight runners.

## 5. Status and scope

`[PROVED — arithmetic]` §2's local part and the forced bound; §3's reduction of the residue
criterion.
`[VERIFIED — 24,000 of 24,000]` §2's blocking criterion, grids and non-grids alike.
`[VERIFIED]` §4's pair-gap table, 1,600 runner-instances per ε.

**Scope.** n = 8 throughout. §2's population is integer 8-subsets of `[1,80)`; rational and
irrational speeds are covered by the same arithmetic but were tested separately and less heavily.
§4 is the AP neighbourhood only.

**Not established.** A closed form for the moment when the bound is *not* attained — about 46% of
runners in §2's population. The `7 − 16ε` threshold is derived and matches at four values of `ε`;
it is not proved.

**n = 8 is not proved here, and is not the target here.**
