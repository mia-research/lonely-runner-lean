# The spine and the reserve — how loneliness times transform off the grid

2026-09-12. n = 8, individual isolation. Structural reading of the mapping series
(`WN_offap_displacement_map`, `WN_grid_base_sweeps`, `WN_grid_shapes`,
`WN_grid_shape_space`). Tracks the loneliness **times**, not just their count.

## 1. The spine

At any grid — any complete residue system mod 8 — the configuration is globally isolated at
exactly `φ(8) = 4` instants, `t = p/(8g)` with `p` odd (`WHICH_GRIDS_ISOLATE_v1` §1). These
four instants lie in **every** runner's good set simultaneously. Call them the **spine**.

Everything else in a runner's good set is its **reserve**: windows it holds that no other
runner need share.

A runner is lonely at `p/8` iff no difference of its is `≡ 0 mod 8` (for `p` odd,
`8 | dp ⟺ 8 | d`). So the spine is all-or-nothing: a runner holds all four or none.

## 2. The decomposition  `[VERIFIED — exhaustive over 6,305 grid shapes]`

Enumerating every grid shape `q ∈ {0,1,2}⁸` (`WN_grid_shape_space` §1):

| base min | shapes | all runners hold the spine | fewest extras |
|---|---|---|---|
| 4 | 311 | 311 | 0 |
| 6 | 1441 | 1441 | 2 |
| 8 | 2467 | 2467 | 4 |
| 10 | 1441 | 1441 | 6 |
| 12 | 532 | 532 | 8 |
| 14 | 96 | 96 | 10 |
| 16 | 15 | 15 | 12 |
| 18 | 2 | 2 | 14 |

> **`base min = 4 + (fewest extras)`, for every grid shape without exception.**

Every grid gives every runner the spine; shapes differ only in the reserve. Reserve profiles:

    tight AP      0, 4, 4, 2, 2, 4, 4, 0      base min 4
    alternating   8,12, 8, 2, 2, 8,12, 8      base min 6
    spread tail   6, 4, 6, 6, 4, 4, 4, 8      base min 8
    two clusters  6,14,12, 8, 8,12,14, 6      base min 10
    wide linear  10,14,10,14,12,10,18,10      base min 14

The tight AP is the unique worst case because its **two end runners have zero reserve** —
their entire good set is the spine.

## 3. What a move does to the times  `[VERIFIED — exact]`

Tight grid `(1,…,8)` → r2 moved to 9, the transition that reaches count 2:

    BEFORE  residues 0,1,2,3,4,5,6,7   every runner: spine 4/4
            extras  0, 4, 4, 2, 2, 4, 4, 0        counts 4,8,8,6,6,8,8,4

    AFTER   residues 0,0,2,3,4,5,6,7   r1 and r2 now collide mod 8
            r1  spine 0/4, 2 windows   <- was 4 windows, all spine
            r2  spine 0/4, 6 windows
            r3..r8  spine 4/4, extras gained

The mechanism, in three steps:

1. **A move that creates a mod-8 collision destroys the spine for exactly the colliding
   pair** — all four instants at once, since the spine is all-or-nothing.
2. **Runners with reserve survive it.** The other six keep 4/4 and in fact gain extras.
3. **A runner with zero reserve has nothing to fall back on.** r1 held only the spine; losing
   it drops it from 4 to whatever fringe windows the new configuration happens to give — here
   2.

This is why vulnerability tracks the base minimum so cleanly
(`WN_grid_shape_space` §3): 80% of base-4 shapes fall to 2 under one move, 0% of base-16
shapes do. The base minimum *is* the reserve, and the reserve is what survives a collision.

## 4. Why spread grids resist

**CORRECTED.** An earlier version said a collision "leaves the reserve intact — so the runner
lands at its reserve value, not near zero". That is false, and false in the direction that
matters.

Measured over 252 spine-losing runner-instances across single moves off grids in `[1..16]`:

| reserve after vs before | up | same | down |
|---|---|---|---|
| instances | **252** | 0 | 0 |

**Losing the spine creates reserve.** Of the 69 spine-losers that had reserve 0 beforehand,
the counts after are 2, 4 and 6 — **none at 0**. On the worked move of §3, the runner at
reduced speed 0 had reserve 0, lost all four spine instants, and landed at **2**.

Had a zero-reserve runner actually landed at its reserve value it would have landed at 0. The
compensation is the entire content: the runner drops onto a finer 2-power lattice
(`GRID_TOWER_v1`) and acquires windows that did not exist before.

The 5.84 → 5.87 mean reported elsewhere is for runners that **kept** the spine, a different
population, and says nothing about this.

A spread grid still needs two moves to reach 2 while the tight grid needs one
(`WN_grid_shape_space` §4) — but the reason is not "no reserve left to dismantle".

## 5. Reading

The permutation picture now has a mechanism attached. Going off grid does not erode isolation
diffusely. It removes **one specific object**, the four-instant spine, from **exactly the
runners that collide mod 8**, and leaves everything else untouched. What determines whether
that is survivable is a quantity computable at the grid itself, before any move: the runner's
reserve.

Two consequences worth stating:

- The `φ(8)` law is not only about global isolation. The four instants it produces are the
  **shared backbone of every runner's individual good set at a grid**, and the whole
  off-grid story is about who keeps them.
- "Distance from the AP" was never the right variable. **Reserve** is: the tight AP is
  dangerous not because it is a reference point but because it is the grid shape in which two
  runners have none.

## 6. Status

`[PROVED]` §1's all-or-nothing property of the spine (`8 | dp ⟺ 8 | d` for `p` odd);
the `φ(8)` count at a grid.
`[VERIFIED — exhaustive]` §2's identity over all 6,305 grid shapes, no exceptions.
`[VERIFIED — exact]` §3's transition.

**n = 8 is not proved.** Nothing here bounds the reserve below, and a runner with zero
reserve landing on 2 rather than 0 is observed, not derived.
