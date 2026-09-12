# Working note — sweeping runners from grid bases of different shapes

2026-09-12. n = 8, individual isolation. Extends `WN_grid_base_sweeps_2026_09_12.md` from
the tight grid to grids of other shapes. BSM in integer arithmetic, exact.

## 1. The bases

A grid is any complete residue system mod 8 (`WHICH_GRIDS_ISOLATE_v1` §1). Base minima:

| base | residues mod 8 | grid? | min count |
|---|---|---|---|
| `(1,…,8)` tight | complete | yes | **4** |
| `(1,…,6,15,24)` doubly spread | complete | yes | 6 |
| `(1,…,7,16)` spread tail | complete | yes | 8 |
| `(1,58,…,64)` back-loaded | complete | yes | 10 |
| `(1,64,72,…,112)` | `{0,7}` only | **no**, `k=6` | 56 |

The set named as a "reverse grid", `(1,64,72,…,112)`, is not a grid — seven of its eight
runners share residue 0 mod 8. It is also the safest thing tested anywhere, min count 56.

**Tighter grids are more dangerous.** The tight AP grid bottoms at 4; spreading the base
raises the base minimum monotonically to 6, 8, 10.

## 2. Every grid reaches the floor under a single move  `[VERIFIED]`

Sweeping one runner over integers `2..90` (back-loaded) or `1..60` (others):

| base | base min | move | reaches |
|---|---|---|---|
| tight `(1..8)` | 4 | r2 → 9 | **2** |
| spread tail `(1..7,16)` | 8 | r2, r6, r7 → 8; r8 → 9 | **2** |
| doubly spread `(1..6,15,24)` | 6 | r1 → 8 | **2** |
| back-loaded `(1,58..64)` | 10 | r7 → 57 | **2** |

So the base minimum varies with shape (4 to 10), but **one move reaches 2 from every grid
shape tested**. Spreading the base delays the fall; it does not prevent it.

The move is always to an **integer**, never a fraction, and always to a position adjacent to
or filling a gap in the existing cluster.

## 3. Two sampling errors in this note's own first attempts

**Too narrow a sweep.** Sweeping each back-loaded cluster runner across its own ±1 gap at
resolution 1/12 gave minimum **10 at the base position itself**, with every off-position
higher — suggesting the back-loaded grid is a local worst that perturbation only improves.
That was an artefact: each cluster runner's neighbours occupy the adjacent integers, so the
only integer in range was the base, and everything else was forced off-lattice, where counts
are large. Widening to integers `2..90` found **2** at r7 → 57.

**Upward only.** A `+1/24 … +8` sweep found the back-loaded base bottoming at 4 (r3 → 65).
The actual minimum of 2 is at 57, **below** the runner's position. As with the AP sweeps, the
downward direction carried the worse case.

## 4. The count-2 configurations are a family, not one set

Reduced forms of the five count-2 configurations reached above:

| base + move | reduced set |
|---|---|
| tight, r2 → 9 | `{0,2,3,4,5,6,7,8}` — the 9-grid less **1** |
| spread tail, r8 → 9 | `{0,1,2,3,4,5,6,8}` — the 9-grid less **7** |
| spread tail, r2 → 8 | `{0,2,3,4,5,6,7,15}` |
| doubly spread, r1 → 8 | `{0,1,2,3,4,6,13,22}` |
| back-loaded, r7 → 57 | `{0,56,57,58,59,60,61,63}` |

Five **distinct** configurations. `WN_grid_base_sweeps` §3 reported three routes converging on
the single set `(0,1,2,3,4,5,6,8)`; that convergence was real for those three routes but does
not generalise — count 2 is reached by a family. What the members share is a **dense
near-run**: `{0,56,…,61,63}` is `{0}` plus a run of seven, `{0,1,2,3,4,6,13,22}` contains a
run of five.

## 5. Status

`[VERIFIED — exact]` §1's base minima; §2's wide integer sweeps; §4's reduced forms.
`[RECORDED]` §3's two sampling errors, both mine, both in the direction of a false floor.
`[NARROWED]` `WN_grid_base_sweeps` §3's convergence claim — see §4.

**n = 8 is not proved.**
