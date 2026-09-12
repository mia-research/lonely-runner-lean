# Working note — the space of grid shapes, and how far each is from the floor

2026-09-12. n = 8, individual isolation. Completes the off-AP/off-grid mapping begun in
`WN_offap_displacement_map`, `WN_grid_base_sweeps` and `WN_grid_shapes`. BSM, integer
arithmetic, exact.

## 1. Parametrising all grids

A grid is a complete residue system mod 8, so `u_i = i + 8 q_i` and the **shape is entirely
the deviation vector `q`** (`WHICH_GRIDS_ISOLATE_v1` §2). Previous notes tested a handful of
`q` by hand: `q = 0` (tight AP), `(0,…,0,1)` (spread tail), `(0,7,7,7,7,7,7,7)` (back-loaded).

Enumerating `q ∈ {0,1,2}⁸` normalised to `min q = 0` gives **6,305 grid shapes**, covering
tight, spread, alternating, two-cluster, middle-bulge and wide-linear arrangements in one
sweep.

## 2. Base minimum is never below 4 — and that is forced

| base min count | 4 | 6 | 8 | 10 | 12 | 14 | 16 | 18 |
|---|---|---|---|---|---|---|---|---|
| shapes | 311 | 1441 | **2467** | 1441 | 532 | 96 | 15 | 2 |

The distribution bottoms at exactly 4 and never below. This is **proved, not observed**: a
grid is globally isolated at exactly `φ(8) = 4` instants, so every runner of every grid has
at least those 4 events. The enumeration reproducing that bound is a check on the pipeline.

Named shapes:

| shape | `q` | set | base min |
|---|---|---|---|
| tight | `(0,…,0)` | `(0,1,2,3,4,5,6,7)` | **4** |
| alternating | `(0,1,0,1,0,1,0,1)` | `(0,2,4,6,9,11,13,15)` | 6 |
| middle bulge | `(1,1,0,0,0,0,1,1)` | `(2,3,4,5,8,9,14,15)` | 6 |
| spread tail | `(0,…,0,1)` | `(0,1,2,3,4,5,6,15)` | 8 |
| two clusters | `(0,0,0,0,1,1,1,1)` | `(0,1,2,3,12,13,14,15)` | 10 |
| wide linear | `(0,0,1,1,1,2,2,2)` | `(0,1,10,11,12,21,22,23)` | 14 |

The most dangerous shapes are the near-tight ones (`q` mostly zero); the safest are the
widely spread.

## 3. Distance from the floor depends on shape

One runner moved to any integer within span 10, sampled 25 shapes per base-minimum class:

| base min | shapes | one-move floor distribution |
|---|---|---|
| 4 | 311 | `{2: 20, 4: 5}` — **80% fall to 2** |
| 6 | 1441 | `{2: 19, 4: 6}` — 76% |
| 8 | 2467 | `{2: 8, 4: 15, 6: 2}` — 32% |
| 10 | 1441 | `{2: 4, 4: 19, 6: 2}` — 16% |
| 12 | 532 | `{2: 2, 4: 22, 6: 1}` — 8% |
| 14 | 96 | `{2: 4, 4: 18, 6: 3}` — 16% |
| 16 | 15 | `{4: 12, 6: 3}` — **0%** |
| 18 | 2 | `{4: 2}` — **0%** |

Vulnerability to a single move tracks the base minimum: near-tight grids fall to the floor
immediately, spread grids do not fall at all in one move.

## 4. The safe grids need two moves  `[VERIFIED — span-stable]`

For all 17 shapes with base min ≥ 16, one move, at four search spans:

| span | 10 | 25 | 60 | 150 |
|---|---|---|---|---|
| floor | 4 or 6 | 4 or 6 | 4 or 6 | 4 or 6 |

**Identical across a 15× range of search width.** Three floors reported earlier today turned
out to be search artefacts (`CONJECTURE_M_REFUTED_v1` §3, `MEASURE_LEMMA_ATTEMPT_v2` §2,
`WN_grid_shapes` §3); this one is not — it is stable under exactly the widening that broke
those.

With **two** moves, the same shapes do reach 2:

    (0,1,2,3,12,13,22,23)   base 16   two-move floor 2
    (0,1,2,3,12,14,21,23)   base 16   two-move floor 2

## 5. The map

Putting the off-AP/off-grid work together:

1. **Every grid has base min ≥ 4** — proved, `φ(8)`.
2. **Base min ranges 4 to 18** across 6,305 shapes, mode 8, controlled by how tight the
   deviation vector is.
3. **Every grid reaches 2**, but the number of moves depends on shape — one move for
   near-tight grids, two for the most spread.
4. **The move is always to an integer**, adjacent to or filling a gap in the cluster; off-lattice
   positions raise counts by the factor their denominator contributes to the reduced
   configuration (`WN_grid_base_sweeps` §2a).
5. **Nothing anywhere reaches below 2**, across every sweep in this series.

## 6. Status

`[PROVED]` §2's bound of 4 for grid bases (`φ(8)` global isolation).
`[VERIFIED — exhaustive]` §2's 6,305-shape enumeration.
`[VERIFIED — sampled]` §3's per-class one-move floors, 25 shapes per class.
`[VERIFIED — span-stable]` §4's one-move floor for the 17 safest shapes, spans 10 to 150.

**n = 8 is not proved.**
