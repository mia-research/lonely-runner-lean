# Depth cells: walls are homogeneous, cells are cones, and enumeration does not localise them

Continues `DEPTH_CELLS_v1` and `DEPTH_CELL_LAW_v1`. Three tests, two negatives, one structural
result.

---

## 1. Wall enumeration: confirms the form, fails as a search method

Walls have the form `c* = e(8M±1)/(8N+1)`, which is enumerable. Enumerating for
`e ∈ {74,96,127,159,175,224}`, `M, N ≤ 14`, over `c ∈ [20,60]`:

```
  399 candidate walls enumerated
  6 of the 7 observed cell boundaries recovered
  missing: 1431/47  (the derived-scale wall, as expected)
```

**The form is confirmed.** But as a way to find deep cells it fails outright. Probing the tightest
wall gaps against the widest and against random points:

```
  tightest 60 gaps   mean depth 17.68   P(≥20) 0.067
  widest   60 gaps   mean depth 17.60   P(≥20) 0.050
  random   60 points mean depth 17.70   P(≥20) 0.050
```

Indistinguishable. The reason: **399 candidates against ~8 real cells.** Almost no enumerable wall
is realised — which `(e, M, N)` becomes an actual boundary depends on the trajectory, and
enumeration cannot see that. Hypothesis refuted.

## 2. Are cells boxes? Locally yes, globally no

A 2-D slice (minimum `c` against the largest disparity), other five fixed:

```
  depth-23 region: 99 grid points, bounding box 9 × 11 = 99, fill 1.0000  → a perfect box
```

But the depth-0 boundary in the same map is plainly **diagonal**. Bisected exactly, for eight
values of the largest disparity:

```
      big     c* (boundary)        big/c*
      215    30.7142857143      7.000000000
      224    32.0000000000      7.000000000
      260    37.1428571429      7.000000000
```

**`big = 7c` exactly, every time.** So that wall is a line through the origin, not a box edge. Cells
are not boxes; depth does not factorise coordinate-wise.

## 3. The structural statement: walls are homogeneous, cells are cones

Depth is scale-invariant (re-verified: `×2, ×3, ×5` all give 23). A scale-invariant function's level
sets are **cones**, so every wall must be a homogeneous hypersurface. Combined with §1's form, the
walls are the rational hyperplanes

```
      q · a_i  =  p · a_j          q = 8N ± 1,   p = 8M ± 1
```

Checks out on every wall found so far:

```
  big = 7c            1·big = 7·c                       (S = 7, the proved wall)
  c = 1225/41         41·c  = 7·175      = 7·a_175
  c =  518/17         17·c  = 7·74       = 7·a_74
  c = 2016/65         65·c  = 9·224      = 9·a_224
```

**So depth lives on the projectivised disparity space** — 6 dimensions once scale is quotiented —
and is constant on the cells cut by those hyperplanes. In a 2-D slice this produces exactly what the
map shows: vertical walls (pairing `c` with a fixed disparity), horizontal walls (pairing `big` with
a fixed one), and lines through the origin (pairing `c` with `big`). The depth-23 box is a box
*because both its walls pair with fixed coordinates*; it is a 2-D face of a cone, not a box in
general.

## 4. What this maps, cumulatively

| | |
|---|---|
| depth is constant on cells | ✅ |
| cells are cones; walls are `q·a_i = p·a_j` with `p, q ≡ ±1 (mod 8)` | ✅ |
| cell width decays `×0.839` per unit depth | ✅ correlation −0.718 over 96 cells |
| the decay base is the cascade's contraction rate | ~ 1.192 fitted vs 1.113 measured, 6.6% apart |
| walls can be enumerated from the disparities | ✅ 6/7 |
| …and enumeration localises deep cells | ❌ 399 candidates, ~8 realised |
| cells are boxes | ❌ `big = 7c` is diagonal |

## 5. Scope

All figures are exact on the configurations tested (boundaries bisected to `10⁻¹²`, verified by
retracing). §3's hyperplane form is verified on the walls found so far and follows from
scale-invariance plus §1's form; it is not proved that every wall has small `p, q`.

```bash
python3 experiments/n8/wall_search_v1.py   # 6/7 recovered; the tight-gap probe fails
python3 experiments/n8/cell_2d_v1.py       # the 2-D depth field
python3 experiments/n8/cell_2d_v2.py       # big = 7c exactly; homogeneity spot checks
```
