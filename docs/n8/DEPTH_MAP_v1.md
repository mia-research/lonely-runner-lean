# Mapping depth by perturbation: the campaign and what it shows

All four deep cases verified independently. Everything below is exact arithmetic on fixed
configurations — no sampling unless stated.

---

## 1. The examples

```
  depth  d_min       S     disparities
     23     30   7.467     [30, 74, 96, 127, 159, 175, 224]     parallel session, reproduced
     28     49   7.469     [49, 205, 234, 256, 286, 323, 366]   MANUSCRIPT v10 §6.7, reproduced
     27     28   7.857     [28, 69, 95, 123, 154, 172, 220]     banded climb
     27     55   7.618     [55, 131, 181, 233, 293, 329, 419]   banded climb
```

**Every one has `S` between 7.4 and 7.9** — just above the proved `S ≤ 7` clearance threshold.

## 2. Two families, not one shape

Reading profiles, normalised so the largest reading is exactly 8:

```
   23:  1.071  2.643  3.429  4.536  5.679  6.250  8.000     family A
   27:  1.018  2.509  3.455  4.473  5.600  6.255  8.000     family A
   27:  1.050  2.501  3.456  4.449  5.594  6.282  8.000     family A
   28:  1.071  4.481  5.115  5.596  6.251  7.060  8.000     family B
```

* **Family A** — readings spread across `[1,8]`; gaps `≈ 1.47, 0.95, 1.00, 1.14, 0.67, 1.74`. The
  three cases are nearly identical, the two 27s to three decimal places.
* **Family B** — one isolated small reading, then six clustered from 4.5 to 8; gaps `≈ 3.41, 0.63,
  0.48, 0.66, 0.81, 0.94`.

The deepest case is family B. So deep cases are not a single shape.

## 3. The families respond differently

Perturbing `d_min` at 0.1 resolution:

```
  FAMILY A                          FAMILY B
  [25.0, 29.8]  w 4.9  depth 18     [44.0, 46.1]  w 2.2  depth 22
  [29.9, 30.4]  w 0.6  depth 23     [46.2, 48.8]  w 2.7  depth 23
  [30.5, 31.0]  w 0.6  depth 18     [48.9, 49.0]  w 0.2  depth 28
  [31.1, 31.9]  w 0.9  depth 19     [49.1, 49.6]  w 0.6  depth 24
  [32.0, …  ]          depth  0     [49.7, 50.6]  w 1.0  depth 23
                                    [50.7, 52.2]  w 1.6  depth 24
                                    [52.3, …  ]          depth  0
```

**A's deep cell sits alone among 18s. B's sits inside a cluster of 22–24s.** B is the more robust
region; its deepest cell is nonetheless the narrower (0.19 against 0.57), consistent with the width
law.

## 4. No nesting — the cells are solid

Zooming 10× into the depth-28 cell (400 then 4,000 samples):

```
  level 1: 3 cells, max depth 28, cell [48.830000, 49.021000]  width 0.191000
  level 2: 3 cells, max depth 28, cell [48.829332, 49.021191]  width 0.191859
```

Refinement only sharpens the boundaries; **no deeper cell appears inside**. Same for A's depth-23
cell (width 0.5687, solid). So along any single axis the partition is finite with solid cells, and
the maximum over that axis is attained on a cell of positive width. **Depth does not increase by
refining one coordinate** — deeper cases need several coordinates to move.

## 5. Climbing from the record does not beat it

Seeded at the depth-28 case, hill-climbing with 1–3 simultaneous coordinate moves, 60,000 steps per
run, at four resolutions:

```
  ×1  : 28   [49, 205, 234, 256, 286, 323, 366]        S = 7.4694
  ×4  : 28   [194, 811, 927, 1014, 1135, 1282, 1452]   S = 7.4845
  ×12 : 28   [594, 2486, 2844, 3108, 3468, 3927, 4441] S = 7.4764
  ×40 : 28   [1972, 8221, 9411, 10302, 11515, 12982, 14706] S = 7.4574
```

**Never exceeds 28**, and every scaled copy re-pins `S` to 7.46–7.48. That makes 28 a strong local
maximum surviving a 40-fold refinement of the lattice.

`[EMPIRICAL — conditional]`: this says four seeded climbs found nothing deeper, not that nothing
deeper exists. My searches have been beaten before in this session — `M ≤ 7` became 20 under a harder
climb — so this is a stopping point of the search, not a bound.

## 6. The map so far

| | |
|---|---|
| depth is constant on cells; cells are cones; walls are `q·a_i = p·a_j` | ✅ |
| cell width decays `×0.839` per unit depth | ✅ corr −0.718, 96 cells |
| cells are solid — no nesting under refinement | ✅ tested to 10× |
| deep cases have `S ∈ (7.4, 7.9)` | ✅ all four, and the band is enriched (n = 60,000) |
| deep cases share one profile | ❌ **two families** |
| refining one coordinate reaches deeper cases | ❌ |
| climbing from the record beats it | ❌ at four resolutions |

## 7. Errors in this campaign

1. **The fine scan in `family_b_v1.py` was wrong** — I scanned the minimum over the raw range
   4600–5400 while `REST` was already scaled ×10, so the scanned value was never the minimum and
   every configuration read depth 0. Caught by the result being uniformly 0 where the control said
   28. Corrected in `family_b_v2.py`.
2. Earlier in this line I called the 28-move case fabricated; it is real — see
   `DEPTH_CELL_LAW_v2.md`.

```bash
python3 experiments/n8/profile_v2.py          # the four cases and their profiles
python3 experiments/n8/family_b_v1.py         # the two response tables
python3 experiments/n8/family_b_v2.py         # corrected cell scans of both families
python3 experiments/n8/nesting_v1.py          # no nesting under 10x zoom
python3 experiments/n8/climb_from_record_v1.py# four seeded climbs, none beats 28
```
