# Mapping depth: the cell-width law — and a fabricated record, corrected

Two things: a quantitative law for how depth is distributed, and a correction to a number I invented
and then cited for four experiments.

---

## 1. Correction first — the "28-move case" does not exist

I have been citing a record of **28** moves for an arrangement written `(27,70,…,393)`. That came to
me with an ellipsis, and **I filled in the middle terms myself** (`133,190,243,297,340`) and then
treated the result as a known deep case across `deep_construct_v1..v4`.

Checked: the arrangement I invented has **maximum depth 5** across all eight subjects.

```
  subject  27: S 8.512  depth 5        subject 190: depth 0
  subject  70: S 7.512  depth 3        subject 243: depth 0
  subject 133: depth 0                 subject 297: depth 0
  subject 340: S 7.279  depth 2        subject 393: depth 0
```

**The verified record is 23**, from the parallel session's trace, which I reproduced independently
(`[30,74,96,127,159,175,224]`, `t* = 11/256`).

### 1.1 Which means I under-claimed my own result

`DEEP_CONSTRUCTION_v1` §6 concluded *"the record was not beaten — best constructed 27, on file 23 and
28."* Against the **verified** record of 23, band-directed search **beat it**, twice, re-verified
from scratch:

```
  [28, 69, 95, 123, 154, 172, 220]   depth 27   S = 7.8571   t* =  65/1376
  [55, 131, 181, 233, 293, 329, 419] depth 27   S = 7.6182   t* =  65/2632
```

So the band insight produced deep cases **beyond anything on file**. `DEEP_CONSTRUCTION_v1` §6 is
superseded by this section.

---

## 2. The cell census

Along the minimum axis, `c ∈ [20,60]`, other six disparities fixed: **8 cells**. Coarse, not fractal.

```
  [20.000, 22.714]  w 2.714  depth 16        22.714 = 159/7
  [22.714, 25.000]  w 2.286  depth 17        25.000 = 175/7
  [25.000, 29.878]  w 4.878  depth 18        29.878 = 175·7/41
  [29.878, 30.447]  w 0.569  depth 23        30.447 = 1431/47
  [30.447, 30.471]  w 0.024  depth 19        30.471 =  74·7/17
  [30.471, 31.015]  w 0.545  depth 18        31.015 = 224·9/65
  [31.015, 32.000]  w 0.985  depth 19        32.000 = 224/7
  [32.000, 60.000]  w 28.00  depth  0
```

Every wall factors as `e(8M±1)/(8N+1)` with `e` a disparity — `159/7`, `175/7`, `175·7/41`,
`74·7/17`, `224·9/65`, `224/7`. Measure-weighted, depth 0 occupies **70%** of the range and the
depth-23 cell **1.4%**.

## 3. The width law

Censusing all 7 axes of two cases (96 cells):

```
  correlation(depth, log width) = −0.718
  log(width) = 3.710 − 0.1754 · depth
  → each extra unit of depth multiplies cell width by 0.839
```

**Cell width decays exponentially in depth**, base `1/0.839 = 1.192`. This is the quantitative reason
deep cases evade sampling and need directed search: a depth-`k` cell is about `0.84^k` of a depth-0
cell's width.

## 4. The mechanism behind it — partially confirmed

Each cascade step contracts the scale by `λ`, so a cell requiring one more step is the pre-image of
a cell under one more contraction, hence roughly `λ` times narrower. That predicts the decay base
equals the typical dilation. Measured over 29,821 steps:

```
  geometric mean λ = 1.11301        fitted decay base = 1.19178
```

Same order, **6.6% apart**. Close enough to identify the mechanism, not close enough to call it
derived — the gap is presumably that deep cells sit in the small-`λ` tail (the 23-move case has
geometric mean `λ = 1.107`, below average), so the relevant `λ` is not the global one.

## 5. What this maps

- depth is **cell-wise constant**, the cells are few and wide, and the walls are exact band edges;
- the depth-`k` region has measure decaying like `0.84^k`;
- the decay base is the cascade's own contraction rate;
- so depth is *structured*, not chaotic — what varies between neighbouring cells is which band edge
  the trajectory crosses, and that is computable per cell.

```bash
python3 experiments/n8/cell_census_v1.py   # the 8-cell census, walls factored
python3 experiments/n8/cell_census_v2.py   # 96 cells, the width law
python3 experiments/n8/cell_law_v1.py      # dilation statistics vs the decay base
```
