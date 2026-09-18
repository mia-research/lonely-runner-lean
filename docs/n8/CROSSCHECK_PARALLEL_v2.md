# Cross-check: the parallel session's perturbation analysis

Their thesis is sound and independently matches mine. Four specific claims tested: **two confirmed
exactly, one wall value wrong, one causal mechanism refuted.**

---

## 0. Independent agreement on the structure

They describe depth as piecewise constant on "chambers" in `ℝ⁷₊`, bounded by hyperplanes where
`d_a/D_j = 8N ± 1`. That is the same object I reached separately as cones cut by
`q·a_i = p·a_j` (`DEPTH_CELLS_v2`). Two routes, same structure — worth recording as mutual
confirmation rather than duplication.

## 1. ✅ "Varying `d₆ = 224` across `[223.80, 224.20]` holds depth at exactly 23"

**Confirmed.** 41 sample points across that interval, **all depth 23**.

## 2. ❌ "`d₀ = 30` holds depth 23 until the exact wall at `29.875 = 239/8`"

**The wall is not there.**

```
  c = 239/8   = 29.875000 :  just below 18,  just above 18   → NOT a wall
  c = 1225/41 = 29.878049 :  just below 18,  just above 23   → IS the wall
  depth at exactly 29.875 : 18
```

`239/8` also fails the band-edge form on its face — a wall is `e(8M±1)/(8N+1)`, and `8` is not
`8N ± 1`. The actual wall `1225/41 = 175·7/41` has `41 = 8·5+1` and `7 = 8·1−1`, as it must.

Their *left* endpoint for the depth-23 chamber is off by 0.003, which also means the chamber they
describe is slightly wrong: it runs `(1225/41, 1431/47)`, not from `239/8`.

## 3. ❌ "`224 → 225` collapses depth because 225 loses colliding status (`8 ∤ 225`)"

**Refuted by the neighbouring values.**

```
    d₆    8 | d    depth
   221    False      23     ← non-colliding, still depth 23
   222    False      23
   223    False      23
   224     True      23
   225    False       1
   232     True       1     ← colliding, still depth 1
   240     True       1
```

Non-colliding values `221, 222, 223` give depth 23; colliding values `232, 240` give depth 1.
**Colliding status is not what drives the collapse.**

What does: bisecting the wall between 224 and 225 puts it at **exactly 225**, and

```
    225 = 175 · 9/7      e = 175 a disparity,  9 = 8·1+1,  7 = 8·1−1
```

So `d₆ = 225` sits precisely on a band-edge wall. The collapse is a chamber crossing, in their own
framework — their geometry (§1) explains it and their divisibility argument (§3) is not needed and
is not correct.

Worth noting the thesis survives: **perturbing a multi-step setter is fragile** is right; only the
proposed reason is wrong.

## 4. ✅ The setter census

```
   mine:  {30: 1, 74: 3, 96: 3, 127: 4, 159: 4, 175: 4, 224: 4}   total 23
  theirs: {30: 1, 74: 3, 96: 3, 127: 4, 159: 4, 175: 4, 224: 4}
```

**Exact match**, including which steps each sets. Their relay-chain description — four disparities
setting four moves each, two setting three, `d_min` setting one — is correct.

## 5. Where we differ on `d_min`

They call `d_min` "robust" because `30 ± 1 ⟹ depth 18` while setters collapse to 1. That reading is
fair. My cell census adds the quantitative version: the `d_min` axis carries **8 cells** over
`c ∈ [20,60]` with depths `16, 17, 18, 23, 19, 18, 19, 0` — so `d_min` perturbation stays *high* but
is not flat, and the depth-23 chamber on that axis is only `0.569` wide.

## 6. Net

| claim | verdict |
|---|---|
| chamber/wall geometry | ✅ independently confirmed |
| `224 ∈ [223.8, 224.2]` holds 23 | ✅ 41/41 |
| wall at `239/8` | ❌ not a wall; it is `1225/41` |
| collapse caused by losing `8 ∣ d` | ❌ 221–223 non-colliding give 23; 232, 240 colliding give 1 |
| setter census and relay chain | ✅ exact match |

```bash
python3 experiments/n8/crosscheck_parallel_v2.py
```
