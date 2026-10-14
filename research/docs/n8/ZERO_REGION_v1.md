# The zero set is a cell with the units pinned — the reduction improves

Doing the local analysis **exactly** (BSM discipline: the AP is a boundary configuration, so
floating point cannot sit on it — the `2.8e-4` floor in `zero_length_v1.py` was machine-limit
fragility, not evidence) changes the picture, and improves the reduction.

---

## 1. The first-order structure is the unit/non-unit split

Exact rates of the uncovered-length functional at the AP, per coordinate:

```
      reading 2 :  rate 0   both directions
      reading 3 :  rate 14/3   and  18/3
      reading 4 :  rate 0   both directions
      reading 5 :  rate 18/5   and  14/5
      reading 6 :  rate 0   both directions
      reading 7 :  rate 22/7   and  10/7
```

**Zero on the non-units `2,4,6`; positive on the units `3,5,7`.** And the `+` rates are derived, not
fitted: reading `p` guards the protected points `R = p` and `R = p+8`, so raising it opens
`pε/(p+ε) + (p+8)ε/(p+ε)`, giving rate `(2p+8)/p`:

```
      p = 3 →  14/3        p = 5 →  18/5        p = 7 →  22/7
```

All three match. This is `Guard.unguarded_width` applied at each unit.

## 2. So the AP is **not** an isolated zero — the zero set is a cell

Bisected exactly, with the other readings held at the AP:

```
      reading 2 :  uncovered = 0  for  s ∈ (161/81,  175/87)   ≈ (1.98765, 2.01149)
      reading 4 :  uncovered = 0  for  s ∈ (195/49,  285/71)   ≈ (3.97959, 4.01408)
      reading 6 :  uncovered = 0  for  s ∈ (435/73,  623/103)  ≈ (5.95890, 6.04854)
```

Rational endpoints — e.g. `175/87 = (8·22−1)/(8·11−1)` and `161/81 = (8·20+1)/(8·10+1)`, the same
band-edge ratio form as the depth-cell walls (v11 §12).

And the units are **pinned**: over 40 nearby rationals at step `1/1000` around each of `3, 5, 7`, the
uncovered length is zero at **none** of them.

**`REDUCTION_v1`'s claim "uncovered = 0 ⟹ profile = AP" is therefore false, and is withdrawn.**

## 3. The reduction improves

What is invariant across the zero cell is what matters. Checked at the corners and centre:

```
   [2,     3, 4,     5, 6,     7]   uncovered 0   clear {1,3,5,7,9,11,13,15}
   [201/100,3, 4,     5, 6,     7]  uncovered 0   clear {1,3,5,7,9,11,13,15}
   [2,     3, 401/100,5, 6,     7]  uncovered 0   clear {1,3,5,7,9,11,13,15}
   [2,     3, 4,     5, 601/100,7]  uncovered 0   clear {1,3,5,7,9,11,13,15}
   [201/100,3,401/100,5,601/100,7]  uncovered 0   clear {1,3,5,7,9,11,13,15}
```

**All eight protected points stay clear across the whole cell**, because they are guarded by the
units, which are pinned. So:

> **uncovered = 0 ⟹ the units are `3, 5, 7` ⟹ the eight protected points are clear ⟹ the clear set
> is non-empty ⟹ `R < 16` ⟹ Existence at order 8.**

That is **weaker than uniqueness of the AP** — the non-units may float freely within explicit
rational intervals and nothing changes. What must be shown is only that the *units* are pinned.

## 4. The gap, restated

```
   Existence  ⟸  clear set non-empty in [1,15]        [PROVED]
              ⟸  uncovered > 0  OR  units = 3,5,7     [PROVED]  via Guard.ap_clear_at_odd
              ⟸  uncovered = 0  ⟹  units = 3,5,7      ← THE GAP
```

The gap is now a statement about **three** coordinates rather than six, and about a functional with
an exact local expansion at the candidate — rate `(2p+8)/p` upward at each unit, and `0` at each
non-unit. Those rates are the mechanism, not a fit.

## 5. What this round established

| | |
|---|---|
| exact first-order rates at the AP, all six directions | **`[VERIFIED — exact rationals]`** |
| rates are `0` on non-units, positive on units | **`[VERIFIED]`**, and derived from the guard structure |
| the `+` rate at unit `p` is `(2p+8)/p` | **`[PROVED — in the text]`** from `Guard.unguarded_width` |
| the zero set is a cell with explicit rational faces | **`[VERIFIED — exact bisection]`** |
| the units are pinned on that cell | **`[VERIFIED]`** at step `1/1000` |
| the AP is the unique zero | **withdrawn** — `REDUCTION_v1` §3 corrected |
| `uncovered = 0 ⟹ units = 3,5,7` | the remaining gap |

```bash
python3 experiments/n8/exact_local_v1.py   # the six exact rates
python3 experiments/n8/zero_family_v1.py   # the zero set is a region, not a point
python3 experiments/n8/zero_region_v1.py   # exact cell faces; the units pinned
```
