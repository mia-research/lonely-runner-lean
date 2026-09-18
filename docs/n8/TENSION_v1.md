# Narrowing the interlocking obstruction: what held, what broke

Continues `TOUCHPOINT_v1`. Three findings, one of them a clean negative that closes a promising
route.

---

## 1. The region splits — and this is new

The region to cover is `[1,7] ∪ [9,15]`. The gap `(7,9)` **is** `s₁ = 1`'s own bad interval, so no
chain ever needs to cross it.

> **`[1,7]` and `[9,15]` must be covered independently, by the same six combs.**

That is a genuine structural simplification: two length-6 problems rather than one length-14 problem,
coupled only through sharing the combs.

## 2. The per-step ceiling differs sharply between them

At reach `x`, using comb `s` at level `m` needs `(8m−1)/s < x < (8m+1)/s`, so `8m ≈ s·x` and the
multiplier is `(8m+1)/(8m−1)`.

```
      x :  1.0    1.5    2.0    3.0    5.0    7.0  |   9.0   11.0   13.0   15.0
   max  : 1.2857 1.2857 1.2857 1.2857 1.2857 1.2857 | 1.1333 1.1333 1.1333 1.1333
   at m :   1      1      1      1      1      1    |   2      2      2      2
```

`9/7` throughout `[1,7]`; only `17/15` throughout `[9,15]`, because `(8m+1)u > 9` with `u < 1` forces
`m ≥ 2`. Greedy lower bounds with one interval per comb per level: **`[1,7]` needs ≥ 10 intervals,
`[9,15]` needs ≥ 5** — 15 in total, from six combs.

## 3. The tension that looked like it would close — **it does not**

An `m = 2` interval `(15/s, 17/s)` meets `[9,15]` only when `17/s > 9`, i.e. **`s < 17/9 = 1.889`**.
So the fastest route through `[9,15]` needs *small* combs.

Meanwhile `s₇ = S` covers `(7/S, 9/S)` at `m=1` and `(15/S, 17/S)` at `m=2`, leaving the gap
`(9/S, 15/S)`. At `S = 7.45` that is `(1.2081, 2.0134)`, and computing which readings have *any*
interval meeting it:

```
    admissible s :  [3.480, 7.990]        none below 1.889
```

**Disjoint ranges.** A comb cannot both cover that gap and serve `[9,15]` at `m = 2`. Confirmed
directly: with all five interior combs below `1.889`, `R = 1.20805 = 9/S` **exactly**, every time —
the gap is uncovered and the touch point is clear.

### 3.1 Why it does not close

Covering `[9,15]` does not *require* `m = 2`. Larger combs reach it at higher levels with smaller
multipliers and more steps. Maximum reach from `9`, as an upper bound over all profiles with
readings in `[s_min, 8]`:

```
   s_min :  1.889   2.000   2.500   3.000   3.480   4.000   5.000
   reach : 15.474  15.155  15.091  15.344  15.062  15.170  15.275
   steps :     7       7       8      10      11      13      16
```

**`[9,15]` is coverable with every reading ≥ 5.0**, in 16 steps. So Fact B bounds the *fastest*
route, not feasibility, and the disjointness of §3 is not a contradiction. **Route closed.**

## 4. One thing that did hold

Covering `[1,7]` from `R = 1` requires some comb whose interval contains `1`, i.e. a reading in
`(7,9)`:

```
   s_max :  1.889   2.500   3.480   4.000   5.000   6.000   7.000   7.990
   reach :  1.000   1.000   1.000   1.000   1.000   1.000   1.000   7.452
```

The reach never leaves `1` until `s_max` passes `7`. That is `R = 1` being blocked, which is
Corollary 6.21 in another dress — recorded as confirmed, not as new.

## 5. Where the obstruction now stands

| | |
|---|---|
| touch points are clear, so max-reach ≠ covering | **established** (`TOUCHPOINT_v1`) |
| `[1,7]` and `[9,15]` are independent problems | **established**, and new |
| per-step ceiling is `9/7` in one region, `17/15` in the other | **established** |
| fast `[9,15]` coverage needs `s < 1.889` | **established** |
| the gap `(9/S, 15/S)` needs `s ∈ [3.48, 7.99]` | **established** (computed) |
| those two are disjoint, hence a contradiction | **NO** — `[9,15]` is coverable slowly by large combs |

The greedy bounds in §3.1 are **upper bounds over a range**, allowing a fresh `s` at every step. A
real profile has six fixed readings serving both regions at all levels, which is far more
constrained — and that is where the remaining obstruction must live. The greedy cannot see it, and
neither can counting.

```bash
python3 experiments/n8/region_split_v1.py   # the two regions and their ceilings
python3 experiments/n8/tension_v1.py        # the disjoint ranges; R = 9/S when combs are small
python3 experiments/n8/tension_v2.py        # the negative: [9,15] coverable with s >= 5.0
```
