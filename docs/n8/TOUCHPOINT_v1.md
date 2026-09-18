# The touch-point obstruction — the first real interlocking mechanism, and what it does not give

Chasing the interlocking obstruction. One genuine mechanism found, one reporting defect of mine
corrected.

---

## 1. The mechanism

The LP search attains exactly `(9/7)^6` for the maximum reach with six intervals
(`ANALYTIC_LAST_STEP_v2`). That ceiling is **forced**: to use comb `s` at level `m = 1` from reach
`x` you need `s·x ∈ (7,9)`, and the new reach is `9/s`. Maximising drives `s → 7/x`, so

```
        x_0 = 1,   s_j = 7/x_{j−1},   x_j = (9/7)·x_{j−1}
```

— a **geometric profile with ratio `9/7`**, descending `7, 5.444, 4.235, 3.294, 2.562, 1.993`, six
combs, reach `(9/7)^6 = 4.5172`. Exactly what the LP found, from a search that knew none of this.

**But driving `s → 7/x` makes interval `j` start exactly where interval `j−1` ends.** Bad intervals
are **open**, so the touch point is covered by neither. It is a clear `R`.

### 1.1 Verified exactly

For the forced geometric profile, in exact rationals:

```
      S = 7.010 :  R = 900/701 = 1.283880   =  9/S
      S = 7.050 :  R =  60/47  = 1.276596   =  9/S
      S = 7.100 :  R =  90/71  = 1.267606   =  9/S
      S = 7.300 :  R =  90/73  = 1.232877   =  9/S
      S = 7.450 :  R = 180/149 = 1.208054   =  9/S
```

**`R = 9/S` exactly, every time** — the first junction. The configuration that maximises reach
clears at the earliest possible touch point.

> **Maximising reach and covering are in direct tension.** The `(9/7)^6` ceiling is approached only
> by configurations that are *not* coverings.

That is an interlocking obstruction in the proper sense: it is arithmetic (open intervals, exact
endpoints), not measure-theoretic, and it explains why the LP's ceiling is unattainable by any
actual counterexample.

## 2. What it does not give

Covering needs strict overlap: `(8m_j−1)/s_j < x_{j−1}`, i.e. `s_j = (8m_j−1)(1+η)/x_{j−1}` for some
`η > 0`. Then

```
        x_j  =  x_{j−1} · (8m_j+1) / ((8m_j−1)(1+η))
```

so the multiplier is **strictly** below `(8m+1)/(8m−1)` — but `η` may be arbitrarily small.
**There is no quantitative gap**, so this sharpens the bound from `≤` to `<` and no further.

The obstruction is real and is not yet a bound. To become one it needs a lower bound on `η`,
i.e. a reason the overlaps cannot all be arbitrarily thin — which would have to come from the
**reuse** of combs, since six combs must supply ≥ 18 intervals to cover `[1,15]`.

### 2.1 The reuse constraint, for the record

If comb `i` is used at levels `m` then `m'`, its first use ends at `(8m+1)/s_i` and its second begins
at `(8m'−1)/s_i`. Between them the reach must grow by `(8m'−1)/(8m+1)`, supplied entirely by the
**other five** combs. At consecutive levels `m' = m+1` and `m = 1` that factor is `15/9 = 1.667`,
against `(9/7)^5 = 3.51` available. Feasible, so no contradiction — recorded as checked, not as a
lead that worked.

## 3. A reporting defect of mine, corrected

`R_twelve_v1.py` printed its maximiser's profile **rounded to four decimals**, and the rounded
profile gives `R = 6.318934`, not `11.965675`. More decimals do not recover it: `R` is cell-wise
constant and the maximiser's cell is narrow, so rounding leaves the cell. **The `11.965675` figure
has no exact witness.**

The maxima that *do* have verified integer witnesses, recomputed from scratch:

```
    [2520, 5750, 8003, 10557, 13161, 14580, 18745]   R = 44856/3749 = 11.964791
    [158, 367, 505, 664, 827, 918, 1179]             R = 14062/1179 = 11.927057
    [46, 107, 146, 194, 241, 268, 344]               R =   1127/97  = 11.618557
```

**The largest `R` with a reproducible witness is `44856/3749 = 11.964791`.** Wherever
`11.965675` appears it should be read as a float-search figure without a witness; the conclusions
that used it (`R` never reaches 12; band 2 unreached) are unaffected, since `11.964791 < 12` equally.

Lesson: a maximiser is not reported until it is rationalised and re-verified. `R_search_v1.py` did
this correctly and `R_twelve_v1.py` did not.

## 4. Status

| | |
|---|---|
| the max-reach profile is forced, and geometric with ratio `9/7` | **derived**, matches the LP exactly |
| its touch points are clear, so `R = 9/S` | **`[VERIFIED — exact rationals]`**, every case |
| maximising reach and covering are in tension | **established** |
| this yields a quantitative bound | **no** — `η` may be arbitrarily small |
| largest `R` with an exact witness | `44856/3749 = 11.964791` |

```bash
python3 experiments/n8/forced_profile_v1.py   # the forced profile and its R
python3 experiments/n8/touchpoint_v1.py       # R = 9/S exactly; the rounding sensitivity
```
