# Working note — dense transit minima, and the r8 sweep between global-isolation points

2026-09-12. Script `experiments/n8/ok_dense_sweeps_v1.py`. Exact `Fraction`, BSM good sets,
eight genuine runners, base `V = (1,…,8)`. Metric throughout: isolation events per unit time
(count of maximal good-set components / period).

Working note. Records data and one correction; nothing is concluded.

---

## 1. Correction to `ISOLATION_COUNT_v1` §3

That file sampled each transit at 24 uniform points. Uniform sampling is wrong here: the rate
depends on the **denominator** of `s`, which sets the period, so a uniform grid systematically
omits high-denominator points. Re-sampled over every `s = a/b` in range with `b ≤ 14`:

| runner | range | points | min rate | at | binder | previously reported |
|---|---|---|---|---|---|---|
| r1 | 1→2 | 64 | **2** | 9/5 | r1 | 2.208 at 43/24 |
| r2 | 1→3 | 127 | 2 | 8/3 | r2 | 2.000 |
| r3 | 2→4 | 127 | 2 | 7/3 | r3 | 2.000 |
| r4 | 3→5 | 127 | 2 | 10/3 | r4 | 2.000 |
| r5 | 4→6 | 127 | 2 | 13/3 | r5 | 2.000 |
| r6 | 5→7 | 127 | 2 | 16/3 | r6 | 2.000 |
| r7 | 6→8 | 127 | 2 | 19/3 | r7 | 2.000 |
| r8 | 7→16 | 576 | **2** | 9 | r8 | 2.750 at 31/4 |

Two of the eight minima were too high. Corrected: **all eight transits bottom at exactly 2**,
binder always the moving runner.

Stability under refinement — nothing below 2 appears:

| | `b ≤ 14` | `b ≤ 20` | `b ≤ 26` |
|---|---|---|---|
| r1 | 2 at 9/5 (64 pts) | 2 at 9/5 (128) | 2 at 9/5 (212) |
| r8 | 2 at 9 (576 pts) | 2 at 9 (1152) | 2 at 9 (1908) |

## 2. r8 swept between consecutive global-isolation points

`V = (1,…,7,x)`. Residues mod 8 are complete iff `x ≡ 0 (mod 8)`, so the global-isolation
points in range are `x = 8` and `x = 16`.

| `x` | period | global | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | min |
|---|---|---|---|---|---|---|---|---|---|---|---|
| **8** | 1 | **yes** | 4 | 8 | 8 | 6 | 6 | 8 | 8 | 4 | **4** |
| 9 | 1 | | 6 | 6 | 8 | 8 | 6 | 8 | 8 | **2** | **2** |
| 17/2 | 2 | | 7 | 8 | 6 | 5 | 5 | 6 | 6 | 5.5 | 5 |
| 10 | 1 | | 8 | 6 | 6 | 6 | 8 | 8 | 8 | 4 | 4 |
| 19/2 | 2 | | 7 | 8 | 7 | 5 | 6 | 5 | 6 | 6.5 | 5 |
| 11 | 1 | | 8 | 8 | 6 | 6 | 8 | 8 | 8 | 8 | 6 |
| 21/2 | 2 | | 7 | 7 | 8 | 6 | 6 | 7 | 5 | 5.5 | 5 |
| 12 | 1 | | 8 | 8 | 6 | 6 | 6 | 8 | 8 | 6 | 6 |
| 23/2 | 2 | | 5 | 8 | 7 | 7 | 7 | 6 | 7 | 5.5 | 5 |
| 13 | 1 | | 8 | 8 | 10 | 6 | 6 | 6 | 8 | 6 | 6 |
| 25/2 | 2 | | 7 | 6 | 8 | 7 | 8 | 8 | 6 | 8.5 | 6 |
| 14 | 1 | | 8 | 8 | 8 | 8 | 6 | 6 | **4** | 8 | 4 |
| 27/2 | 2 | | 8 | 7 | 7 | 8 | 7 | 8 | 7 | 10.5 | 7 |
| 15 | 1 | | 6 | 10 | 10 | 8 | 10 | 8 | 6 | 8 | 6 |
| 29/2 | 2 | | 7 | 9 | 8 | 7 | 8 | 7 | 7 | 10.5 | 7 |
| **16** | 1 | **yes** | 10 | 8 | 10 | 10 | 8 | 8 | 8 | **12** | **8** |

Directly readable from the table:

- Minimum over `x = 8..16` integer: `4, 2, 4, 6, 6, 6, 4, 6, 8`.
- The half-integer rows sit at 5–7; the integer rows at 4–6. Every integer row's minimum is at
  or below the neighbouring half-integer rows.
- Lowest point of the sweep is `x = 9`, where r8 alone is at 2 and every other runner is 6–8.
- Second dip at `x = 14`, where r7 is at 4.
- The two global-isolation points differ: at `x = 8`, min 4 with r8 at 4; at `x = 16`, min 8
  with r8 at 12.

## 3. Ledger

`[VERIFIED — exact]` §1's dense minima and the three refinement levels; §2's full table.
`[SUPERSEDED]` `ISOLATION_COUNT_v1` §3's r1 and r8 minima (2.208, 2.750). Its r2–r7 values,
its AP counts `[4,8,8,6,6,8,8,4]`, and its rate tables stand.
`[SCOPE]` one base (`1,…,8`); denominators bounded at 26; `x` sampled at integers and
half-integers only between 8 and 16. "Binder is the mover" holds at every sampled point, not
proved.
`[NOT MEASURED]` whether the `x = 8` / `x = 16` difference persists at further
global-isolation points (`x = 24, 32, …`); whether half-integer rows sit above integer rows
away from this base.

`n = 8` is **not proved.**
