# First individual isolation time of every runner, by BSM, across one runner's transit

2026-09-12. Script `experiments/n8/ok_first_iso_time_v1.py`. Exact `Fraction`, Boundary Set
Method throughout. Eight genuine runners; nothing adjoined.

`V = (s, 2,3,4,5,6,7,8)`, `s` permuting from 1 up to 2. Times in **original** units
(cleared time × period).

---

## 1. The table  `[VERIFIED — exact, BSM]`

| `s` | period | r1 | r2 | r3 … r8 |
|---|---|---|---|---|
| **1** (AP) | 1 | **1/8** | **1/8** | **1/8** |
| 13/12 | 12 | 75/166 | 3/22 | 1/8 |
| 7/6 | 6 | 75/164 | 9/32 | 1/8 |
| 5/4 | 4 | 17/54 | 9/32 | 1/8 |
| 4/3 | 3 | 51/160 | 9/32 | 1/8 |
| 3/2 | 2 | 1/4 | 9/32 | 1/8 |
| 5/3 | 3 | 75/152 | 3/8 | 1/8 |
| 7/4 | 4 | 1/2 | 9/16 | 1/8 |
| 11/6 | 6 | 3/4 | 41/48 | 1/8 |
| 23/12 | 12 | 3/2 | 25/16 | 1/8 |

> **`r3` through `r8` never leave `t = 1/8`.** Not at any `s`, and not at any separation —
> checked down to `δ = |2−s| = 1/64`, where r1 and r2 have receded to `t = 8` and `t = 65/8`.

Only the moving runner and the one it approaches have their isolation times displaced.

## 2. The divergence  `[VERIFIED — exact]`

| `δ = \|2−s\|` | 1/2 | 1/4 | 1/8 | 1/16 | 1/32 | 1/64 |
|---|---|---|---|---|---|---|
| r1 first | 1/4 | 1/2 | 1 | 2 | 4 | **8** |
| `r1 × δ` | .1250 | .1250 | .1250 | .1250 | .1250 | **.1250** |
| r2 first | 9/32 | 9/16 | 9/8 | 17/8 | 33/8 | 65/8 |
| `r2 × δ` | .1406 | .1406 | .1406 | .1328 | .1289 | **.1270** |

Both diverge as `1/δ`. `r1 × δ` is **exactly `1/8`**; `r2 × δ` approaches `1/8` from above.

## 3. The exactness is a parity condition  `[PROVED + VERIFIED]`

> **`r1`'s first isolation time is exactly `1/(8δ)` iff `δ = 1/D` with `D` even.**

*Why.* r1's constraints are `δ, 1+δ, …, 6+δ`. At `t = D/8 = 1/(8δ)` the constraint against r2
is `δt = 1/8` exactly — admissible. The others are `(k+δ)t = kD/8 + 1/8`, and such a
constraint fails only if it lands on an integer, i.e. `kD ≡ −1 ≡ 7 (mod 8)`. That needs `kD`
**odd**, hence `D` odd. For `D` even it is impossible, so `t = D/8` is already a witness. ∎

Verified: exact at `δ = 1/2, 1/4, 1/6, 1/8, 1/10, 1/12`; strictly later at
`δ = 1/3, 1/5, 1/7` and at the non-unit fractions `2/5, 3/7, 5/12`. Worked failure at
`D = 3`, `t = 3/8`: `k = 5` gives `5·3/8 + 1/8 = 2` exactly, distance `0`.

## 4. Two measurements that answer different questions  `[recorded]`

`WITNESS_DRIFT_v1` §1 reported r2's drift from the grid as `0` throughout — its isolation
*set* touches a grid time. This file reports r2's *first* isolation time, which is often
**earlier** and not at a grid time at all: at `s = 23/12`, `WITNESS_DRIFT_v1` finds the grid
witness at `a = 13` (`t = 13/8`) while the first witness is `25/16 < 13/8`. Both are correct;
"does a grid time work" and "when does isolation first occur" are different questions and were
reported as if interchangeable.

## 5. Ledger

`[VERIFIED — exact, BSM]` §1's table; §2's divergence rows.
`[PROVED]` §3's parity criterion, with derivation; `[VERIFIED]` across twelve values of `δ`.
`[recorded]` §4, the distinction between grid-witness existence and first-witness time.
`[SCOPE]` one base (the AP) and one transit (`r1: 1 → 2`). §3's derivation uses only that
r1's other constraints are `k+δ` with `k = 1..6`, so it transfers to any runner whose integer
differences are `1..n−2`.

`n = 8` is **not proved.**
