# How often each runner isolates before the grand return, and across all eight transits

2026-09-12. Scripts `experiments/n8/ok_iso_count_v1.py`, `ok_all_transits_v1.py`.
Exact `Fraction`, BSM good sets, eight genuine runners.

The **grand return** — every runner simultaneously back at the start — happens at `t = 1` for
integer speeds with `gcd = 1`, and at `t = q` for rational speeds cleared to integers with
period `q`. Isolation must occur before then for every runner, or LRC(8) has a counterexample.

---

## 1. At the AP  `[VERIFIED — exact]`

Isolation **events** (maximal intervals of the good set) per runner over one period:

| r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 |
|---|---|---|---|---|---|---|---|
| **4** | 8 | 8 | 6 | 6 | 8 | 8 | **4** |

The extremal runners have exactly **`φ(8) = 4`** — confirming the GECT audit §7.2's
`ν = φ(n)` for the extremal runner. The row is palindromic, as reflection invariance requires.

## 2. The rate is the invariant  `[VERIFIED — exact]`

Raw counts are not comparable across a transit because the period changes with the
denominator of `s`. The scale-free quantity is **events per unit time** = count / period.

`V = (s,2,…,8)`:

| `s` | 1 | 13/12 | 5/4 | 3/2 | 7/4 | 15/8 | 31/16 | 63/32 |
|---|---|---|---|---|---|---|---|---|
| **r1** | **4.00** | 2.92 | 2.75 | 4.50 | 2.25 | 2.38 | 2.19 | 2.22 |
| r2 | 8.00 | 6.17 | 6.00 | 7.00 | 6.00 | **6.00** | **6.00** | **6.00** |
| others | 4–8 | 4.8–6.8 | 4.5–7 | 4–7 | 4.5–6.5 | 4.3–6.8 | 4.4–6.8 | 4.4–6.7 |

- **`r1`'s rate halves** on leaving the AP — `4.00 → ~2.2` — and then stays there, **bounded
  away from zero** down to `δ = |2−s| = 1/64` (139 events over a period of 64).
- **`r2` locks at exactly `6.000`** per unit time at every separation tested.
- The count grows in step with the period; nothing is lost, the events simply spread out.

## 3. All eight transits  `[VERIFIED — exact]`

Each runner swept between its neighbours; `r8` swept on to the **next global-isolation point**
(`V = (1,…,7,x)` has complete residues mod 8 iff `x ≡ 0`, so `x: 8 → 16`).

| runner | range | min rate | at | binding runner |
|---|---|---|---|---|
| r1 | 1 → 2 | 2.208 | 43/24 | **r1** |
| r2 | 1 → 3 | **2** | 8/3 | **r2** |
| r3 | 2 → 4 | **2** | 7/3 | **r3** |
| r4 | 3 → 5 | **2** | 10/3 | **r4** |
| r5 | 4 → 6 | **2** | 13/3 | **r5** |
| r6 | 5 → 7 | **2** | 16/3 | **r6** |
| r7 | 6 → 8 | **2** | 19/3 | **r7** |
| r8 | 7 → 16 | 2.750 | 31/4 | **r8** |

Two exact facts:

> **In every transit the binding runner is the one that is moving** — never a bystander.
>
> **For all six interior runners the minimum rate is exactly `2`**, realised identically as
> **6 events over a period of 3**. Counts at those points, e.g. `r4` at `s = 10/3`:
> `[14, 20, 20, 6, 16, 20, 20, 14]` — the moving runner alone drops to 6.

**No rate is ever zero** anywhere in the eight sweeps, which is the control: a zero would be an
LRC(8) counterexample.

## 4. Reading

Moving a runner off its grid point costs **that runner** roughly half its isolation rate — from
`φ(8) = 4` down to `2` — and costs the others nothing that brings them near zero. The cost is
paid entirely by the mover, it is bounded, and it does not deepen as the runner approaches its
neighbour: at `δ = 1/64` the rate is still `2.17`, essentially the same as at `δ = 1/4`.

## 5. Ledger

`[VERIFIED — exact]` §1's counts; §2's rate table and the `δ → 0` rows; §3's eight sweeps,
24 sample points each, with the exact-`2` minima confirmed by direct count (6 events, period 3).
`[SCOPE]` one base (the AP `1,…,8`); sweeps are sampled at 24 points, so a minimum between
sample points could be lower. §3's "binding runner is the mover" holds at every sampled point
but is not proved.

`n = 8` is **not proved.**
