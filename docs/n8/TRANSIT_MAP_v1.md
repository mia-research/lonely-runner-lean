# The transit map — every runner's isolation set, while one runner moves between grid points

2026-09-12. Scripts `experiments/n8/ok_transit_map_v1.py`, `ok_outer_runner_v1.py`.
Exact `Fraction`; good sets by BSM. Owner's construction: increment one runner's speed
continuously toward the next runner's, and map the **individual** isolation set of **every**
runner throughout.

Rational speeds are cleared to integers, so the cleared time variable spans one **full
period** — necessary, because as two runners approach, the period lengthens and the witness
moves far out in real time. `|G_i|` below is the *fraction of the period* on which runner `i`
is individually isolated.

---

## 1. The transit, AP base  `[VERIFIED — exact]`

`V = (s, 2,3,4,5,6,7,8)`, `s` from 1 to 2.

| `s` | period | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | min |
|---|---|---|---|---|---|---|---|---|---|---|
| **1** (the AP) | 1 | **0** | .0875 | .1458 | .3333 | .3333 | .1458 | .0875 | **0** | **0** |
| 13/12 | 12 | .1320 | .0656 | .1094 | .2500 | .3438 | .2500 | .1094 | .0656 | .0656 |
| 3/2 | 2 | .1136 | .0667 | .1354 | .2021 | .3185 | .2743 | .1138 | .0731 | .0667 |
| 19/12 | 12 | .1317 | .0656 | .1094 | .2500 | .3438 | .2500 | .1094 | .0656 | .0656 |
| 23/12 | 12 | .1344 | .0656 | .1094 | .2500 | .3438 | .2500 | .1094 | .0656 | .0656 |

Three things:

- **At the AP the two extreme runners are tight** (`|G| = 0` — isolated only at isolated
  points), while the interior runners sit at `.0875` to `.3333`. The extremes carry all the
  difficulty, as `RESIDUAL_NO_STATIONARY_v1` predicts.
- **Any step off the AP jumps every runner clear.** `r1` goes `0 → ~0.13` immediately.
- **Across the whole transit the minimum is flat:** mean `0.0653`, min `0.0613`, max `0.0667`,
  **spread `0.0054`**. And the binding runner is `r2` (or `r8`) throughout — **never the
  runner that is moving**.

**Near-collision is benign.** At `s = 2 − 1/1000` the period is 1000 and `r1`, `r2` nearly
coincide, yet `min|G| = 0.06563`, `r1 = 0.13031`, `r2 = 0.06563` — unchanged. The period
lengthens and the witnesses move out in real time; the *fractions* do not move.

## 2. The spikes are at the grid points  `[VERIFIED — exact]`

Base `(2,6,7,8,10,13,14,16)`, runner 1 transiting `2 → 6` and therefore crossing the grid
points `3, 4, 5`:

| `s` | 2 | 5/2 | **3** | 7/2 | **4** | 9/2 | **5** | 11/2 |
|---|---|---|---|---|---|---|---|---|
| `min\|G\|` | **.0509** | .0937 | **.0661** | .1047 | **.0229** | .0937 | **.0859** | .1032 |

Between the grid points, 36 samples: mean `0.0984`, spread `0.0110`. **At** the grid points:
`0.0509, 0.0661, 0.0229, 0.0859` — two to four times worse, with the global worst (`0.0229`)
sitting exactly on `s = 4`.

> **The map is flat between grid points and spikes at them.**

## 3. Moving outward: the spikes damp  `[VERIFIED — exact]`

`V = (1,…,7,x)`, consecutive unit steps of `x`:

| `x` range | mean `\|Δ min\|G\|\|` per step | `x·mean\|Δ\|` |
|---|---|---|
| `[8,40]` | 0.017555 | 0.42 |
| `[40,80]` | 0.005786 | 0.35 |
| `[100,140]` | 0.002470 | 0.30 |
| `[300,340]` | 0.000887 | 0.284 |
| `[1000,1040]` | **0.000281** | **0.287** |

**Impact per grid step decays as `≈ 0.285/x`.** The level converges: mean `min|G|` goes
`0.0520 → 0.0636 → 0.0651 → 0.0654`, spread collapsing to `0.001`. And `min|G| = 0` — a tight
instance — occurs only at `x = 8` and `x = 14`; never beyond `x = 40`.

## 4. What the three results say together

The difficulty of LRC(8) is **concentrated at the grid points** — the integer configurations —
and **nowhere else**. Between grid points the map is flat and comfortable (`~0.098` in §2,
`~0.065` in §1). At grid points it spikes, by a factor of 2–4. And as a runner moves outward
through successive grid points the spikes damp like `1/x`, with the tight instances confined
to the AP's immediate neighbourhood.

This is why the hard case of LRC is exactly the rationally-dependent one: **the integers are
the grid points.**

## 5. A mis-attribution of mine  `[recorded]`

An earlier pass reported the transit spread as tracking *transit length* — 0.0054 for a
one-step transit versus 0.0818 for a four-step one. Wrong. The difference was whether my
sample points **landed on integers**: the four-step sweep used step `1/10` and hit `s = 3,4,5`,
while the comparison sweep used denominator 41 and never touched a grid point. Re-run with the
grid points separated out, transit length is irrelevant (spreads `0.00164, 0.00166, 0.00168,
0.00161` for 1, 2, 4, 8 steps) and grid-point alignment is everything. The real finding is §2,
and it is stronger than the one I first reported.

## 6. Ledger

`[VERIFIED — exact]` §1's transit table and the near-collision rows; §2's grid-point versus
interior comparison; §3's decay and convergence tables.
`[recorded]` §5.
`[SCOPE]` §1 is one base (the AP), §2 one base, §3 one family `(1,…,7,x)`. The pattern is
consistent across the four bases tested but is not established in general.
`[NULL]` separately: residual runners' single orbits are **not** the tight instances — only
0.56% of residual witnesses hit exactly `1/8` (`PERMUTATION_MAP_v1` §3 gives the orbit counts;
the tightness mapping fails).

`n = 8` is **not proved.**
