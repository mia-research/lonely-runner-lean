# The cause of depth: the cascade self-slows, and `R` saturates

---

## 1. The step law, and a proved bound

At scale `D` a blocking disparity has reading `s` with `|s − 8M| < 1`, and `move_lap` gives
`D' = D·s/(8M+1)`. So

```
    λ = D/D' = (8M+1)/s,      8M − 1 < s < 8M + 1
```

Hence `λ < (8M+1)/(8M−1)`, decreasing in `M`, maximal at `M = 1`:

> **`λ < 9/7`** — `DilationBound.dilation_lt_nine_sevenths`, axiom-clean, and `λ < 17/15` once
> `M ≥ 2`.

`M ≥ 1` because `d_min` never blocks at its own scale (`dmin_always_clear`). Measured: **45,199
steps, zero with `λ ≥ 9/7`**, maximum `1.284105` against `9/7 = 1.285714`, attained at `M = 1`.

**Consequence:** `R = ∏λⱼ < (9/7)^K`, so `K > log R / log(9/7)` — a *lower* bound on depth. There is
no matching upper bound, because `λ → 1` as `M → ∞`. **Steps can be arbitrarily unproductive, which
is precisely why a depth ceiling does not follow from the step structure.**

## 2. The mechanism: the cascade self-slows

`M` rises along every deep cascade — first half against second half:

```
   23-move:  M  1.73 → 3.58     λ  1.1483 → 1.0752
   28-move:  M  2.07 → 4.57     λ  1.1204 → 1.0577
   27:       M  1.85 → 4.07     λ  1.1264 → 1.0633
```

The reason is structural: as the scale contracts, **every reading inflates**, so blockers are caught
at higher lap index, and `λ = (8M+1)/(8M+δ) → 1`. The cascade's own progress is what slows it.

This also corrects a guess of mine. I predicted slow steps would have `δ` near `+1` (a setter just
leaving the band). **Wrong** — `δ` is near `−0.5` throughout, and *more* negative in deep cascades
(−0.44, −0.50, −0.40 against −0.18 for depth 1–3). The driver is `M`, not `δ`.

## 3. `R` saturates while depth grows

With `τ = d_min·t* = R/8`, and the depth band 10–28 filled by perturbing the known cases:

```
   depth    10    14    18    20    23    25    27    28
   mean τ  0.494 0.604 0.789 0.682 1.154 1.277 1.331 1.284
   1.11^K/8 0.355 0.539 0.818 1.008 1.378 1.698 2.092 2.322
```

`τ` is **continuous across the band** — the apparent gap between shallow (`τ ≤ 0.63`) and the deep
cases (`τ ≈ 1.3`) was simply the missing depths 17–22 in the earlier sample. `τ ≥ 1` first occurs at
**depth 18**, not only at the deepest.

And `τ` **saturates near 1.28–1.34 from depth 23 on**, while the naive exponential keeps climbing.
So across the four deep cases:

```
   depth 23 → R = 10.31     depth 27 → R = 10.58, 10.87     depth 28 → R = 10.26
```

**`R` is nearly the same while depth varies by five.** Deeper cascades take *more steps to reach the
same total contraction* — which is the self-slowing of §2, measured from the other side.

The identity is exact: `depth = log R / log λ_geom`. With `R ≈ 10.5`, that predicts
`λ = 10.5^(1/23) = 1.1073` and `10.5^(1/28) = 1.0873`, against measured `1.1068` and `1.0890`.

## 4. So: the cause of depth

> Depth is set by **how slowly the cascade contracts**, not by how far it has to go. `R` is pinned
> near 10.5 for deep cases; what varies is the number of steps taken to reach it, and that is
> governed by the lap indices `M` encountered — which rise as the cascade's own progress inflates
> every reading.

A deep case is one where the self-slowing sets in *before* clearance is reached.

## 5. What is bounded and what is not

| | |
|---|---|
| `λ < 9/7` per step | **`[PROVED]`** |
| `λ < 17/15` once `M ≥ 2` | **`[PROVED]`** |
| `K > log R / log(9/7)` | **`[PROVED]`** (lower bound on depth) |
| `M` rises along deep cascades | `[EMPIRICAL]`, all four cases |
| `R ≲ 11.1` over ~150,000 cascades | `[EMPIRICAL]` — *this is the open question*, since `R` bounded ⟺ Existence |
| `K ≤ 28` | **not established** — see `CEILING_CLAIM_v1` |

The honest shape: the *step* is bounded above (`9/7`) and not below, so nothing in the step law
prevents arbitrarily many steps. The empirical saturation of `R` is the whole content of the open
problem, now visible as a saturation rather than as a bare search maximum.

```bash
cd LonelyRunner && lake env lean ../experiments/n8/DilationBound_v1.lean
python3 experiments/n8/step_anatomy_v1.py    # (M, δ, λ) deep vs shallow
python3 experiments/n8/self_slowing_v1.py    # M rises; λ < 9/7 in 45,199 steps
python3 experiments/n8/tau_gap_v2.py         # the 10-28 band filled; τ saturates
```
