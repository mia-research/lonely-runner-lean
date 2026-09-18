# `R` is confined to bands, and the open question sharpens to "is band 2 reachable?"

---

## 1. `R` in closed form

The final scale is `D_final = a·g/(8M+1)` for the last setter `a` at lap `M`, so

```
    R = d_min/D_final = c(8M+1)/a        (reduced units, c = d_min)
```

Verified **10,290 / 10,290**. Since `a ≥ c`, this gives `R ≤ 8M_final + 1` — true (zero violations)
but weak: the bound runs 9 to 137 while `R` stays near 1.1–1.3.

## 2. `R` avoids the bad bands — `[PROVED]`

`R/8 = d_min·t*` is **`d_min`'s own lap coordinate** at the isolation instant. Isolation puts every
disparity at circle distance `≥ 1/8`, and `d_min` is a disparity. Hence

> **`R mod 8 ∈ [1,7]`** — `RBand.R_avoids_bad_bands`, axiom-clean, stated for general `n`

so `R` can never lie in `(7,9)`, `(15,17)`, `(23,25)`, … Measured: **148,892 cascades, zero
violations.**

This retro-explains the "gap" from the depth work: `τ = R/8` jumped from `≤ 0.63` straight to `≈ 1.3`
with nothing between. That interval, `τ ∈ (0.875, 1.125)`, is exactly `R ∈ (7,9)` — a forbidden band,
not a sampling artefact.

## 3. The band structure

`⌊R/8⌋` counts the **complete laps `d_min` makes** before isolation.

```
   band 0   R ∈ [1, 7]     148,892 random cascades — every one
   band 1   R ∈ [9, 15]    0 random; all five known deep cases (10.26 … 11.93)
   band 2   R ∈ [17, 23]   never observed
```

Every known deep case is a band-1 case. **Depth and band are the same phenomenon seen twice**: a deep
cascade is one that pushes `d_min` past its first lap.

## 4. What this does to the open question

`R` bounded ⟺ Existence at order 8 (`existence_of_capped` / `capped_of_existence`). By §2, `R` is
bounded **iff the lap count `⌊R/8⌋` is bounded**. So the question is no longer the open-ended *"is
`R` bounded"* but:

> **Is band 2 reachable? Can the cascade push `d_min` past its second lap?**

That is concrete and falsifiable — one witness with `R ≥ 17` settles it in the negative direction,
and it is a much better-shaped target than a search maximum.

## 5. Current state of the hunt

A dedicated `R`-maximising search (500 restarts × 4,000 steps, three seeding modes):

```
   max R = 11.927057    band 1    [158, 367, 505, 664, 827, 918, 1179]
                        depth 28  S = 7.4620
```

Improving on an earlier `11.618557` at `[46, 107, 146, 194, 241, 268, 344]` (also depth 28,
`S = 7.478`). Two observations:

* **Maximising `R` and maximising depth converge** — every `R`-maximiser found is a depth-28 case
  with `S ≈ 7.46–7.48`, reached without targeting depth at all.
* **`R` saturates near 12, not near 15.** Band 1 runs to 15 but nothing found exceeds 11.93, so the
  upper half of band 1 is as unreached as band 2.

`[EMPIRICAL — conditional]`: band 2 has not been reached by these searches. That is not evidence it
is unreachable — this session's searches have been beaten twice (`M ≤ 7` → 20; the first `R` max
→ 11.93).

## 6. Grades

| | |
|---|---|
| `R = c(8M+1)/a` | `[PROVED]` algebra + 10,290/10,290 |
| `R ≤ 8M_final + 1` | `[PROVED]`, weak |
| `R mod 8 ∈ [1,7]` | **`[PROVED]`**, general `n`, axiom-clean |
| band 0 and 1 occupied, band 2 not | `[EMPIRICAL]`, ~150,000 cascades + directed search |
| `R` bounded ⟺ lap count bounded | follows from the above |
| band 2 unreachable | **not established** |

```bash
cd LonelyRunner && lake env lean ../experiments/n8/RBand_v1.lean
python3 experiments/n8/R_bound_v1.py    # R = c(8M+1)/a; the (R, M) distribution
python3 experiments/n8/R_bands_v1.py    # zero violations in 148,892; band occupancy
python3 experiments/n8/band2_hunt_v1.py # max R = 11.927, band 1
```
