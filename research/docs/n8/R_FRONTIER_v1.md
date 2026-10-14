# How far we got on `R`: a closed form, a proved band structure, and a frontier at `S ≈ 7.45`

---

## 1. `R` has a closed form that does not mention the cascade — `[PROVED]` + 10,677/10,677

At the final scale every reading is `s_i·R` (with `s_i = d_i/d_min`), so clearance is
`s_i·R mod 8 ∈ [1,7]` for all `i`. The cascade walks forward from `R = 1`, hence

> **`R_final = min{ R ≥ 1 : ∀i, s_i·R mod 8 ∈ [1,7] }`**

Verified against the cascade on **10,677 / 10,677** subjects and exact on every known deep case. The
cascade is an *algorithm* for this minimum; the minimum is the object.

**Consequence:** `R` is computable from the profile alone, ~1000× faster than iterating the cascade.
Everything below rests on that.

## 2. `R` is confined to bands — `[PROVED]`

`R/8 = d_min·t*` is `d_min`'s own lap coordinate, so `R mod 8 ∈ [1,7]`
(`RBand.R_avoids_bad_bands`, axiom-clean, general `n`). 148,892 cascades, zero violations. `⌊R/8⌋`
counts `d_min`'s complete laps.

Since `s₁ = 1`, `d_min`'s bad set covers only `(7,9)` and `(15,17)`. So **band 2 requires the other
six disparities to cover `[1,7] ∪ [9,15]` entirely** — 12 units, six combs of density `1/4` each,
18 units of bad measure available. Feasible by measure; the question is whether the combs interlock.

## 3. The search, at scale

```
   6,150,899 profile evaluations (4,000 restarts)   → max R = 11.964897
   6,022,983 more, seeded at the maximiser          → max R = 11.965675
```

**12.2 million evaluations. `R` never reaches 12, let alone band 2's 17.** This converges on the
`11.96` already recorded on this project by other means.

## 4. Why it stops there — the frontier

At the maximiser exactly one constraint binds:

```
   s₇ · R  =  89  =  8·11 + 1      exactly — the largest reading on a band's lower edge
```

so `R = 89/s₇ = 89/S`, giving the ceiling `R < 89/7 = 12.714` as `S → 7`. But `S ≤ 7` clears
immediately (`clear_of_reading_le_seven`), so the ceiling cannot be approached. Mapping the tension —
max `R` at each fixed `S`:

```
       S      max R      89/S     attained?
   7.020    10.84134   12.6781    no  — the other six cannot dodge that long
   7.200    10.56952   12.3611    no
   7.400    10.53050   12.0270    no
   7.450    11.94631   11.9463    YES
   7.500    11.86667   11.8667    YES
   7.700    11.55844   11.5584    YES
   7.950    11.19497   11.1950    YES
```

Two regimes meeting at `S ≈ 7.45`:

* **`S ≥ 7.45`** — the `89/S` ceiling is *attained*; `R` decreases as `S` grows.
* **`S < 7.45`** — the ceiling rises but is *not reachable*: the six remaining readings cannot
  collectively dodge their bad bands long enough to get there.

**The maximum of `R` is where the two curves cross: `S ≈ 7.45`, `R ≈ 11.95`.**

### 4.1 This explains the deep cases

Every deep case found all session sits at `S ≈ 7.45–7.48` — the 23-move at 7.467, the 28-move at
7.469, the two 27s at 7.618 and 7.857, the `R`-maximisers at 7.462 and 7.478. **They are sitting on
the frontier**, and that is why `S` re-pinned to 7.46–7.48 under every rescaling and every seeded
climb. It was not a coincidence to be noted; it is the optimum.

## 5. How far this gets, honestly

**Established.** `R`'s closed form; the band theorem; that band 2 requires covering 12 units with
six combs; that `R` is maximised near `S = 7.45` by the `89/S` constraint; and the mechanism for
why smaller `S` cannot reach its own higher ceiling.

**Not established.** `R < 12`. That is 12.2 million evaluations with no counterexample, not a proof
— and the binding constraint being `(8k+1)/S` with `k = 11` is itself empirical. A proof would need
a bound on how long six readings can collectively dodge, which is the covering question of §2 and is
the open problem.

**What would settle band 2.** A single profile whose six non-minimal readings cover `[1,7] ∪ [9,15]`
completely. §2 says the measure is there (18 against 12); §4 says the searches cannot find the
interlocking. Those are not in conflict — the union bound was never the obstruction.

```bash
python3 experiments/n8/R_direct_v1.py     # the closed form, 10,677/10,677
python3 experiments/n8/R_search_v1.py     # 6.15M evaluations, max 11.9649
python3 experiments/n8/R_twelve_v1.py     # 6.02M more; the s₇·R = 89 binding constraint
python3 experiments/n8/R_frontier_v1.py   # max R against S; the crossing at 7.45
```
