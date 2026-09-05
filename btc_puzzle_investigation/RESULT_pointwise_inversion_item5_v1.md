> ## ⚠ NOTE (same day): the DEEP-RUN extension of this result was VOIDED and re-done.
> The `M = 6.25×10⁶` k=128 adjudication was voided under `VOID_item5_k128_adjudication_v1.md`
> (a pre-registered `C-NULLSD` failure that I overrode post-hoc). The deep-run bound now rests on the
> **k=135** arm adjudicated under `PREREG_item5_deep_inversion_v2.md`: `z = −0.141`, floor ≈0.13%.
> The `M = 20000` results in this file are unaffected.

# RESULT — ITEM 5: the pointwise inversion statistic at 2^128, measured for the first time. A ~2% BOUND.

**Date:** 2026-08-01. **Script:** `pointwise_inversion_2p128_item5_v1.py`.
**Grade:** `[EMPIRICAL — BOUND, power measured]`. **Not a null; the channel is not closed.**

## 0. The object and why it matters

`S = Σ_i χ₂(x_{[d_i]G})·χ₂(x_{[d_i⁻¹]G})`, `d_i` drawn from `[2^{k−1}, 2^k)`.

`d ↦ d⁻¹` is **the non-algebraic index map that survives the Weil closure**
(`STRUCTURAL_IMPLICATIONS` §5.3) — the record's own named residual. It had been settled only at
`p ~ 10⁴` on the full group. **This is its first measurement at the puzzle's native scale.**

## 1. Structural constraints interrogated BEFORE measuring

- **Parity:** `x(−d) = x(d)` makes `a` even; `(−d)⁻¹ = −(d⁻¹)` makes `b` even. The summand is even —
  pairing `d ↔ −d` gives `2×`, **not** 0. Not annihilated.
- **μ₃:** `χ₂(β) = 1` so `a` is μ₃-invariant, and `(λd)⁻¹ = λ²d⁻¹` so `b` is too. The summand is a
  μ₆-class function; on a sampled set that only bites through class collisions — **checked (C-DUP),
  not assumed. 0 collisions.**
- **⚠ The involution has FORCED FIXED POINTS.** `S` is symmetric under `d ↔ d⁻¹`, and wherever
  `d = ±d⁻¹` (i.e. `d² = ±1`) the summand is `r(d)² = +1` **regardless of the data** — a constant
  shared by data and null, carrying zero information and diluting the statistic.
  **Counted and excluded (C-FIX); 0 occurred in random samples.**
- The Gram/singular-value blindness theorem does **not** apply — this is not a Gram spectrum.

## 2. Instrument — every control measures both sides

| control | result |
|---|---|
| C-BALANCE (marginal of `a` **and** `b`) | balanced, e.g. 9841/10159 and 10140/9860 |
| C-DUP (μ₆ class collisions) | **0** at every arm |
| C-FIX (forced involution fixed points) | **0**, excluded by construction |
| **C-NULLSD** (null sd vs theory `√M`) | **141.07 vs 141.42, ratio 0.998** (range 0.975–1.025) |
| C-PLANT (dilution) | floor measured: **2–5% planted** |

`C-NULLSD` is the check that would have caught item 4's `√2` fault. The null here is correctly
scaled on every arm.

## 3. Result

`M = 20000`, `R = 2000`:

| arm | S | z | perm p |
|---|---|---|---|
| k = 128 | −154 | −1.09 | 0.27 |
| k = 135 | +52 | +0.36 | 0.73 |
| **k = 160** | **+416** | **+2.95** | **0.003 — FIRED** |
| full-range control | −46 | −0.33 | 0.76 |

**The k=160 hit died out of sample.** Pre-committed statistic and direction, five fresh seeds:

| seed | S | z | fires |
|---|---|---|---|
| 11111 | −156 | −1.08 | no |
| 22222 | +70 | +0.51 | no |
| 33333 | −36 | −0.25 | no |
| 44444 | +52 | +0.37 | no |
| 55555 | +44 | +0.31 | no |

**mean z = −0.028, pooled z = −0.063, 3/5 signs, 0/5 fire.** Dead — the 9th chance pattern killed by
the pre-committed OOS rule on this project.

## 4. What is established — a bound, stated as one

The planted-fraction threshold is `f > 2.5/√M`; at `M = 20000` that is ≈1.8%, matching the observed
2–5% dilution boundary.

> **At `M = 20000`, `k ∈ {128, 135, 160}`: any pointwise correlation between `χ₂(x_{[d]G})` and
> `χ₂(x_{[d⁻¹]G})` exceeding ≈2% is excluded.**

That is a genuine, quantified constraint on the record's own named residual at its native scale, and
far tighter than the interval-channel tests. **It is a bound, not an absence** — a correlation below
2% is untouched, and whether a real inversion-channel leak would exceed 2% is unknown.

**The floor scales as `1/√M`:** reaching 0.1% needs `M ≈ 6.25×10⁶` (~12.5M scalar multiplications,
a few hours). That is the concrete route to tightening this, and it is cheap in analyst time.

## 5. Scope

secp256k1, `χ₂` of the x-coordinate only, `M = 20000` per arm, `R = 2000` permutations,
`k ∈ {128,135,160}` plus a full-range control, one readout. Untouched: `χ₃`/`χ₆` readouts, `d ↦ d^k`
for `k ≡ ±1 mod 6` other than `−1`, other bit-lengths, and any correlation below the 2% floor.
