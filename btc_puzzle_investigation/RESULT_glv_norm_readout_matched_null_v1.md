# RESULT — the surviving GLV lane, RUN against a matched null: SCOPED NULL at full-group scale

**Date:** 2026-08-01. **Scripts:** `glv_norm_readout_matched_null_v1.py` (superseded, screen bug),
`glv_norm_readout_matched_null_v2.py`. Integer-only; exact permutation p-values.
**Grade:** `[EMPIRICAL — SCOPED NULL]`, power and scope stated in §4. **The avenue is NOT closed.**

---

## 0. The object (in scope: the CONVERSION, not the selection)

Does a scalar's Eisenstein/GLV lattice footprint couple to the algebraic geometry of the point the
curve maps it to?

- **feature** `N(κ(d)) = k₁² − k₁k₂ + k₂²`, from the GLV lift `d ↦ κ = k₁ + k₂ω`
- **readout** `χ_k(x)` of `[d]G = (x,y)`
- **scalars** the full group at each prime — nothing depends on how any `d` was chosen.

## 1. The screen, corrected

`RESULT_glv_lattice_feature_prescreen_v1.md` established the pairing rule. Two refinements, both
found by controls in v1 of this script:

- **An x-readout is automatically EVEN in `d`.** `[−d]G = (x, −y)` leaves `x` fixed, so any function
  of `x` alone is even regardless of `χ_k(−1)`. v1 screened on `χ_k(−1)` and wrongly marked `χ₂(x)`
  forced at `p ≡ 3 mod 4` — contradicting the earlier script, which measured it moving at exactly
  those primes. **The only binding constraint is `χ_k(β) = 1`** (else the μ₃ orbit-sum annihilates).
- **`C-FORCED` is valid only at `p ≡ 3 mod 4`.** `Σ_d χ₂(y)·N = 0` is forced by `χ₂(y)` being odd,
  which needs `ε = χ₂(−1) = −1`. v1 applied it at `p ≡ 1 mod 4`, where it correctly "failed".
  secp256k1 has `p ≡ 3 mod 4`, so the forced regime is the relevant one.

Under the corrected screen `χ₂(x)` is legal at every prime; `χ₃(x)`, `χ₆(x)` are legal only when
`χ_k(β) = 1`, which is roughly a third of primes.

## 2. Design

`N` and the readout are both constant on the μ₆ orbits `{±d, ±λd, ±λ²d}` (size exactly 6, since
`6 | n−1`). Statistic `S = Σ_classes w·N`. **Matched null:** permute the readout's class-values
among classes — preserves every forced symmetry, destroys only the putative coupling. This is the
class-permutation null of `curve_native_beam_scan_v2`, where a free permutation manufactured a
phantom that the symmetry-preserving null killed on identical data.

## 3. Controls

| control | result |
|---|---|
| `C-FORCED` `Σ_d χ₂(y)·N = 0` wherever `ε = −1` | **exactly 0 at every such prime**, all runs |
| `C-PLANT` power curve, `M = 162` classes | 10% planted → p = 18/4001 **FIRES**; 20/30/50% → 1/4001 |

The instrument moves when a coupling is there, and reads exactly zero where the algebra says it must.

## 4. Result

**Broad run** (36 cells, `p ≤ 541`, `χ₂/χ₃/χ₆`, both `ε`, R = 2000):
4 cells at `p ≤ 0.05` against 1.8 expected (binomial `P(X≥4) ≈ 0.10`), **0 at `p ≤ 0.01`**.

**Powered run in secp's own regime** (16 primes, `ε = −1`, `χ₂(x)`, `p ≤ 967`, `M` up to 162,
R = 4000): **0 of 16 at `p ≤ 0.05`** (0.8 expected). Smallest p-value 261/4001 ≈ 0.065.

> **SCOPED NULL.** No coupling between `N(κ(d))` and `χ₂(x)` at full-group scale.
> **POWER:** detects ≳10% class-level coupling at `M ≈ 162`.
> **SCOPE:** `j=0` curves, `p ≤ 967`, complete sums over the whole group, 3 readouts,
> class-permutation null, exact permutation p-values.

**This also explains the number that prompted the run.** `Σ_d χ₂(x)·N = −192` (p=79) was a *control*
row, built to show the lane is not forced. Raw sums of that size are exactly what two uncoupled class
functions produce — which is what the matched null now measures directly. "S moves" was never
evidence of coupling; it was evidence the instrument was alive, which is what it was for.

## 5. What is NOT closed

The null is about **complete sums over the whole group**. The target regime is different in kind:

- **short dyadic intervals at `2^128`**, where the sum is **incomplete**, no character-sum bound
  applies, and the μ₆ class structure does not tile the interval. The statistic there is not the one
  tested here, and nothing above bounds it.
- larger `p` (power grows with `M ≈ n/6`), finer lattice features than the norm alone (the reduced
  representative's *position*, not just its length), and non-`χ₂` readouts at primes where they are
  legal.

Per the counter-prior: a scoped empirical null bounds a statistic at a scale. It does not close the
channel, and this one is explicitly not offered as doing so.

## 6. Cost note

Pre-screen → matched null → powered run took one session. Two of the three originally proposed
statistics were killed by algebra before any data (`N` vs `χ₂(y)` by parity; `det` by `1+ω+ω²=0`),
and the third was run to a null with a firing plant instead of being argued about.
