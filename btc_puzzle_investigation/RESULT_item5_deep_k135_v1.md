# RESULT — Item 5 deep run, arm k=135 (clean): no detection, floor ≈0.13%

**Date:** 2026-08-01. **Spec:** `PREREG_item5_deep_inversion_v2.md` (frozen before this arm was read).
**Grade:** `[EMPIRICAL — BOUND, power measured]`. **Not a null.**
**Gate:** `experiment-designer` **OWED**; no grade promotion until it clears.

## 0. Why this arm and not k=128

`VOID_item5_k128_adjudication_v1.md`: the k=128 adjudication fired the pre-registered `C-NULLSD`
failure condition (3.15% > 2%) and I overrode it post-hoc. **That adjudication is void, and k=128 is
now contaminated** — the outcome was known before the corrected control was specified. k=135 was
unread when v2 was written and is therefore the arm that can carry a result.

## 1. Controls (v2)

| control | result |
|---|---|
| C-FIX (forced involution fixed points) | **0**, excluded |
| C-DUP (μ₆ class collisions) | **0** |
| C-BALANCE | `a`: 3124327/3125673, `b`: 3126858/3123142 |
| **C-NULLSD — R = 50 000 shuffles, precision ±0.32%** | analytic 632.45 vs empirical 633.91, **ratio 1.0023, deviation 0.23% — PASS**, well inside threshold |
| C-PLANT dilution | fires at 0.15%, not at 0.10% |

The corrected control has ~6σ of headroom against its own threshold, which v1's 500-shuffle version
did not. It also confirms the analytic permutation-moment formula is exact — established **in the
spec, before reading**, which is where that argument belonged all along.

## 2. Result

`M = 6 250 000`, `d ∈ [2^134, 2^135)`:

> `S = −354`, null mean `−0.800`, sd `2500.000` ⇒ **`z = −0.141`**.
> FIRE (`|z| ≥ 3.0`): **no**. CLAIM (`|z| ≥ 3.4`): **no**.

**Measured floor ≈0.13%** (z = +3.60 at 0.15% planted, +2.41 at 0.10%), against the pre-registered
prediction of 0.10% — within the factor-2 the spec allowed, so the `1/√M` scaling model holds.

## 3. What is established

> **At `M = 6.25×10⁶`, `k = 135`: any pointwise correlation between `χ₂(x_{[d]G})` and
> `χ₂(x_{[d⁻¹]G})` exceeding ≈0.13% is excluded.**

≈15× tighter than the `M = 20000` bound (≈2%), on the non-algebraic map that survives the Weil
closure, at the puzzle's scale. **A bound, not an absence.** Below 0.13% is untouched, and whether a
real inversion-channel leak would exceed 0.13% is unknown.

## 4. Scope

One readout (`χ₂` of `x`), one map (`k = −1`), one bit-length, one seed. k=160 and the full-range
control are still computing and remain clean/unread. k=128 is contaminated and may be reported only
with that label.
