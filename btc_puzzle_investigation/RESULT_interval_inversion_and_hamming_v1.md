# RESULT — interval inversion and Hamming weight, run: both NULL; the spectral arm popped and died OOS

**Date:** 2026-08-01. **Script:** `interval_inversion_and_hamming_v1.py`.
**Grade:** `[EMPIRICAL — SCOPED NULL]`, power stated. **Neither covariate is closed as a channel.**

## 0. Why these ran

I had dismissed the interval-inversion covariate as *"no mechanism, near-zero prior"*. That is a
dismissal with no object/class/power/scope — the closure-by-declaration bar this project forbids —
and it **conflated low prior with low power**. With `M` sampled `d₀` the test detects correlation of
order `1/√M`: ordinary power. The user was right; it ran.

Hamming weight ran too. It is **legal** — the binary expansion of `d ∈ [0,N)` is unique, so
`popcount(d)` is a genuine function of the group element, unlike `(k₁,k₂)`. But the motivation
offered for it — *"double-and-add performs popcount(d) additions, so it is the physical footprint"* —
is **not a mechanism**: `[d]G` is the same point for every multiplication algorithm. That is
precisely why the Voronoi thesis died, and it is the same error one level along.

## 1. Result — `M=150` intervals, `W=128`, `d₀ ∈ [2^127,2^128)`, `R=4000`

| arm | statistic | exact perm p |
|---|---|---|
| A1 | `T(d₀)·T(d₀⁻¹)` (pointwise-style) | 1485/4001 |
| **A2** | **`|T(d₀)|·|T(d₀⁻¹)|` (spectral)** | **278/4001 = 0.069** |
| B1 | `T(d₀)·popcount(d₀)` | 3538/4001 |
| B2 | `|T(d₀)|·popcount(d₀)` | 2218/4001 |

**C-PLANT fires on both arms down to 12–25% of pairs forced.** Instrument has power.

## 2. A2 popped, then died out-of-sample

A2 was the variant predicted in advance to be the live one ("a spectral or variance leak rather than
a strict 1-to-1 point correlation"). It read 0.069 in-sample — below the fire threshold, but lowest
on the board, so the standing rule applies: **OOS before naming.**

| seed | A2 exact perm p |
|---|---|
| in-sample 20260801 | 0.069 |
| 55501 | 0.831 |
| 88802 | 0.324 |
| 13303 | 0.700 |

**Dead.** Sixth chance pattern killed by the pre-committed OOS rule (after `k=t`, p=2731
multiplicativity, `max|u|`, `S3_max`, and the x-only phase-recon seed-noise item).

## 3. Scope

`W=128`, `M=150`, `d₀ ∈ [2^127,2^128)`, `χ₂(x)` readout, pairing-permutation null, `R=4000`.
Power: detects a coupling forced on ≳12–25% of pairs. Untouched: other widths, other readouts,
the **pointwise** inversion statistic `Σ_i χ₂(x_{[d]G})χ₂(x_{[d⁻¹]G})` at `2^128` (a different
object — this arm is interval-level), low-Hamming-weight `d` as a restricted class rather than a
smooth correlate, and higher-order spectral statistics on `|T|`.
