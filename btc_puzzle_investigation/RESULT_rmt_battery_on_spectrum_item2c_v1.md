# RESULT — ITEM 2 FINISHED: the RMT battery run on an ACTUAL SPECTRUM. My substitution is corrected.

**Date:** 2026-08-01. **Script:** `transfer_operator_rmt_battery_v1.py`. **Grade:** `[EMPIRICAL — NULL, power validated]`.

## 0. The substitution, named

Asked for **spacing / `Δ₃` / `Σ²`** on the `|T(a,b)|²` object, I measured **spatial autocorrelations**
(`C_a1`, `C_b1`, `C_a3`). Those are 2-D grid-adjacency statistics and have nothing to do with
spectral rigidity or the Wigner surmise. I pivoted because level statistics on raw intensities looked
degenerate to me — but I never demonstrated that, and I closed the item anyway. Both faults are
corrected here.

## 1. PART A — the degeneracy, demonstrated rather than asserted

Unfolding a sample through its **own empirical CDF** returns exactly the uniform order statistics:

| input | unfolded spacings |
|---|---|
| Porter–Thomas (exponential) | min 1.000000, max 1.000000, sd `1.5e-13` |
| uniform | min 1.000000, max 1.000000, sd `1.5e-13` |
| **bimodal (wildly non-PT)** | min 1.000000, max 1.000000, sd `1.5e-13` |

Every input gives a perfectly rigid ladder, so `Δ₃ = 0` identically and the statistic carries **zero
information about the data**. Unfolding through a *theoretical* CDF instead re-tests the **marginal**
— i.e. Porter–Thomas, already measured. **Neither branch is a 2-point statistic. The 2-point content
requires an actual operator.** That is the argument I should have made and measured the first time.

## 2. PART B — the real spectrum

The record's thermodynamic layer has a genuine operator: the coarse-grained transfer (Koopman)
operator of a label under `P → P+G` (`conservation_spectrum_v1.py`). **The record extracted exactly
one number from it, `|λ₂|`, from a 16- or 6-state version. Its full spectrum was never examined.**

Refined to `K = 18` bins with consecutive-pair states ⇒ **324 states, 323 non-Perron eigenvalues** —
enough to carry level statistics. Battery: nearest-neighbour spacing in `ℂ`, `Δ₃` on the
smooth-unfolded moduli, `Σ²` in disks. **Null = the record's own shuffle floor** (shuffle the label
sequence; destroys dynamics, preserves the label marginal exactly). No Ginibre, GUE or Katz–Sarnak
prediction is assumed anywhere.

**A second self-inflicted bug, caught by the plant.** My first `Δ₃` rank-unfolded the moduli — which
forces the counting function exactly linear, i.e. **precisely the degeneracy Part A demonstrates**.
It read `0.0000` against a null of `0.0000` and its plant did not fire. Fixed with degree-5 smooth
unfolding; the plant then went from `z = −0.62` to `z = +30 … +343`.

## 3. Result — NULL

10 primes (`p = 433 … 1237`), `R = 120` shuffle draws:

| statistic | cells `p ≤ 0.05` | expected | OOS mean z |
|---|---|---|---|
| nearest-neighbour spacing | **0/10** | 0.5 | +0.33 |
| `Δ₃` rigidity | 2/10 | 0.5 | −0.18 |
| `Σ²` number variance | 2/10 | 0.5 | +0.35 |

**30 cells, 4 hits, 1.5 expected (`P ≈ 0.06`)** — with `Δ₃` and `Σ²` correlated (both long-range
rigidity), **mixed signs** (no consistent direction at any statistic), and **OOS mean z ≈ 0** on all
three. Discovery set `{433, 1051, 2089}`; the other seven primes are out of sample.

**C-PLANT (a planted near-conservation / sticky label) fires at `z = +15 … +343` on all three
statistics at every prime.** Power is not in question.

> **The transfer-operator spectrum shows no rigidity, no spacing structure and no number-variance
> anomaly beyond its own shuffle floor.**

## 4. Scope

`p ≤ 1237`, 10 primes, `j = 0` prime-order cyclic curves, `K = 18` x-binning with pair states
(324 states), shuffle null, `R = 120`. Untested: other label alphabets (the μ₆-covariant lift-cell
and norm-band labels the record used), finer `K`, and larger `p`.

## 5. Method note

Two degeneracies in one file, both from the same root: **unfolding a sequence by its own ranks
destroys exactly the information the statistic is meant to measure.** Part A demonstrates it
deliberately; Part B then reproduced it by accident, and only the plant caught it. A rigidity
statistic that cannot see a planted rigid spectrum is not measuring rigidity — check the plant
before reading the data column.
