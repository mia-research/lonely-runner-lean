# RESULT — N7: the finite-rank carrier hypothesis is REFUTED (pre-registered falsifier fired). The null is confirmed Rayleigh; the `c=0` depletion looks finite-size, not structural.

**Date 2026-09-02. Grade: `[REFUTED — pre-registered, own hypothesis]` for finite-rank;
`[VERIFIED]` for the null-is-Rayleigh baseline; `[EMPIRICAL — suggestive, n=6, min-statistic]` for
the `c=0` fade.** Executes `PREREG_n7_finite_rank_carrier_v1.md` (written before the run).
Scripts: `n7_finite_rank_v1.py` (+`.log`, `.json`), `n7_xonly_floor_v1.py` (+`.log`).
Signal path: the FROZEN `subrayleigh_deficit_scaling_v1.py` exact-int EC arithmetic; FFT float is the
sanctioned carve-out (that prereg §8). Model scale only; **no transfer to secp**.

---

## 1. The hypothesis, and why it was worth testing

The measured N7 signature — excess near-zero `|U|`, deficit at the top, `Σ|U|²` exactly matched,
`M4` blind, and **constant in `p`** — is the textbook signature of a **finite-rank** sum. The record's
own P6a/P6b bounds `|U| ≤ (1+ord_O(f))√p+1`, giving `r=4` for `c≠0` and `r=3` for `c=0`, while the
matched Hermitian null is a sum of `n≈p` phases ⇒ Gaussian ⇒ Rayleigh.

## 2. Results against the four pre-registered arms

| arm | prediction | outcome |
|---|---|---|
| **N7-A** | null matches Rayleigh | ✅ **CONFIRMED.** Null bulk `[0.00252, 0.00992, 0.03894]` vs Rayleigh `[0.00250, 0.00995, 0.03921]` at τ=.05/.10/.20 — agreement to ~1%, all four primes. The baseline the whole effect is measured against is now independently validated. |
| **N7-B** | char low tail fits finite-`r`, `r̂ ∈ [3,5]` | ❌ **NOT SUPPORTED.** `r̂=4` was returned at 4/4 primes, but **Rayleigh was not in the candidate set** (a design error, §4). Scored against Rayleigh, Rayleigh wins: low-tail SSE `5.5e−6` (Rayleigh) vs `6.8e−6` (r=4) at p=2089. |
| **N7-C** | r=4 reproduces the ~8% excess (4–16%) | ❌ **FALSIFIED.** A true 4-step walk gives τ=.05 mass `0.00375` vs Rayleigh `0.00250` — a **+50%** excess. Measured char-vs-null excess: **+6.0 / +4.5 / +7.5 / +6.0 %** (τ=.05, four primes). The model **over-predicts by ~6×**. |
| **N7-D** | sign flips at `c=0`, and `r̂(c0) < r̂(bulk)` | ⚠️ **HALF.** The **sign flip is confirmed and stronger than previously measured** (below). The rank ordering **fails**: `r̂(c0) = 3, 3, 5, 5` vs `r̂(bulk) = 4, 4, 4, 4`. |

> **Verdict: the finite-rank hypothesis is REFUTED in its stated (iid-uniform-phase) form.**
> `U` does not behave like a sum of 4 free unit vectors. In hindsight this is consistent with the
> ω-orbit saturation established 2026-09-01: the four eigenvalues are `{α, ζ₃α, −ᾱ, −ζ̄₃ᾱ}` —
> **one free angle, not four** — so a 4-step *free* walk was the wrong finite-rank model. Whether a
> correctly-constrained one-angle model fits is **not tested here and is not claimed**.

## 3. What did replicate, and one lead retired

**The bulk excess replicates independently.** Char-vs-null near-zero excess **+6.0…+7.7%** at
τ=.05/.10 across four primes, matching the banked ~8% (`RESULT_subrayleigh_deficit_locus_v1`). The
effect is not in question here; only my proposed cause is.

**The `c=0` (x-only) depletion — retired as probably finite-size.** The locus drill named a weak,
non-τ-robust char-specific near-zero *depletion* on this axis and owed it a powered follow-up. At
τ=0.05 it looked absolute — **zero** x-only harmonics below 5% of RMS at p=349, 577, 991, where the
null has its usual share. But the minimum itself tells a different story:

| p | 211 | 349 | 577 | 991 | 1471 | 2089 |
|---|---|---|---|---|---|---|
| char `min\|U(b,0)\|/RMS` | 0.0893 | 0.1149 | 0.0711 | 0.0593 | 0.0261 | 0.0156 |
| null mean-of-mins (K=20) | 0.0862 | 0.0670 | 0.0568 | 0.0445 | 0.0312 | 0.0231 |
| **ratio** | **1.0×** | **1.7×** | **1.3×** | **1.3×** | **0.8×** | **0.7×** |

**There is no hard floor.** The ratio falls monotonically past 1 and is *below* the null at the two
largest primes. The τ=0.05 "zeros" were the stratum's minimum happening to sit above 0.05 at three
small primes — a small-`N` artifact (`c=0` holds only `p` values, vs `p²` in the bulk), not a bound.
The depletion **fades with `p`**, which is the signature of a finite-size effect rather than a
mechanism.

**Caveat, binding:** this is a **min-statistic on 6 primes** — a noisy estimator. The fade is
*suggestive*, not decided. A powered test needs the full low-tail CDF on the `c=0` stratum across a
wider `p` range with matched draw counts, τ-concordance, and an √N-rising check. Until then the
locus drill's owed follow-up is **narrowed, not discharged**.

## 4. Instrument defect found in my own probe

`fit_r` searched only the finite-rank table `{2,3,4,5,6,8,12}` and **omitted Rayleigh as a candidate
model**. It therefore always returned some `r̂`, and reporting `r̂=4` as a fit would have been an
artifact of the restricted model class — the same defect class as the `canon()` and `β` conventions
retired this week. Caught by scoring the residuals by hand. The `r=12` row was the intended Rayleigh
proxy and is a poor one (`[0.00242, 0.00953, 0.03752]` vs Rayleigh `[0.00250, 0.00995, 0.03921]`).
**Any re-run must include Rayleigh, and preferably a one-angle ω-orbit model, in the candidate set.**

## 5. Scope

`E: y²=x³+7`; p ∈ {211, 349, 577, 991, 1471, 2089}; `a₀=1`; K=10–30 Hermitian null draws; the
5-threshold low-tail CDF. **Closed:** the free-phase finite-rank model as the carrier of N7.
**NOT closed:** N7 itself — the carrier remains unidentified; a *constrained* (one-angle /
ω-orbit-saturated) finite-rank model is untested; the imaginary-part isotype, higher-order phase
invariants, and the co-occurrence arms named by the locus drill all remain open.
