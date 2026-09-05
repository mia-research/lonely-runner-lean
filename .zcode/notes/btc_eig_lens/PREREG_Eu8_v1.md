# PREREG — E[u⁸] measurement (amendment extending PREREG_Eu6_v1.md)

**Status:** FROZEN before apply. Date: 2026-07-30.
**Purpose.** `RESULT_Eu6_v1.md` confirmed $E[u^6]\approx 5/64$ (SU(2)) at 12/12 OOS primes.
This locks the moment curve at orders 2, 4, 6. $E[u^8]$ is the next moment; if it matches
SU(2)'s $7/128$ the full curve is locked and the max-entropy reading is confirmed to higher
order. Cheap extension: $T_4 = (R^{*4})[0] = \sum_m (R^{*3})[m]\,R(-m)$, reusing the $T_3$
convolution already computed for $E[u^6]$.

## Object

$$E[u^8] = \frac{n\cdot T_4}{256\,p^4\,(n-1)}, \quad T_4 = \sum_{m=0}^{n-1}(R*R*R)[m]\cdot R(-m\bmod n)$$

where $(R*R*R)[m] = \sum_{j_1,j_2}R(j_1)R(j_2)R(m-j_1-j_2\bmod n)$ is the 3-fold cyclic
convolution (already computed exactly for $E[u^6]$). Exact integer signal path, no float.

## Pre-committed predictions

| | full SU(2) (Sato–Tate) | torus/CM (uniform angle) |
|---|---|---|
| $E[u^8]$ | **7/128 = 0.054688** ($C_4/4^4$, $C_4=14$) | **35/256 = 0.136719** ($\binom84/4^4$) |

## Decision (per prime, then aggregate)

Same structure as `PREREG_Eu6_v1.md`: SU(2) and uniform null bands ($R_{\text{sim}}=4000$,
seed `20260730`), 12 OOS stratum-S primes, `in_su2` / `in_unif`, L-weighted dev from $7/128$,
small-L/large-L convergence split, $1/\sqrt L$ extrapolation intercept.

## Controls

1. **C-FORCED:** $E[u^2]=n/(4p)$.
2. **C-CROSS:** integer $T_4$ vs float FFT $\sum_a|V(a)|^8/n$ (verified at $p=127$ before run).
3. **C-REPRODUCE-$E[u^4]$/$E[u^6]$:** recompute both from same $R$, confirm match to published
   ($E[u^4]$) and to `Eu6_results_v1.json` ($E[u^6]$) — instrument sanity + cross-run repro.
4. **PLANT separation:** SU(2) and uniform bands disjoint at all primes.

## Interpretation

| result | lens reading |
|---|---|
| $E[u^8]\approx 7/128$, converges | moment curve locked at orders 2,4,6,8 — full SU(2); max-entropy rate function on $\theta$ confirmed to 4th nontrivial order |
| $E[u^8]\approx 35/256$ | would refute SU(2) reading (contradicts $E[u^4],E[u^6]$) — extremely unlikely given prior |
| intermediate | a moment-curve anomaly worth characterizing |

## Scope / artifacts

Same 12 primes; all artifacts in `.zcode/notes/btc_eig_lens/`: `Eu8_run_v1.py`,
`Eu8_results_v1.json`, `RESULT_Eu8_v1.md`. Inherited banners (no security claim).
