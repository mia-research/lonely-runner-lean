# PREREG — E[u⁶] measurement on the twist orbit (v1)

**Status:** FROZEN before apply. Gate: `experiment-designer` (isolated). Date: 2026-07-30.
**Motivation.** `LENS_rate_function_eigenvalue_manifold_v1.md` Prediction A: if the
$\theta$-rate function is the max-entropy/Sato–Tate one (as $E[u^4]=1/8$ suggests), then ALL
even moments follow SU(2)'s curve. $E[u^6]$ is the next moment and is **named but never
implemented** in `PREREG_twist_orbit_monodromy_v1.md` (the run code computes only $E[u^2]$
forced and $E[u^4]$). This prereg measures it.

## Object

$u(a) = V(a)/(2i\sqrt p)$, $V(a) = \sum_{P\in E(\mathbb{F}_p)}\chi_2(y_P)\zeta_n^{a\,d(P)}$.
The 6th moment, exact-integer signal path (matches `twist_orbit_monodromy_run_v1.py`):

$$E[u^6] = \frac{n\cdot T_3}{64\,p^3\,(n-1)}, \quad T_3 = \sum_{j_1=0}^{n-1}\sum_{j_2=0}^{n-1} R(j_1)\,R(j_2)\,R(-(j_1+j_2)\bmod n)$$

where $R(j) = \sum_{k=0}^{n-1} c_k c_{k+j\bmod n}$ is the integer autocorrelation of
$c_k = \chi_2(y_{[k]G})\in\{\pm 1\}$. **No float in the signal path** (Fraction throughout);
float lives only in the null simulation.

**Derivation check.** Matches the $E[u^4]$ formula at one lower order:
$E[u^4] = \frac{n\sum_j R(j)^2}{16p^2(n-1)} = \frac{n\cdot T_2}{16p^2(n-1)}$ with
$T_2 = \sum_{j_1}R(j_1)R(-j_1)$. The pattern $T_k/(2^{2k}p^k(n-1))$ with prefactor $n$ holds
for $k=2,3$.

## Pre-committed predictions (FROZEN before data)

| | full SU(2) (Sato–Tate, max-entropy) | torus/CM (uniform angle) |
|---|---|---|
| $E[u^6]$ | **5/64 = 0.078125** | **5/16 = 0.3125** |

The two predictions differ by $4\times$ — easily resolvable at $L\sim (n-1)/6 \sim 200$–$400$.

## Null band (float reference; NOT the data)

Two iid simulations of $L=(n-1)/6$ draws each, $R_{\text{sim}}=4000$ resamples, seed frozen
`20260730`:
- **SU(2) null:** $u = \cos\theta$, $\theta$ from semicircle density $(2/\pi)\sqrt{1-u^2}$
  (rejection sampling, matches `_st_u` in the existing run).
- **Torus/CM null:** $u = \cos\theta$, $\theta$ uniform on $[0,\pi]$ (matches `_unif_u`).
- Band = 2.5/97.5 percentiles of the simulated $E[u^6]$.

## Decision (per prime)

```
in_su2   iff  E[u⁶](p) ∈ [su2_lo, su2_hi]
in_unif  iff  E[u⁶](p) ∈ [unif_lo, unif_hi]
```
Plus exact-Fraction comparison to $5/64$ and $5/16$ (`below_5_64`, `below_5_16`).

**Aggregate (12-prime OOS stratum-S, same set as `RESULT_twist_orbit_monodromy_v1.md`):**
- count `in_su2`, count `in_unif`.
- L-weighted mean deviation from $5/64$.
- Convergence check: split small-L / large-L halves; finite-p correction shrinks with $L$,
  a real reduction is a constant offset.
- Linear extrapolation of dev vs $1/\sqrt{L}$ to $L\to\infty$; intercept $\approx 0$ ⟹ SU(2).

## Interpretation (lens predictions)

| result | lens reading |
|---|---|
| $E[u^6]\approx 5/64$ on most primes, converges to $5/64$ | **Prediction A CONFIRMED** — $\theta$-rate function is max-entropy/SU(2); lens formalism holds on $\theta$-direction; supports the rate-function/Fisher-info picture |
| $E[u^6]\approx 5/16$ | **Prediction A REFUTED on $\theta$** — rate function is NOT max-entropy; lens picture wrong on $\theta$ (may still hold on $\varphi$); the $E[u^4]=1/8$ match was coincidental |
| intermediate / mixed | **third monodromy group** — neither full SU(2) nor torus; the moment curve discriminates structure $E[u^4]$ could not; most informative outcome |

## Controls (must fire)

1. **C-FORCED:** $E[u^2] = n/(4p)$ (reproduce existing forced check).
2. **C-CROSS:** exact $n\cdot T_3$ vs float FFT $\sum_a |V(a)|^6$ — agree to $10^{-9}$.
3. **C-REPRODUCE-$E[u^4]$:** recompute $E[u^4]$ from the same $R$ and confirm it matches the
   published 12-prime values (`RESULT_twist_orbit_monodromy_v1.md` §1) — instrument sanity.
4. **PLANT-SU2 / PLANT-UNIF separation:** the SU(2) and uniform null bands must be disjoint
   at the primes tested (else the test cannot discriminate).

## Scope

- Same 12 OOS stratum-S primes as `RESULT_twist_orbit_monodromy_v1.md`: 823, 907, 967, 991,
  1051, 1303, 1831, 2143, 2251, 2503, 2647, 2731. (Read from the existing freeze JSON.)
- $E[u^6]$ and $E[u^8]$ (`7/128`) — this prereg covers $E[u^6]$ only; $E[u^8]$ is a follow-up
  if $E[u^6]$ matches SU(2) (further confirmation) or if it's intermediate (more
  discrimination).
- **SCALE BANNER / LANGUAGE RULES / ANOMALY-DRILL RULE** inherited. This identifies a
  monodromy group moment-by-moment; it is not a security claim.

## Reproducibility

- Python 3 + numpy + `fractions.Fraction` (exact signal path); float only in null sim.
- Reuses `twist_orbit_spectrum_run_v1.signal(p, b=7)` for the $c_k$ array.
- Null seed `20260730`, $R_{\text{sim}}=4000$.

## Artifacts (this directory: `.zcode/notes/btc_eig_lens/`)

- `Eu6_run_v1.py` (the measurement)
- `RESULT_Eu6_v1.md` (after the run)
