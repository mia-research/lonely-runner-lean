# PREREG addendum — μ₃-forced subspace residual, v2 scaled-up extension

**Date:** 2026-08-08.
**Parent:** `PREREG_mu3_subspace_residual_v1.md`.
**Script:** `mu3_subspace_residual_v2.py`.
**Purpose:** tighten the v1 scoped null by extending the powered range from $|Q_6| \leq 426$ to
$|Q_6| \sim 16000$ (~40×). v1 was binding-limited by the $O(L^2)$ naive null; v2 replaces it with
numpy-vectorized nulls and adds larger primes.

## 1. What changes from v1

| | v1 | v2 |
|---|---|---|
| Null draws per cell | $R = 3000$, pure Python | $R = 5000$, numpy-vectorized batch |
| $|Q_6|$ range | $5 \to 426$ | $5 \to \sim 16000$ |
| Prime strata | IN/S/C frozen (22 primes, $p \leq 2503$) | new LARGE stratum: 6-8 primes $p \in [10^4, 10^5]$ |
| Pruning | IN stratum unpowered → dropped | only run primes where $|Q_6| \geq 200$ |
| Probes | A, B, C (all retained) | A, B, C + **Probe D**: max-Fourier on $Q_6$ at scale |

## 2. Probe D — max-Fourier on $Q_6$ at scale (the prior probe, re-run with power)

The prior max-Fourier probe (`mu3_forced_subspace_object_v1.py`, 8 primes, $|Q_6| \leq 138$) returned
`[SCOPED NULL — LOW POWER]`. At $|Q_6| \sim 16000$ the same statistic has ~100× power. Re-run with:
- **Statistic:** $T_D = \max_{1 \leq k < L} |\sum_{j=0}^{L-1} u_j\, e^{-2\pi i k j/L}|$.
- **Null:** $R = 5000$ random $\pm 1$ sequences of length $L$; rank $T_D$ among null maxima.
  Null computed via numpy batch FFT (float permitted inside the monotone statistic only, ranked
  against null — same convention as `twist_orbit_spectrum_run_v1.py`).
- **Firing control:** plant a single-Fourier-mode signal at known amplitude; must FIRE.

## 3. Primes (LARGE stratum, frozen here)

Selected by: $p \equiv 7 \pmod{12}$, $p$ prime, $\#E(\mathbb{F}_p) = p+1$ prime (so $n$ prime, $Q_6$
integral), $p$ in $[10^4, 10^5]$. Walk primes, test the conditions, take the first 8 that qualify.
Also re-run the v1 S-stratum primes where the B-plant fired (1303, 2143, 2251, 2503) as a
consistency bridge.

## 4. Discipline (unchanged from v1)

- Exact-int signal path (Legendre, dlog, index arithmetic). `check_no_float.py` must pass.
- Float only inside the monotone statistic (Fourier magnitude, sum), ranked against matched null.
- Firing controls at every prime; instrument invalid if control fails.
- Verdict → grade map: rank $\geq 99\% \cdot R$ at $\geq 5/8$ LARGE primes = POSITIVE–replicated;
  rank $\geq 99\%$ at fewer = NULL; control failure = NO VERDICT.

## 5. Seed and reproducibility

- Seed: `20260809` (frozen here).
- $R = 5000$.
- No deviations yet; file `PREREG_mu3_subspace_residual_v1_DEVIATIONS.md` if any.
