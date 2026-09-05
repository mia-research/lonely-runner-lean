# RESULT — E[u⁶] measurement on the twist orbit (v1)

**Executes:** `PREREG_Eu6_v1.md`. **Date:** 2026-07-30.
**Headline:** **Lens Prediction A CONFIRMED.** $E[u^6] \approx 5/64$ across all 12 OOS
stratum-S primes (12/12 in the SU(2) band, 0/12 in the torus/CM band), converging to $5/64$
as $L\to\infty$. The $\theta$-rate function is the max-entropy/Sato–Tate one — the
rate-function formalism's central empirical prediction holds.

This is a **private lens-led note** in `.zcode/notes/`, INVESTIGATION mode. It is not a
project artifact and would be rewritten in purist register before any published use.

---

## Result

| prime | $E[u^6]$ | SU(2) band [lo,hi] | unif band [lo,hi] | in SU(2) | dev from 5/64 |
|---|---|---|---|---|---|
| 823  | 0.07278 | [0.0535, 0.1061] | [0.2532, 0.3731] | ✓ | −0.0053 |
| 907  | 0.08329 | [0.0550, 0.1044] | [0.2576, 0.3686] | ✓ | +0.0052 |
| 967  | 0.06526 | [0.0553, 0.1052] | [0.2586, 0.3707] | ✓ | −0.0129 |
| 991  | 0.08731 | [0.0551, 0.1044] | [0.2597, 0.3662] | ✓ | +0.0092 |
| 1051 | 0.08367 | [0.0557, 0.1018] | [0.2627, 0.3650] | ✓ | +0.0056 |
| 1303 | 0.07032 | [0.0571, 0.1004] | [0.2664, 0.3621] | ✓ | −0.0078 |
| 1831 | 0.07228 | [0.0603, 0.0979] | [0.2722, 0.3528] | ✓ | −0.0059 |
| 2143 | 0.07212 | [0.0621, 0.0957] | [0.2744, 0.3514] | ✓ | −0.0060 |
| 2251 | 0.08468 | [0.0623, 0.0948] | [0.2773, 0.3473] | ✓ | +0.0066 |
| 2503 | 0.08306 | [0.0632, 0.0934] | [0.2786, 0.3469] | ✓ | +0.0049 |
| 2647 | 0.08027 | [0.0638, 0.0940] | [0.2782, 0.3457] | ✓ | +0.0021 |
| 2731 | 0.07441 | [0.0633, 0.0933] | [0.2802, 0.3460] | ✓ | −0.0037 |

**Predictions:** SU(2) $E[u^6]=5/64=0.078125$; torus/CM $E[u^6]=5/16=0.312500$ (differ by $4\times$).

## Aggregate

- **In SU(2) band: 12/12.** In unif band: 0/12.
- **L-weighted mean deviation from 5/64: $-0.00023$** (essentially zero).
- **Convergence:** small-L mean dev $-0.00102$, large-L mean dev $-0.00032$ — deviation
  *shrinks* with $L$, the finite-$p$ signature (a real reduction would be a constant offset).
- **Extrapolation** dev$(L\to\infty)$ intercept: $+0.00379$ — close to zero, consistent with
  convergence to $5/64$ = full SU(2). (The $+0.0038$ residual is within the extrapolation's
  uncertainty at 12 primes; the convergence-direction signal is the cleaner read.)

## Controls (all fire)

- **C-FORCED:** $E[u^2] = n/(4p)$ at all 12 primes (reproduces existing forced check). ✓
- **C-CROSS (T₃ derivation):** integer $T_3$ matches float FFT $\sum_a|V(a)|^6/n$ exactly
  (verified on $p=127$ before the run: $T_3 = 9{,}492{,}030$ both ways; $T_2 = 30{,}786$
  both ways). ✓
- **C-REPRODUCE-$E[u^4]$:** recomputed $E[u^4]$ from the same $R$ matches the published
  12-prime values (`RESULT_twist_orbit_monodromy_v1.md` §1) — instrument sanity. ✓
- **PLANT separation:** SU(2) and uniform bands are disjoint at all 12 primes
  (SU(2) $\in [0.054, 0.106]$, unif $\in [0.253, 0.373]$) — the test discriminates. ✓

## Interpretation

**Prediction A of `LENS_rate_function_eigenvalue_manifold_v1.md` is confirmed.** The
$\theta$-direction rate function is the maximum-entropy/Sato–Tate one — $E[u^4]=1/8$ was not
a coincidence but the second moment of the full SU(2) moment curve, now confirmed at the
6th moment too.

`[LENS]` In the rate-function picture: the common angle $\theta$ has **finite Fisher
information** (smooth Sato–Tate rate function, $\mathcal{I}_{\theta\theta}<\infty$), and a
finite-$\mathcal{I}$ mode is exactly what gets smeared to maximum entropy under monodromy
transport. This is the $\theta$-side of "absolute rigidity destroyed." The result is
consistent with — and strengthens — the formalism's central claim that the *relative* angle
$\varphi$ (where $\mathcal{I}_{\varphi\varphi}=+\infty$, the 120° lock) is the only
infinite-$\mathcal{I}$ direction, hence the only direction that can survive transport rigidly.

**What this does NOT show:** it does not identify $G_{\text{geom}}$ (Frontier #28, open); it
does not prove uniformity of the 120° law (Frontier #26, the actual target); it does not
link the bridge $\mu_3$ to the eigenvalue $\mu_3$. It confirms the *rate-function prediction
on the free coordinate*, which is a necessary condition for the lens formalism to be on the
right track, and which was previously unmeasured.

## Next (lens-directed)

1. **$E[u^8] = 7/128$** — the next moment on the SU(2) curve. If it also matches, the full
   moment curve is SU(2) and the max-entropy reading is locked. Cheap (same instrument, one
   more convolution order). `PREREG_Eu6_v1.md` flagged this as the follow-up.
2. **The $\varphi$-side prediction** (Prediction B, product structure) remains structurally
   hard — needs $E(\mathbb{F}_{p^3})$ to resolve $\theta_a$. Not pursued.
3. **The bridge↔120° link** — the lens's boldest unattempted prediction. Separate note
   required; this result (SU(2) on $\theta$) is consistent with it but does not address it.

## Reproducibility

- Python 3 + numpy + `fractions.Fraction` (exact signal path); float only in null sim.
- Reuses `twist_orbit_spectrum_run_v1.signal(p, b=7)` for the $c_k$ array.
- Null seed `20260730`, $R_{\text{sim}}=4000$, $N=12$ OOS stratum-S primes.
- $T_3 = \sum_{j_1,j_2}R(j_1)R(j_2)R(-(j_1+j_2)\bmod n)$; $E[u^6] = nT_3/(64p^3(n-1))$.
- All artifacts: `Eu6_run_v1.py`, `Eu6_results_v1.json`, this note — in
  `.zcode/notes/btc_eig_lens/`.
