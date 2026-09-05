# RESULT — the M40 triple probe: NO 3-sign group-law coupling beyond the forced vanishing loci (total cube enumeration, 6 primes, both arms)

**Date 2026-08-22. Grade: `[VERIFIED — exact, total enumeration]`** (counts exact; floats only to
display MI). Deterministic first pass per `ROADMAP_REDIRECT_v3` (no leakage claim). Script:
`m40_triple_probe_v1.py` (+ `.log`). Continues `RESULT_m40_n15_exact_accounting_v1.md` (pairwise
flatness) into the 3-point regime — the N15∩M40 intersection the (g)/(h) sessions converged on.

## Object

$f(d) = \chi_2(y_{[d]G})$ (M40's forced $\mu_6$-invariant sign sequence), primes 43, 79, 127, 163,
211 ($p \equiv 7 \bmod 12$) and 61 ($\equiv 1$, anomalous). **Total enumeration of the cube**
$(d_1,d_2,d_3) \in [1,n)^3$ (up to $7.6 \times 10^6$ triples/prime). Statistics:

- $MI_3 = I(f(s); (f_1,f_2,f_3))$, $s = d_1+d_2+d_3 \bmod n$;
- $gain_3 = I(f(s); f_3 \mid f_1, f_2)$ (same-cube conditional — the "does a third point's sign add
  anything beyond two?" question);
- $MI_3^{\rm rest}$: the same off **all four forced vanishing loci** ($d_i{+}d_j \equiv 0$, $s \equiv 0$
  — cube mass exactly $4/n$, verified).

## Results

| p | n | MI₃ | gain₃ | MI₃^rest | 2/n |
|---|---|---|---|---|---|
| 43 | 31 | 0.005380 | 0.005350 | 0.002809 | 0.0645 |
| 79 | 67 | 0.001033 | 0.001031 | 0.000565 | 0.0299 |
| 127 | 127 | 0.000173 | 0.000173 | 0.000193 | 0.0157 |
| 163 | 139 | 0.000177 | 0.000176 | 0.000145 | 0.0144 |
| 211 | 199 | 0.000086 | 0.000086 | 0.000070 | 0.0100 |
| 61 | 61 | 0.001086 | 0.001082 | 0.000733 | 0.0328 |

**Readings:**
1. **Flat off the forced loci at every prime, both arms** — $MI_3^{\rm rest}$ is an order of magnitude
   below $2/n$ everywhere, and the whole MI₃ scales like $c/n^2$ with $c \approx 3$–$5$
   ($MI_3 \cdot n^2 = 5.2, 4.6, 2.8, 3.4, 3.4, 4.0$) — **faster than the pairwise $1/n$**. At secp
   this is $2^{-510}$-scale: total vanish.
2. **No third-point synergy:** $gain_3 \approx MI_3$ throughout — the conditional information added by
   a third sign is indistinguishable from the (already $n^{-2}$) whole; there is no separate
   synergistic component.
3. With (g)'s pairwise result: **the sign family carries no 2- or 3-point group-law coupling beyond
   the named forced vanishing loci**, at total-enumeration power, on both mod-12 arms.

## Scope / burden-on-closure

Closed: 3-sign readouts of group sums, at the tested scopes (6 primes ≤ 211, total enumeration, zero
sampling error; secp by the measured $n^{-2}$ decay). **Not closed:** 4+-point couplings; non-sign
readouts (sextant/tuple-valued across points); weighted/multiset 3-point objects (the E3-class —
already powered-bounded on the real 82 by N30); the Fourier-side $V(a)$ family. The N15 filter
question is therefore pushed fully outside the sign-sequence world: any cheap alignment must live in
*non-sign, structured* joint readouts — the exact residue named in (g)/(h).
