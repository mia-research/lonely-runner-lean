# 130-bit vs 256-bit scalar: flap density of P=dG — high-powered NULL (no density bias)

**Date:** 2026-07-22 · **Script:** `flap_density_glv_prereg_v1.py` (prereg in its header). Exact-int
signal path; z-score is a report-only statistic on integer counts.

## Hypothesis tested (user)
GLV-cell rigidity for a 130-bit scalar `d` (Babai coefficients `(c₁,c₂)` forced to microscopic
integers) pushes `P=dG` out of the ¼ Eisenstein flap into the ¾ core ⇒ an exploitable density bias /
Kangaroo lever. Motivated by a 2.7σ gap in a prior n=6000 spot check (130-bit 23.92% vs 256-bit 26.03%).

## Result (N = 100,000 each arm, exact flap classifier)
| arm | flap density |
|---|---|
| 130-bit `dG` (`d∈[2¹²⁹,2¹³⁰)`) | 24871/100000 = **0.24871** |
| 256-bit `dG` (`d∈[1,N_ord)`) | 25036/100000 = **0.25036** |
| true fraction (uniform random valid abscissas) | 24763/100000 = 0.24763 |

**gap(130−256) = −0.00165, z = −0.85 → NULL.** All three agree at ≈0.2485 (the secp flap fraction,
just under ¼). Each `dG` arm matches the point-native reference (`|z|<1.5`). The prior 2.7σ (n=6000)
regressed to noise at 17× the sample.

## Power / scope
`[VERIFIED — high power]`. N=100,000 ⇒ SE(diff) ≈ 0.0019; the design resolves a real gap **≥ 0.008 at
4σ**; observed gap 0.0017. So the base flap density of a 130-bit-scalar point equals the true fraction
to **well under 1%**. Scope: base density only (the 1-bit ε readout), secp256k1, N=1e5.

## Why it had to be null (object-level)
`P=dG` is the **same point** regardless of how `d` is decomposed — GLV `[k₁]G+[k₂]φ(G)` and plain
double-and-add give identical `P`. The Babai coefficients `(c₁,c₂)` are an artifact of the **scalar's**
decomposition; ε reads `x(P)`. So GLV-cell rigidity is a scalar-side property that does not transfer to
the point. Equidistribution then pins the flap density of `{dG}` over any wide window to the true
fraction. **The scalar side is rigid; the point side is generic — the ECDLP scramble is exactly that
gap.** No Kangaroo lever from base flap density.

## Not excluded (honest scope)
This bounds the **base density of the 1-bit flap ε** only. It does not test: finer rhombus / `ν_π`
position, joint multi-point statistics, or any scalar-correlated readout (all separately null this
session). No leakage claim beyond the measured density.

## Reproduction
```
python3 flap_density_glv_prereg_v1.py 100000
```
