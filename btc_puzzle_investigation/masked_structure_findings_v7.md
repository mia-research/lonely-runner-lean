# Masked-Structure — Findings v7: the joint (x,y) interference pattern

**Date:** 2026-07-16 · new object prompted by "shadow / harmonic resonance / interference in
x & y." Script: `coord_interference_v1.py`. Exact self-checks (integer); float only in the
analytic-size FFT (declared, no key in path).

## The object (never built before)

Every prior probe was single-coordinate (x-only character sums; y-parity) or the pairwise
difference set. The joint information in x **and** y lives in the 2-D additive transform of
the point set:
```
    F(a,b) = sum_{P=(x,y) in E}  e_p(a x + b y)     ( = FFT2 of the curve indicator )
```

## Result — the resonance is exactly the CM μ₃ symmetry, and nothing beyond it

| | CM `y²=x³+7` (j=0) | non-CM `y²=x³+x+1` control |
|---|---|---|
| **μ₃ symmetry** `F(a,b)=F(βa,b)` | **True (exact)** at p=307,439,607 | **False** |
| negation `F(a,b)=F(a,−b)` | True | True (every curve) |
| `max\|F\|/√p` | 3.6–4.0 | 3.0–3.5 |
| `\|F\|²/p` near-integer frac | 0.057 | 0.058 |
| `\|F\|²/p` = 1 frac (Jacobi resonance) | 0.015 | 0.015 |
| `\|F\|²/p` coeff. of variation | ≈1.00 | ≈1.00 |

**Two facts, both graded:**

1. **[VERIFIED exact]** The CM curve's joint (x,y) interference has an **exact μ₃ resonance**
   `F(a,b) = F(βa,b)` (β³=1), absent on the non-CM control. One-line reason: `ψ:(x,y)↦(βx,y)`
   bijects `E` (`(βx)³+7=x³+7`), so the exponent multiset `{a·x+b·y}` is invariant under
   `a↦βa`. Verified by exact integer multiset equality, not float. This is the GLV/CM
   covariance, now exhibited in the joint 2-D transform — the "shadow CM casts" on the
   spectrum.

2. **[VERIFIED, matched control, scoped p≤1009]** Beyond the μ₃ (+ negation) symmetry the
   `|F|²/p` spectrum shows **no quantization at the scales tested**: `max|F|~√p` (Weil),
   `CV≈1`, near-integer / `=1` mass ≈ 0.057 / 0.015 for both curves, and the two full
   distributions **converge** — KS distance 0.031→0.003 over p=307→1009 (`coord_interference`
   follow-up). A raw distinct-value-count gap (CM lower at 2-dp binning) is **a binning
   artifact**: it reverses at 1-dp binning (CM higher at p=307, 1009) and is not a robust
   signal. So: no discrete harmonic beyond the μ₃ fold **in the magnitude distribution, at
   p≤1009**. NOT tested: phase, bright-spot arrangement, higher correlations, secp's p —
   those are the un-shut residuals below, not covered by this statement.

## Reading

The joint (x,y) interference pattern, at p≤1009, is a Weil-magnitude spectrum folded by the
one exact CM symmetry (μ₃ in the x-frequency), with the residual magnitude distribution
converging to the non-CM control. Stated without inflation: **five low-order objects this
session (single-point geometric/multiplicative, cubic S3, scalar-mult, bilinear difference
set, and this) each came back generic-beyond-GLV at the scales and statistics tested.** That
is five scoped results, not a proof that GLV/CM is the *only* structure — the induction is
suggestive, not established. The μ₃ resonance here is exact and real; it is the GLV
covariance, and no *additional* harmonic showed up in the one statistic (magnitude
distribution) measured.

**Scope / grade:** VERIFIED at small p (307–607, full point-set), with a matched non-CM
control and exact symmetry self-checks. Not a proof at secp's p (max|F|~√p is the Weil
theorem; the un-quantization is empirical + control). A modest positive that closes the
joint-(x,y) gap; not a break.

## Residual, if pushed further (honest, un-shut)

- The **arrangement** of bright spots `(a,b)` beyond the μ₃-triple structure (a line? a
  sublattice?) — only the magnitude *distribution* was tested here, not the geometry of where
  the bright spots sit.
- The **multiplicative** 2-D transform `Σ_P χ(x) ψ(y)` — for j=0 curves these are classical
  sextic Jacobi sums with `|·|²=p` exactly (the real quantized object), but that is textbook
  CM theory, not a secp-specific structure.
- The **amicable cross-domain** version (the F_p pattern vs the F_n pattern) — the standing
  open E-probe, disjoint-construction so tautology-clean.
