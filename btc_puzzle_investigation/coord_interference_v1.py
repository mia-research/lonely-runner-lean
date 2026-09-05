#!/usr/bin/env python3
"""
coord_interference_v1.py — the JOINT (x,y) additive-interference pattern.

New object (never built): the 2-D transform of the curve point-set,
    F(a,b) = sum_{P=(x,y) in E}  e_p(a*x + b*y),   e_p(t)=exp(2pi i t/p).
This is the "interference pattern" of information in x AND y together (all prior
probes were x-only or y-parity). F = FFT2 of the curve indicator n(x,y).

FORCED symmetries (exact self-checks):
  * GLV / CM:  psi:(x,y)->(beta x,y), beta^3=1, is a bijection of E (since (beta x)^3+7
    = x^3+7) => F(a,b) = F(beta*a, b) EXACTLY (a mu_3 resonance in the x-frequency).
  * negation:  (x,y)->(x,-y) bijection => F(a,b) = F(a,-b).
These are verified by EXACT integer multiset equality of the exponents (no float).

THE OPEN QUESTION (beyond forced symmetry): is the spectrum {|F(a,b)|} generic
(~sqrt p everywhere, Weil) or QUANTIZED (piling at |F|^2 = p, like CM Jacobi sums)?
Quantization = a genuine discrete harmonic resonance. Matched control: a NON-CM curve
y^2 = x^3 + x + 1 (j != 0), which must LACK the mu_3 symmetry.

GRADE UP FRONT: most likely VERIFIES CM (mu_3 symmetry + possible quantization), not a
break. Value: the joint-(x,y) resonance object, built, with an exact self-check + control.

FLOAT NOTE: the FFT that turns the point-set into |F(a,b)| is an analytic-size character-
sum check (roots of unity), NOT a key/leakage signal path -- float FFT is fine here (same
carve-out as glv_closure_verification). The SYMMETRY claims are checked exactly (integers).
"""
import math
import numpy as np
from sympy import isprime
from hybrid_char_sum_v1 import legendre, tonelli


def curve_points(p, a_coef, b_coef):
    """all (x,y) on y^2 = x^3 + a x + b over F_p."""
    pts = []
    for x in range(p):
        r = (x * x * x + a_coef * x + b_coef) % p
        if r == 0:
            pts.append((x, 0))
        elif legendre(r, p) == 1:
            y = tonelli(r, p)
            pts.append((x, y)); pts.append((x, (p - y) % p))
    return pts


def cube_root(p):
    e = (p - 1) // 3
    g = 2
    while pow(g, e, p) == 1:
        g += 1
    return pow(g, e, p)                       # primitive cube root of unity mod p


def pattern(p, pts):
    """|F(a,b)| over all (a,b) via FFT2 of the indicator (float; analytic-size)."""
    A = np.zeros((p, p))
    for (x, y) in pts:
        A[x, y] += 1.0
    F = np.fft.fft2(A)                         # F[a,b] = sum e_p(a x + b y)
    return np.abs(F)


def check_mu3_exact(p, pts, beta):
    """F(a,b)=F(beta a,b) EXACT: for sample (a,b), exponent multisets coincide."""
    import random
    rng = random.Random(p)
    ok = True
    for _ in range(20):
        a = rng.randrange(1, p); b = rng.randrange(0, p)
        L1 = sorted((a * x + b * y) % p for (x, y) in pts)
        L2 = sorted((beta * a * x + b * y) % p for (x, y) in pts)
        if L1 != L2:
            ok = False; break
    return ok


def check_negation_exact(p, pts):
    """F(a,b)=F(a,-b) EXACT via (x,y)->(x,-y) bijection."""
    import random
    rng = random.Random(p + 1)
    ok = True
    for _ in range(20):
        a = rng.randrange(0, p); b = rng.randrange(1, p)
        L1 = sorted((a * x + b * y) % p for (x, y) in pts)
        L2 = sorted((a * x - b * y) % p for (x, y) in pts)
        if L1 != L2:
            ok = False; break
    return ok


def spectrum_stats(p, M):
    """max|F|/sqrt p over (a,b)!=0, and QUANTIZATION: how much mass sits at |F|^2 ~ k*p."""
    s2 = (M * M) / p                                  # |F(a,b)|^2 / p
    s2flat = s2.copy(); s2flat[0, 0] = 0.0            # drop trivial (a,b)=(0,0)
    mx = math.sqrt(float(s2flat.max()))
    vals = s2flat[(s2flat > 1e-6)].ravel()            # nonzero |F|^2/p values
    # quantization: fraction of (a,b) whose |F|^2/p is within 2% of the NEAREST integer
    nearest = np.round(vals)
    frac_near_int = float(np.mean(np.abs(vals - nearest) < 0.02 * np.maximum(nearest, 1)))
    # fraction sitting near 1 exactly (|F|=sqrt p)  -- the Jacobi-sum resonance
    frac_at_1 = float(np.mean(np.abs(vals - 1.0) < 0.02))
    # spread: coefficient of variation of |F|^2/p (low = quantized/rigid, high = smooth)
    cv = float(vals.std() / (vals.mean() + 1e-12))
    ndist = len(np.unique(np.round(vals, 2)))
    return mx, frac_near_int, frac_at_1, cv, ndist, len(vals)


def analyze(p, a_coef, b_coef, label, do_sym):
    pts = curve_points(p, a_coef, b_coef)
    M = pattern(p, pts)
    mx, fni, f1, cv, nd, nv = spectrum_stats(p, M)
    beta = cube_root(p)
    mu3 = check_mu3_exact(p, pts, beta) if do_sym else None
    neg = check_negation_exact(p, pts)
    print(f"  {label:22} |E|={len(pts):>5}  max|F|/sqrt p={mx:5.3f}  "
          f"mu3-sym={str(mu3):>5}  neg-sym={str(neg):>5}")
    print(f"  {'':22} |F|^2/p: near-int frac={fni:5.3f}  =1 frac={f1:5.3f}  "
          f"CV={cv:5.3f}  distinct(2dp)={nd}/{nv}")
    return mx, fni, f1, cv


def main():
    print("JOINT (x,y) INTERFERENCE PATTERN  F(a,b) = sum_P e_p(a x + b y)")
    print("=" * 78)
    print("CM curve y^2=x^3+7 (secp family, j=0)  vs  NON-CM control y^2=x^3+x+1 (j!=0).")
    print("Forced: CM has exact mu_3 symmetry F(a,b)=F(beta a,b); control must NOT.")
    print("Open: quantization of |F|^2/p (near-int / =1 mass) = discrete resonance?\n")
    for p in [307, 439, 607]:
        if not isprime(p) or p % 3 != 1:
            continue
        print(f"p = {p}:")
        analyze(p, 0, 7, "CM  y^2=x^3+7", do_sym=True)
        analyze(p, 1, 1, "non-CM y^2=x^3+x+1", do_sym=True)   # do_sym to CONFIRM it fails
        print()
    print("READ: mu3-sym True only for CM = the CM/GLV resonance (exact).  If near-int/=1")
    print("      frac is high for CM & low for control => CM QUANTIZES the (x,y) spectrum")
    print("      (discrete harmonic).  If both smooth (CV alike) => Weil-generic magnitude,")
    print("      resonance is ONLY the mu_3 symmetry.")


if __name__ == "__main__":
    main()
