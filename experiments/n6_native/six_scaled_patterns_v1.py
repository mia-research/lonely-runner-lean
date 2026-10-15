#!/usr/bin/env python3
"""Scaled blocking patterns. P in {(1,3,4,5), (1,2,3,5)} (the coarse blocking patterns at order six).
(1) L(P): lonely set of P at threshold 1/6 in [0,1), exact components.
(2) For S = kP + {e} (k >= 1, e > 5k, gcd(kP + {e}) = 1): the largest flank e fails iff no opening
    t_j = (6j+1)/(6e), j < e, has k t_j mod 1 in L(P). Lists every failing (k, e) for k <= 8, e <= 300,
    the phase of the grid, and whether S is a primitive SixResidual set.
Exact Fractions."""
import math, importlib.util
from fractions import Fraction as F
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
def lonely_set(R):
    ivs = [(F(0), F(1))]
    for p in R:
        bands = [(F(6*k + 1, 6*p), F(6*k + 5, 6*p)) for k in range(p)]
        ivs = [(max(a, c), min(b, d)) for a, b in ivs for c, d in bands if max(a, c) <= min(b, d)]
    return sorted(ivs)
def inL(x, L):
    x = x - (x.numerator // x.denominator)
    return any(a <= x <= b for a, b in L)
for P in [(1, 3, 4, 5), (1, 2, 3, 5)]:
    L = lonely_set(P)
    print(f"P={P}: L(P) components (measure {sum(b-a for a,b in L)}):", [(str(a), str(b)) for a, b in L])
    fails = []
    for k in range(1, 9):
        for e in range(5 * k + 1, 301):
            S = tuple(sorted(set(k * p for p in P) | {e}))
            if len(S) != 5 or S[-1] != e or math.gcd(*S) != 1: continue
            if not any(inL(F(k * (6 * j + 1), 6 * e), L) for j in range(e)):
                fails.append((k, e, math.gcd(k, e), r.six_residual(S)))
    print(f"  failing (k, e, gcd(k,e), in SixResidual) for k <= 8, e <= 300: {fails}")
