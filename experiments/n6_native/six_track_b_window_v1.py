#!/usr/bin/env python3
"""Track B, first measure: BHK Corollary 5 in framework form (LRC.SpecN.lonely_six_of_slow_window).
For S = {v1<...<v5} (primitive SixResidual), does some clear lap of v3, the interval
[(k+1/6)/v3, (k+5/6)/v3] of length 2/(3 v3), keep v1 and v2 clear throughout?  If so, the two-flank
window names a lonely instant in it (v4, v5 faster than v3). Integer speeds: k < v3 suffices
(period 1). Exact Fractions."""
import sys, math, importlib.util
from itertools import combinations
from fractions import Fraction as F
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)

def clear_throughout(v, lo, hi):
    # v*[lo,hi] inside some [m+1/6, m+5/6]
    a, b = v * lo, v * hi
    m = a.numerator // a.denominator
    return a >= m + F(1, 6) and b <= m + F(5, 6)

def corollary5(S):
    v1, v2, v3, v4, v5 = S
    for k in range(v3):
        lo, hi = F(6 * k + 1, 6 * v3), F(6 * k + 5, 6 * v3)
        if clear_throughout(v1, lo, hi) and clear_throughout(v2, lo, hi):
            return True
    return False

HI = int(sys.argv[1]); tot = ok = 0; left = []
for S in combinations(range(1, HI + 1), 5):
    if math.gcd(*S) != 1 or not r.six_residual(S): continue
    tot += 1
    if corollary5(S): ok += 1
    else: left.append(S)
print(f"HI={HI}: residual={tot}; BHK Cor.5 window settles {ok}; left {len(left)}")
print("  first left:", left[:10])
