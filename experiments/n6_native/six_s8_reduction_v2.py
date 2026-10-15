#!/usr/bin/env python3
"""As six_s8_reduction_v1.py, enumerating §8 residual sets directly (v1 < v2 < v3 <= 3 v1 < ... ) up to
HI, primitive, SixResidual. Reports exceptions (walk(S) != walk({v1,v4,v5})) per bucket of v5 and lists
them, with the step at which a slow element is in the way."""
import sys, math, importlib.util
from fractions import Fraction as F
from collections import Counter
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
HI = int(sys.argv[1])
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
def walk(S):
    t = F(1, 6 * S[0]); times = [t]
    while True:
        blk = [d for d in S if cd(d * t) < F(1, 6)]
        if not blk: return times
        t = max(F(6 * round(d * t) + 1, 6 * d) for d in blk); times.append(t)
n = 0; exc = []; byb = Counter(); tot = Counter()
for v1 in range(1, HI):
    for v2 in range(v1 + 1, min(3 * v1, HI) + 1):
        for v3 in range(v2 + 1, min(3 * v1, HI) + 1):
            for v4 in range(v3 + 1, HI + 1):
                for v5 in range(v4 + 1, HI + 1):
                    S = (v1, v2, v3, v4, v5)
                    if math.gcd(*S) != 1 or not r.six_residual(S): continue
                    n += 1; tot[(v5 - 1) // 12] += 1
                    if walk(S) != walk((v1, v4, v5)):
                        exc.append(S); byb[(v5 - 1) // 12] += 1
print(f"HI={HI}: §8 residual sets={n}; exceptions={len(exc)}")
for b in sorted(tot): print(f"  v5 in [{12*b+1},{12*b+12}]: sets={tot[b]}, exceptions={byb[b]}")
print("  exceptions:", exc[:30])
