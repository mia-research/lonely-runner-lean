"""Is 16 about n=8?  16 = 2n, and floor(R/n) counts complete laps of d_min, so R < 2n says
'at most one complete lap'.  Test whether that is order-8-specific or general.

R_n = min{ R >= 1 : dist(s_i R, n Z) >= 1 for all i }.  Exact endpoint enumeration.
"""
from fractions import Fraction as F
import random

def clear(S, x, n):
    for s in S:
        y = s*x
        if abs(y - n*round(y/n)) < 1: return False
    return True

def R_exact(S, n, hi):
    c = {F(1)}
    for s in S:
        k = 0
        while F(n*k+1,1)/s <= hi:
            for num in (n*k+1, n*k-1):
                if num > 0:
                    x = F(num,1)/s
                    if 1 <= x <= hi: c.add(x)
            k += 1
    for x in sorted(c):
        if clear(S, x, n): return x
    return None

rng = random.Random(20260919)
print(f"{'n':>3} {'runners':>8} {'profiles':>9} {'max R':>12} {'max R/n':>9} {'laps':>6} {'2n':>5}")
for n in range(4, 11):
    k = n - 1
    mx = None; marg = None; tot = 0; none = 0
    for _ in range(1500):
        # rational readings (the case where band 1 can matter), s_1 = 1
        d = sorted(rng.sample(range(1, 4000), k))
        S = [F(x, d[0]) for x in d]
        if len(set(S)) != k or min(S) != 1: continue
        tot += 1
        R = R_exact(S, n, F(4*n))
        if R is None: none += 1; continue
        if mx is None or R > mx: mx, marg = R, d
    laps = int(mx // n)
    print(f"{n:>3} {n:>8} {tot:>9,} {float(mx):>12.4f} {float(mx)/n:>9.4f} {laps:>6} {2*n:>5}"
          + ("   R < 2n" if mx < 2*n else "   R >= 2n  <-- more than one lap"))
