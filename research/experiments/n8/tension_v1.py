"""THE TENSION, sharpened.

Covering [9,15] needs steps at multiplier 17/15 (m = 2), and an m=2 interval (15/s, 17/s) meets
[9,15] only if 17/s > 9, i.e. s < 17/9 = 1.889.  So combs used there must be SMALL.

But a small comb's m=1 interval is (7/s, 9/s) with 7/s > 7/1.889 = 3.70 -- it sits in the RIGHT half
of [1,7] and cannot help the left half.  Meanwhile s_7 = S ~ 7.45 covers (7/S, 9/S) = (0.94, 1.21) at
m=1 and then (15/S, 17/S) = (2.01, 2.28) at m=2, leaving a GAP (9/S, 15/S) = (1.21, 2.01).

WHO COVERS (9/S, 15/S)?  Only a comb with an interval meeting it: need (8m-1)/s < 15/S and
(8m+1)/s > 9/S.  Compute, for each candidate s, whether it can -- and whether that conflicts with
being small enough for [9,15]."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
import numpy as np
S=7.45
lo, hi = 9/S, 15/S
print(f"  S = {S}:  the gap between s_7's m=1 and m=2 intervals is ({lo:.4f}, {hi:.4f})\n")
print(f"  which readings s have ANY interval meeting that gap?")
ok=[]
for s in np.arange(1.01, 8.0, 0.01):
    hit=False
    for m in range(0,60):
        a,b=(8*m-1)/s,(8*m+1)/s
        if b>lo and a<hi: hit=True; break
    if hit: ok.append(s)
# summarise as intervals of s
runs=[]
for s in ok:
    if runs and s-runs[-1][1] < 0.015: runs[-1][1]=s
    else: runs.append([s,s])
print(f"    admissible s ranges: " + ", ".join(f"[{a:.3f},{b:.3f}]" for a,b in runs))
print(f"    of these, how many are < 17/9 = 1.889 (i.e. also usable in [9,15] at m=2)?")
small=[r for r in runs if r[0] < 17/9]
print(f"      {small}")
print()
print("  DIRECT TEST: force five small combs (all < 1.889) plus S, and see what R does.")
def Rdir(Sl, RMAX=60.0):
    c=[1.0]
    for s in Sl:
        k=0
        while (8*k+1)/s<=RMAX:
            r=(8*k+1)/s
            if r>=1.0: c.append(r)
            k+=1
    c.sort()
    for R in c:
        if all(1.0 <= (s*(R+1e-12))%8.0 <= 7.0 for s in Sl): return R
    return None
import random
rng=random.Random(11)
print(f"    {'profile':>52} {'R':>10}")
for _ in range(8):
    smalls=sorted(rng.uniform(1.02,1.888) for _ in range(5))
    prof=[1.0]+smalls+[S]
    print(f"    {str([round(x,3) for x in prof]):>52} {Rdir(prof):>10.5f}")
print()
print("  and for comparison, profiles with NO comb below 1.889:")
for _ in range(6):
    mids=sorted(rng.uniform(1.95,7.0) for _ in range(5))
    prof=[1.0]+mids+[S]
    print(f"    {str([round(x,3) for x in prof]):>52} {Rdir(prof):>10.5f}")
