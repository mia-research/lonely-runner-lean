r"""
nonrep_primitive_min_v1  --  min |S| over PRIMITIVE base tuples (gcd(E_non)=1),
excluding the single exceptional tuple {1,3,5,7,4}.  This is the gap (H) that the
Reduction Theorem leaves open; the number below is how much slack it has empirically.
"""
from math import gcd
import itertools, sys
from fractions import Fraction as F
from nonrep_sweep_v2 import safe_num_den

QMAX = int(sys.argv[1])
for rho0 in (2, 4, 6):
    rhos = (1, 3, 5, 7, rho0)
    mn = None; n_le_half = 0; tot = 0
    for qs in itertools.product(range(QMAX + 1), repeat=5):
        sp = tuple(8 * q + r for q, r in zip(qs, rhos))
        if len(set(sp)) != 5: continue
        g = 0
        for e in sp: g = gcd(g, e)
        if g != 1: continue
        if sorted(sp) == [1, 3, 4, 5, 7]: continue
        tot += 1
        n, d = safe_num_den(sp, rhos)
        if 2 * n <= d: n_le_half += 1; print("   *** |S| <= 1/2 at", sp, F(n, d))
        if mn is None or n * mn[1] < mn[0] * d: mn = (n, d, sp)
    print(f"rho0={rho0}  q<= {QMAX}: {tot} primitive tuples (excluding {{1,3,5,7,4}})")
    print(f"   min |S| = {F(mn[0],mn[1])} = {mn[0]/mn[1]:.6f} at {mn[2]}")
    print(f"   number with |S| <= 1/2 : {n_le_half}")
    sys.stdout.flush()
