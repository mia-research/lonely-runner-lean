"""
nonrep_sweep_v2  --  same exact computation as v1, integer-only inner loop.

Common denominator D = lcm(e_1,e_3,e_5,e_7,e_rho0).  Breakpoints are the integers
k*D/e.  On a cell starting at integer p, floor(e*x) = (e*p)//D exactly.
Measure of S = (sum of safe cell widths)/D, an exact rational.
No floating point in any decision.
"""
from math import lcm
import itertools, sys
from fractions import Fraction as F

MASK = {(rho, t): sum(1 << r for r in range(8) if (rho * r + t) % 8 in (0, 7))
        for rho in range(1, 8) for t in range(8)}
ALL = 255

def safe_num_den(speeds, rhos):
    D = lcm(*speeds)
    pts = set()
    for e in speeds:
        s = D // e
        pts.update(range(0, D, s))
    p = sorted(pts); p.append(D)
    tot = 0
    mk = [[MASK[(rho, t)] for t in range(8)] for rho in rhos]
    for i in range(len(p) - 1):
        a = p[i]; cov = 0
        for j in range(5):
            cov |= mk[j][((speeds[j] * a) // D) % 8]
        if cov != ALL:
            tot += p[i + 1] - a
    return tot, D

def safe_measure(speeds, rhos):
    n, d = safe_num_den(speeds, rhos)
    return F(n, d)

if __name__ == "__main__":
    QMAX = int(sys.argv[1])
    RHO0 = [int(a) for a in sys.argv[2].split(",")] if len(sys.argv) > 2 else [2, 4, 6]
    for rho0 in RHO0:
        rhos = (1, 3, 5, 7, rho0)
        cnt = 0; bad = []; mn = None
        for qs in itertools.product(range(QMAX + 1), repeat=5):
            speeds = tuple(8 * q + r for q, r in zip(qs, rhos))
            if len(set(speeds)) != 5: continue
            cnt += 1
            n, d = safe_num_den(speeds, rhos)
            if 2 * n <= d:                      # |S| <= 1/2, exact integer test
                bad.append((F(n, d), speeds))
            if mn is None or n * mn[1] < mn[0] * d:
                mn = (n, d, speeds)
        bad.sort()
        print(f"rho0={rho0}  q<= {QMAX}  speeds <= {8*QMAX+rho0 if rho0>7 else 8*QMAX+7}  "
              f"tuples={cnt}")
        print(f"   min |S| = {F(mn[0],mn[1])} = {mn[0]/mn[1]:.6f} at {mn[2]}")
        print(f"   tuples with |S| <= 1/2 : {len(bad)}")
        for m, s in bad:
            g = 0
            for e in s: g = __import__('math').gcd(g, e)
            base = tuple(e // g for e in s)
            print(f"      |S|={m}  speeds={s}  gcd={g}  reduced={base}"
                  f"  {'= gcd * {1,3,5,7,4}' if sorted(base)==[1,3,4,5,7] else '  *** NOT A DILATE ***'}")
        sys.stdout.flush()
