"""Sharp window: the LARGEST interval of the lonely set, computed exactly.

L = { t in [0,1) : ||d t|| >= 1/5 for every NON-FLANK d }.  Its complement is a union of OPEN
intervals ((k - 1/5)/d, (k + 1/5)/d), so L is a union of closed intervals whose endpoints are
exactly the points (k +- 1/5)/d.  Collect them, sweep, take the widest surviving interval W.

Criterion (the proved gap lemma): if W > 1/e then some flank opening of e is lonely.
This replaces the Lipschitz window 2(S - 1/5)/d_max, which is only a lower bound on W.
"""
import math
from itertools import combinations
from fractions import Fraction as F

def norm(x):
    fr = x - math.floor(x); return min(fr, 1 - fr)

def max_gap(ds, _c={}):
    """Largest closed interval of L, exactly."""
    key = tuple(ds)
    if key in _c: return _c[key]
    pts = {F(0), F(1)}
    for d in ds:
        for k in range(0, d + 2):
            for off in (F(-1,5), F(1,5)):
                t = (F(k) + off) / F(d)
                if 0 <= t <= 1: pts.add(t)
    P = sorted(pts)
    best = F(0)
    for i in range(len(P) - 1):
        lo, hi = P[i], P[i+1]
        mid = (lo + hi) / 2
        if all(norm(F(d) * mid) >= F(1,5) for d in ds):
            if hi - lo > best: best = hi - lo
    _c[key] = best
    return best

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

def in_residue(c):
    e = c[-1]
    return any(d % 5 == 0 for d in c[:-1]) and e > 4*c[0] and e > 15

def works(c):
    e = c[-1]; M = 5*e
    return any(all(e <= (d*(5*j+1)) % M <= 4*e for d in c) for j in range(e))

hi = 40
sets = [c for c in combinations(range(1, hi+1), 4) if prim(c) and in_residue(c)]
from collections import Counter
res = Counter(); cov = Counter(); bad = []
for c in sets:
    e = c[-1]; nf = c[:-1]
    k5 = sum(1 for d in nf if d % 5 == 0)
    res[k5] += 1
    W = max_gap(nf)
    if W > F(1, e):
        cov[k5] += 1
        if not works(c) and len(bad) < 3: bad.append(c)   # soundness check
print(f"residue sets in [1,{hi}]: {len(sets)}")
print(f"{'# inner 5-mults':>16} {'sets':>8} {'SHARP window closes':>21} {'share':>8}")
for k in sorted(res):
    print(f"{k:>16} {res[k]:>8} {cov[k]:>21} {100*cov[k]/res[k]:>7.1f}%")
tot = sum(res.values()); tc = sum(cov.values())
print(f"{'TOTAL':>16} {tot:>8} {tc:>21} {100*tc/tot:>7.1f}%")
print(f"\nsoundness: sets the criterion claims but that actually fail = {len(bad)} {bad}")
