"""Total coverage with P6 added."""
import math
from itertools import combinations
from fractions import Fraction as F

def norm(x):
    fr = x - math.floor(x); return min(fr, 1-fr)

def max_gap(ds, _c={}):
    key = tuple(ds)
    if key in _c: return _c[key]
    pts = {F(0), F(1)}
    for d in ds:
        for k in range(0, d+2):
            for off in (F(-1,5), F(1,5)):
                t = (F(k)+off)/F(d)
                if 0 <= t <= 1: pts.add(t)
    P = sorted(pts); best = F(0)
    for i in range(len(P)-1):
        lo, hi = P[i], P[i+1]
        if all(norm(F(d)*((lo+hi)/2)) >= F(1,5) for d in ds) and hi-lo > best: best = hi-lo
    _c[key] = best
    return best

def k_ok(ds, ep, k, n=5):
    for d in ds:
        if d == ep: continue
        c, s = divmod(d, ep)
        r = (d*k + c) % n
        if r in (1,2,3): continue
        if r == n-1 and s == 0: continue
        return False
    return True

def P6(ds, n=5):
    return any(ep % n == 0 and any(k_ok(ds, ep, k, n) for k in range(1, n)) for ep in ds)

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

for hi in (30, 40):
    tot = 0; cov = {k: 0 for k in ("P1'","P2","P3","P4","P5","P6","union")}; rem = 0
    left = []
    for c in combinations(range(1, hi+1), 4):
        if not prim(c): continue
        tot += 1; e = c[-1]; nf = c[:-1]
        a = all(d % 5 != 0 for d in nf); b = e <= 4*c[0]; d_ = e <= 15
        f = max_gap(nf) > F(1, e); g = all(d % 5 == 0 for d in nf); h = P6(c)
        for kk, v in (("P1'",a),("P2",b),("P3",d_),("P4",f),("P5",g),("P6",h)):
            if v: cov[kk] += 1
        if a or b or d_ or f or g or h: cov["union"] += 1
        else:
            rem += 1
            if len(left) < 8: left.append(c)
    print(f"n=5, card 4, primitive subsets of [1,{hi}]: {tot} sets")
    for kk in ("P1'","P2","P3","P4","P5","P6"):
        print(f"    {kk:>4} : {cov[kk]:>8}  ({100*cov[kk]/tot:5.2f}%)")
    print(f"    UNION: {cov['union']:>8}  ({100*cov['union']/tot:5.2f}%)")
    print(f"    residue left: {rem:>8}  ({100*rem/tot:5.2f}%)   e.g. {left[:5]}")
    print()
