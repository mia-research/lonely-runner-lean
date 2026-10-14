"""Where the sharp window falls short: how close is W*e to 1?

The criterion W > 1/e is sufficient, not necessary: a window of width W <= 1/e can still contain
a lattice point if it sits favourably.  So measure the shortfall W*e, and see how much of the
uncovered part is only just short.
"""
import math
from itertools import combinations
from fractions import Fraction as F
from collections import Counter

def norm(x):
    fr = x - math.floor(x); return min(fr, 1 - fr)

def max_gap(ds, _c={}):
    key = tuple(ds)
    if key in _c: return _c[key]
    pts = {F(0), F(1)}
    for d in ds:
        for k in range(0, d + 2):
            for off in (F(-1,5), F(1,5)):
                t = (F(k) + off) / F(d)
                if 0 <= t <= 1: pts.add(t)
    P = sorted(pts); best = F(0)
    for i in range(len(P)-1):
        lo, hi = P[i], P[i+1]
        if all(norm(F(d)*((lo+hi)/2)) >= F(1,5) for d in ds) and hi-lo > best: best = hi-lo
    _c[key] = best
    return best

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

def in_residue(c):
    e = c[-1]
    return any(d % 5 == 0 for d in c[:-1]) and e > 4*c[0] and e > 15

def n_open(c):
    e = c[-1]; M = 5*e
    return sum(1 for j in range(e) if all(e <= (d*(5*j+1)) % M <= 4*e for d in c))

hi = 36
sets = [c for c in combinations(range(1, hi+1), 4) if prim(c) and in_residue(c)]
buckets = Counter(); opens = {}
for c in sets:
    e = c[-1]; W = max_gap(c[:-1])
    x = float(W * e)
    b = min(int(x * 4), 12)      # quarter-width buckets of W*e
    buckets[b] += 1
    opens.setdefault(b, []).append(n_open(c))
print(f"residue [1,{hi}]: {len(sets)} sets   (criterion needs W*e > 1, i.e. bucket >= 4)")
print(f"{'W*e range':>14} {'sets':>8} {'mean #openings':>16} {'min #open':>10}")
for b in sorted(buckets):
    lo = b/4; hi_ = (b+1)/4
    o = opens[b]
    lab = f"[{lo:.2f},{hi_:.2f})" if b < 12 else ">=3.00"
    print(f"{lab:>14} {buckets[b]:>8} {sum(o)/len(o):>16.2f} {min(o):>10}")
print()
cov = sum(v for b,v in buckets.items() if b >= 4)
near = sum(v for b,v in buckets.items() if 2 <= b < 4)
print(f"   covered (W*e > 1)          : {cov} ({100*cov/len(sets):.1f}%)")
print(f"   near miss (0.5 < W*e <= 1) : {near} ({100*near/len(sets):.1f}%)")
print(f"   far short (W*e <= 0.5)     : {len(sets)-cov-near} ({100*(len(sets)-cov-near)/len(sets):.1f}%)")
