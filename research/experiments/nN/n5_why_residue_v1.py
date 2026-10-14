"""Why does isolation still occur in the residue, and what is different about it?

The criteria that PROVE a set all deliver one wide lonely interval: P2 names the last opening,
P1' names e*s or k*e+1, P4 needs W > 1/e.  So the residue is exactly the sets whose lonely set
has NO wide interval.  Yet they are all lonely (min 2 openings).  So isolation there must come
from MANY NARROW pieces, one of which the opening lattice happens to hit.

Measured, residue vs proved: total measure |L|, number of components, largest component W,
and W*e.
"""
import math
from itertools import combinations
from fractions import Fraction as F

def norm(x):
    fr = x - math.floor(x); return min(fr, 1 - fr)

def comps(ds, _c={}):
    key = tuple(ds)
    if key in _c: return _c[key]
    pts = {F(0), F(1)}
    for d in ds:
        for k in range(0, d + 2):
            for off in (F(-1,5), F(1,5)):
                t = (F(k) + off) / F(d)
                if 0 <= t <= 1: pts.add(t)
    P = sorted(pts); out = []
    for i in range(len(P)-1):
        lo, hi = P[i], P[i+1]
        if all(norm(F(d)*((lo+hi)/2)) >= F(1,5) for d in ds): out.append((lo, hi))
    # merge touching
    merged = []
    for lo, hi in out:
        if merged and merged[-1][1] == lo: merged[-1] = (merged[-1][0], hi)
        else: merged.append((lo, hi))
    _c[key] = merged
    return merged

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

def n_open(c):
    e = c[-1]; M = 5*e
    return sum(1 for j in range(e) if all(e <= (d*(5*j+1)) % M <= 4*e for d in c))

hi = 34
rows = {"PROVED": [], "RESIDUE": []}
for c in combinations(range(1, hi+1), 4):
    if not prim(c): continue
    e = c[-1]; nf = c[:-1]
    P1 = all(d % 5 != 0 for d in nf); P2 = e <= 4*c[0]; P3 = e <= 15
    cs = comps(nf)
    W = max((b-a for a,b in cs), default=F(0))
    P4 = W > F(1,e)
    key = "PROVED" if (P1 or P2 or P3 or P4) else "RESIDUE"
    meas = sum(b-a for a,b in cs)
    rows[key].append((float(meas), len(cs), float(W), float(W*e), n_open(c), e))

print(f"{'class':>9} {'sets':>8} {'mean |L|':>9} {'mean #comps':>12} {'mean W':>9} {'mean W*e':>9} {'mean #open':>11} {'mean e':>8}")
for k, v in rows.items():
    n = len(v)
    print(f"{k:>9} {n:>8} {sum(r[0] for r in v)/n:>9.4f} {sum(r[1] for r in v)/n:>12.2f} "
          f"{sum(r[2] for r in v)/n:>9.4f} {sum(r[3] for r in v)/n:>9.3f} "
          f"{sum(r[4] for r in v)/n:>11.2f} {sum(r[5] for r in v)/n:>8.1f}")
print()
print("=== the discriminator: is |L| smaller in the residue, or just more fragmented? ===")
for k, v in rows.items():
    n = len(v)
    frag = sum(r[0]/r[1] for r in v)/n      # mean component width
    print(f"   {k:>8}: mean |L| = {sum(r[0] for r in v)/n:.4f}   mean component width = {frag:.4f}"
          f"   mean W/|L| = {sum(r[2]/r[0] for r in v if r[0]>0)/n:.4f}")
