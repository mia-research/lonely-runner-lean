"""Why isolation occurs: the openings EQUIDISTRIBUTE in the lonely set.

|L| ~ 0.21 ~ (3/5)^3 for both the proved and residue classes, and #openings ~ |L| * e.
So isolation is not a width phenomenon at all -- it is a counting one.  The proved criteria all
name ONE point or ONE wide interval; the residue is exactly where no such point is named, yet
the count still delivers ~|L|*e openings.

Test: the discrepancy D = #openings - |L|*e.  If |L| is bounded below and D is bounded, then
#openings >= 1 for e past an explicit bound -- which is the proof shape the residue needs.
"""
import math
from itertools import combinations
from fractions import Fraction as F

def norm(x):
    fr = x - math.floor(x); return min(fr, 1-fr)

def measure(ds, _c={}):
    key = tuple(ds)
    if key in _c: return _c[key]
    pts = {F(0), F(1)}
    for d in ds:
        for k in range(0, d+2):
            for off in (F(-1,5), F(1,5)):
                t = (F(k)+off)/F(d)
                if 0 <= t <= 1: pts.add(t)
    P = sorted(pts); m = F(0)
    for i in range(len(P)-1):
        lo, hi = P[i], P[i+1]
        if all(norm(F(d)*((lo+hi)/2)) >= F(1,5) for d in ds): m += hi-lo
    _c[key] = m
    return m

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

def n_open(c):
    e = c[-1]; M = 5*e
    return sum(1 for j in range(e) if all(e <= (d*(5*j+1)) % M <= 4*e for d in c))

hi = 34
res = []
for c in combinations(range(1, hi+1), 4):
    if not prim(c): continue
    e = c[-1]; nf = c[:-1]
    P1 = all(d % 5 != 0 for d in nf); P2 = e <= 4*c[0]; P3 = e <= 15
    m = measure(nf)
    # P4 needs the largest interval; approximate membership by excluding proved ones only
    if P1 or P2 or P3: continue
    res.append((c, e, float(m), n_open(c)))
print(f"non-P1'/P2/P3 sets in [1,{hi}]: {len(res)}")
D = [o - m*e for _, e, m, o in res]
print(f"   discrepancy D = #open - |L|*e :  mean {sum(D)/len(D):+.3f}   min {min(D):+.3f}   max {max(D):+.3f}")
mins = min(m for _, _, m, _ in res)
print(f"   minimum |L| over the class    :  {mins:.4f}")
worst = min(res, key=lambda r: r[2])
print(f"   at {worst[0]}  (|L| = {worst[2]:.4f}, e = {worst[1]}, openings = {worst[3]})")
print()
print("   If |L| >= L0 and D >= -Dmax then #open >= L0*e - Dmax >= 1 once e >= (1+Dmax)/L0:")
L0 = mins; Dmax = -min(D)
print(f"      L0 = {L0:.4f}   Dmax = {Dmax:.3f}   =>  e >= {(1+Dmax)/L0:.1f}")
print()
print("=== is the discrepancy really bounded, or does it grow with e? ===")
from collections import defaultdict
by = defaultdict(list)
for _, e, m, o in res: by[e//5*5].append(o - m*e)
print(f"{'e bucket':>10} {'sets':>7} {'min D':>8} {'max D':>8}")
for b in sorted(by):
    v = by[b]
    print(f"{b:>10} {len(v):>7} {min(v):>8.3f} {max(v):>8.3f}")
