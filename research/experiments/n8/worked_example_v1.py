"""A single complete cascade at n=8, traced, for the submission paper's worked example.
Exact rational arithmetic throughout.  Wanted: 2-4 moves, small integers, a clean final (e,k)."""
from fractions import Fraction as F
from itertools import combinations
import math
n = 8
def circ(x):
    fl = x - (x.numerator // x.denominator)
    return min(fl, 1 - fl)
def trace(ds):
    m = min(ds); t = F(1, n*m); steps = []
    for _ in range(40):
        inway = [d for d in ds if circ(F(d)*t) < F(1,n)]
        if not inway:
            return steps, t, True
        best = None; setter = None; lap = None
        for d in inway:
            k = math.ceil(F(d)*t - F(1,n))
            op = (F(k) + F(1,n)) / F(d)
            while op < t: k += 1; op = (F(k)+F(1,n))/F(d)
            if best is None or op > best: best, setter, lap = op, d, k
        steps.append((t, [ (d, F(d)*t, circ(F(d)*t)) for d in ds ], inway, setter, lap, best))
        t = best
    return steps, t, False
# search for a clean example
best = None
for c in combinations(range(1,17), 7):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    if g != 1: continue
    st, t, done = trace(c)
    if done and 2 <= len(st) <= 3 and max(c) <= 12:
        score = (len(st), max(c), t.denominator)
        if best is None or score < best[0]: best = (score, c, st, t)
score, ds, steps, tfin = best
print(f"difference set ds = {ds}")
print(f"d_min = {min(ds)}   bound t0 = 1/(8*d_min) = {F(1,8*min(ds))}")
print()
for i,(t, readings, inway, setter, lap, nxt) in enumerate(steps):
    print(f"step {i}:  t = {t}")
    print(f"   readings d*t : " + ", ".join(f"{d}->{v} (dist {c})" for d,v,c in readings))
    print(f"   in the way   : {inway}")
    print(f"   setter       : {setter} at lap {lap};  its opening ({lap}+1/8)/{setter} = {nxt}")
    print()
print(f"fixed point t = {tfin}")
print(f"   readings: " + ", ".join(f"{d}->{F(d)*tfin} (dist {circ(F(d)*tfin)})" for d in ds))
print(f"   every distance >= 1/8 = {F(1,8)}   -> LONELY")
# express as a flank opening (e,k)
for e in ds:
    k = tfin*e - F(1,8)
    if k.denominator == 1 and k >= 0:
        print(f"   as a flank opening: e = {e}, k = {k},  t = (k + 1/8)/e = {(F(k)+F(1,8))/F(e)}")
