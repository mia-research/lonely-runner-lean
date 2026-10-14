"""ok_transit_duration_v1 — duration vs count along a one-runner transit.

n = 8 individual isolation.  For each position on a transit, report BOTH
observables for every runner: the COUNT of good components and the DURATION
(measure) of the good set, per period, on the reduced integer configuration.

Purpose: count is scaled by the denominator of the moved speed, so counts at
different positions of a transit are not comparable.  Duration is a fraction of
the period and is comparable throughout.

BSM: boundary points and open-cell midpoints are evaluated separately, so
isolated boundary witnesses (gap exactly 1/n) are not lost.  Exact Fractions.
"""
from fractions import Fraction as F
from math import gcd

def prim(vs):
    D = 1
    for v in vs: D = D*v.denominator//gcd(D, v.denominator)
    ints = [int(v*D) for v in vs]
    g = 0
    for a in ints[1:]: g = gcd(g, abs(a-ints[0]))
    g = g or 1
    return [ (a-ints[0])//g for a in ints ]

def lonely(ds, t, n=8):
    for d in ds:
        x = (d*t) % 1
        if min(x, 1-x) < F(1,n): return False
    return True

def comps_and_measure(speeds, i, n=8):
    u = speeds[i]
    ds = sorted({abs(u-v) for j,v in enumerate(speeds) if j!=i and v!=u})
    if not ds: return 0, F(0)
    pts = {F(0)}
    for d in ds:
        for k in range(0, d+1):
            for x in (F(k,d)+F(1,n*d), F(k,d)-F(1,n*d)):
                if 0 <= x < 1: pts.add(x)
    pts = sorted(pts)
    segs=[]
    for idx,a in enumerate(pts):
        if lonely(ds,a,n): segs.append((a,a))
        b = pts[idx+1] if idx+1 < len(pts) else F(1)
        if b>a and lonely(ds,(a+b)/2,n): segs.append((a,b))
    merged=[]
    for s in segs:
        if merged and s[0] <= merged[-1][1]: merged[-1]=(merged[-1][0], max(merged[-1][1], s[1]))
        else: merged.append(s)
    return len(merged), sum(b-a for a,b in merged)

print("AP (1..8), runner 8 transits 8 -> 9 in steps of 1/24")
print(f"{'r8':>8} {'denom':>6} {'min count':>10} {'min density':>12} {'r1 count':>9} {'r1 dens':>9}")
rows=[]
for k in range(0, 25):
    r8 = 8 + F(k,24)
    vs = [F(x) for x in (1,2,3,4,5,6,7)] + [r8]
    sp = prim(vs)
    cs=[]; ms=[]
    for i in range(8):
        c,m = comps_and_measure(sp, i)
        cs.append(c); ms.append(m)
    rows.append((r8, min(cs), min(ms)))
    print(f"{str(r8):>8} {r8.denominator:>6} {min(cs):>10} {float(min(ms)):>12.6f} {cs[0]:>9} {float(ms[0]):>9.6f}")

cnt=[r[1] for r in rows]; den=[float(r[2]) for r in rows]
print()
print(f"min count  : min {min(cnt)}  max {max(cnt)}  ratio {max(cnt)/max(1,min(cnt)):.1f}x")
print(f"min density: min {min(den):.6f}  max {max(den):.6f}  ratio {max(den)/max(1e-12,min(den)):.2f}x")
