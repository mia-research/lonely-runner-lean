"""
nonrep_units_ov_v1  --  the parity split of the four unit runners.

Pair rule: for a unit rho, bad(rho,t) has exactly one ODD and one EVEN element.
So the four units block at most 4 odds and at most 4 evens.  Define
    O = { x : the four units block ALL FOUR odd r },   o = |O|
    V = { x : the four units block ALL FOUR even r },  v = |V|
    U = O n V  (units block all of Z/8).

For rho0 in {2,6}, bad(rho0,t) is a coset of {0,4}: either both elements odd
({1,5},{3,7}) or both even ({0,4},{2,6}).  Hence
    BLOCKED(x)  =>  x in O  or  x in V,
so |S^c| <= o + v, and o + v < 1/2 would close rho0 in {2,6} outright.

This sweeps the four unit speeds and reports max(o+v).  Exact Fractions.
"""
from fractions import Fraction as F
import itertools, sys

ODD = frozenset({1,3,5,7}); EVEN = frozenset({0,2,4,6})
BAD = {(rho,t): frozenset(r for r in range(8) if (rho*r+t)%8 in (0,7))
       for rho in (1,3,5,7) for t in range(8)}
OMASK = {k: sum(1<<r for r in v if r%2==1) for k,v in BAD.items()}
EMASK = {k: sum(1<<r for r in v if r%2==0) for k,v in BAD.items()}
ALLO = sum(1<<r for r in ODD); ALLE = sum(1<<r for r in EVEN)

def ov(speeds):
    rhos = (1,3,5,7)
    pts = set()
    for e in speeds:
        for j in range(e): pts.add(F(j,e))
    p = sorted(pts); p.append(F(1))
    o = F(0); v = F(0); u = F(0)
    for a,b in zip(p,p[1:]):
        an,ad = a.numerator, a.denominator
        co = 0; ce = 0
        for e,rho in zip(speeds,rhos):
            t = ((e*an)//ad) % 8
            co |= OMASK[(rho,t)]; ce |= EMASK[(rho,t)]
        io = (co==ALLO); ie = (ce==ALLE)
        if io: o += b-a
        if ie: v += b-a
        if io and ie: u += b-a
    return o,v,u

QMAX = int(sys.argv[1]) if len(sys.argv)>1 else 7
best = []
for qs in itertools.product(range(QMAX+1), repeat=4):
    sp = tuple(8*q+r for q,r in zip(qs,(1,3,5,7)))
    if len(set(sp))!=4: continue
    o,v,u = ov(sp)
    best.append((o+v, o, v, u, sp))
best.sort(reverse=True)
print(f"unit speeds q<= {QMAX} (<= {8*QMAX+7}), {len(best)} tuples")
print(f"uniform-state expectation: o = v = 384/4096 = 3/32, o+v = 3/16 = 0.1875, u = 16/4096 = 1/256")
print("\nTOP 15 by o+v:")
for s,o,v,u,sp in best[:15]:
    print(f"   o+v = {str(s):>14} = {float(s):.6f}   o={str(o):>12} v={str(v):>12} u={str(u):>10}  speeds {sp}")
print(f"\nMAX o+v over the sweep = {best[0][0]} = {float(best[0][0]):.6f}")
print(f"number of tuples with o+v >= 1/2 : {sum(1 for s,*_ in best if s>=F(1,2))}")
print(f"MAX u = {max(b[3] for b in best)}")
print(f"\nBOTTOM 3: " + ", ".join(f"{float(s):.6f}@{sp}" for s,o,v,u,sp in best[-3:]))
