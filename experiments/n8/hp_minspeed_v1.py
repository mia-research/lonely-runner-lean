r"""
Does o > 1/3 force a SMALL speed?  Both observed exceptions have e_1 = 1.

o = |O|, O = {x : rho -> s_rho * rho is a bijection of (Z/8)^*}, s_rho = odd member of
{floor(e_rho x), floor(e_rho x)+1} mod 8.  When e_1 = 1 we have t_1 = 0 throughout
[0,1), so s_1 = 1 is FROZEN and one degree of freedom is removed -- the natural reason
for o to be large.  This measures max o as a function of the minimum speed.
Exact arithmetic, entry-point evaluation.
"""
from fractions import Fraction as F
from math import gcd
from functools import reduce
import itertools, sys

def cells(S):
    pts={F(0),F(1)}
    for e in S:
        for j in range(1,e+1):
            q=F(j,e)
            if 0<q<1: pts.add(q)
    p=sorted(pts); return list(zip(p,p[1:]))
def fl(e,a): v=e*a; return v.numerator//v.denominator
def bad(e,t): return frozenset(r for r in range(8) if (e*r+t)%8 in (0,7))
ODD=frozenset({1,3,5,7}); FULL=frozenset(range(8))
def o_u(U4):
    o=F(0); u=F(0)
    for a,b in cells(U4):
        cov=set()
        for e in U4: cov|=bad(e,fl(e,a))
        if ODD<=cov: o+=b-a
        if cov==FULL: u+=b-a
    return o,u

QMAX=int(sys.argv[1]) if len(sys.argv)>1 else 6
best={}
for qs in itertools.product(range(0,QMAX+1),repeat=4):
    U4=tuple(8*q+r for q,r in zip(qs,(1,3,5,7)))
    if len(set(U4))!=4: continue
    if reduce(gcd,U4)!=1: continue
    o,u=o_u(list(U4))
    mn=min(U4)
    if mn not in best or o>best[mn][0]: best[mn]=(o,u,U4)
print(f"max o as a function of the MINIMUM speed (primitive, q <= {QMAX}):")
print(f"   {'min e':>6} {'max o':>14} {'max o~':>9} {'u there':>10} {'tuple':>22} {'>1/3?':>6}")
for mn in sorted(best):
    o,u,U4=best[mn]
    print(f"   {mn:>6} {str(o):>14} {float(o):>9.4f} {str(u):>10} {str(U4):>22} {str(o>F(1,3)):>6}")
print(f"\n   max o over tuples with min speed >= 3: "
      f"{max((best[m][0] for m in best if m>=3), default=None)}"
      f" = {float(max((best[m][0] for m in best if m>=3))):.4f}   (1/3 = 0.3333)")
