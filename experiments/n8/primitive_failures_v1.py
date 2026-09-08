r"""
Are the a-priori failures confined, once dilation is quotiented out?

o and u are DILATION INVARIANTS (proved: the safe/blocked structure at x for lambda*E
equals that at lambda*x for E, and safety is invariant under x -> x+1 because the free
residue r absorbs the shift; so |.| is preserved).  Hence o(E_4) = o(E_4 / gcd(E_4)),
and every unit 4-tuple reduces to a PRIMITIVE one.

The rho0 = 4 fibre closes a priori when u = 0 or u + 2o <= 1/2.  This lists the
PRIMITIVE unit 4-tuples that fail that test, by max speed, to see whether they are a
finite set.  Exact rational arithmetic; entry-point evaluation only.
"""
from fractions import Fraction as F
from math import gcd
import itertools, sys
from functools import reduce

def cells(S):
    pts={F(0),F(1)}
    for e in S:
        for j in range(1,e+1):
            q=F(j,e)
            if 0<q<1: pts.add(q)
    p=sorted(pts); return list(zip(p,p[1:]))
def fl(e,a): v=e*a; return v.numerator//v.denominator
def bad(e,t): return frozenset(r for r in range(8) if (e*r+t)%8 in (0,7))
FULL=frozenset(range(8)); ODD=frozenset({1,3,5,7})
def o_u(U4):
    o=F(0); u=F(0)
    for a,b in cells(U4):
        cov=set()
        for e in U4: cov|=bad(e,fl(e,a))
        if ODD<=cov: o+=b-a
        if cov==FULL: u+=b-a
    return o,u

QMAX=int(sys.argv[1]) if len(sys.argv)>1 else 8
fails=[]; nprim=0
for qs in itertools.product(range(0,QMAX+1),repeat=4):
    U4=tuple(8*q+r for q,r in zip(qs,(1,3,5,7)))
    if len(set(U4))!=4: continue
    if reduce(gcd,U4)!=1: continue          # dilation-reduce: primitive only
    nprim+=1
    o,u=o_u(list(U4))
    if u!=0 and u+2*o>F(1,2): fails.append((max(U4),u+2*o,U4,o,u))
fails.sort()
print(f"PRIMITIVE unit 4-tuples with q <= {QMAX}: {nprim}")
print(f"   failing the a-priori test (u != 0 and u+2o > 1/2): {len(fails)}")
print(f"   max speed among them: {max(f[0] for f in fails) if fails else '-'}"
      f"   (largest possible at this QMAX: {8*QMAX+7})")
print(f"\n   by max speed:")
from collections import Counter
c=Counter(f[0] for f in fails)
print("     ", dict(sorted(c.items())))
print(f"\n   the ten with largest u+2o:")
for mx,s,U4,o,u in sorted(fails,key=lambda z:-z[1])[:10]:
    print(f"      {str(U4):>22} max={mx:>3}  o={float(o):.4f} u={float(u):.4f} u+2o={float(s):.4f}")
