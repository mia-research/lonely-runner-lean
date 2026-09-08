r"""
Is {primitive unit 4-tuples with o > 1/3} a FINITE list?

If so, the dichotomy "u = 0 or o <= 1/3, except (1,3,5,7)" is a finite check, and (H')
reduces to the discrepancy term in beta = |A_odd n O| alone.

o = |O| where O = {x : the four unit runners block all four ODD residues}.  By the pair
rule the unit of residue rho blocks the odd residue -tau_rho * rho, tau_rho the odd
member of {t_rho, t_rho + 1}.  Writing s_rho = tau_rho mod 8 in (Z/8)* and using the
Klein-group structure, O is exactly {x : rho -> s_rho * rho is a bijection of (Z/8)*},
which is 24 of the 4^4 = 256 s-vectors, so o -> 24/256 = 3/32 under equidistribution.
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

QMAX=int(sys.argv[1]) if len(sys.argv)>1 else 8
THIRD=F(1,3)
big=[]; tot=0
for qs in itertools.product(range(0,QMAX+1),repeat=4):
    U4=tuple(8*q+r for q,r in zip(qs,(1,3,5,7)))
    if len(set(U4))!=4: continue
    if reduce(gcd,U4)!=1: continue
    tot+=1
    o,u=o_u(list(U4))
    if o>THIRD: big.append((o,u,U4,max(U4)))
big.sort(reverse=True)
print(f"PRIMITIVE unit 4-tuples, q <= {QMAX} (max speed <= {8*QMAX+7}): {tot}")
print(f"   with o > 1/3: {len(big)}")
print(f"   max speed among them: {max(b[3] for b in big) if big else '-'}")
print(f"\n   {'tuple':>24} {'max':>4} {'o':>14} {'o~':>8} {'u':>10} {'u>0?':>6}")
for o,u,U4,mx in big:
    print(f"   {str(U4):>24} {mx:>4} {str(o):>14} {float(o):>8.4f} {str(u):>10} {str(u>0):>6}")
