r"""
ok_case2_sup_v1 -- is sup u(E) over CASE 2 bounded away from 1?

Reformulation (proved, it is the bridge restated):
    u(E) < 1  ==>  a witness exists, strictly interior.
    u(E) = 1  is possible only via a BOUNDARY witness (block index 7 with s_e = 0);
              those are exactly the three tight instances, and
              TIGHT_INSTANCES_v1.md:51 records that NONE of them contains a multiple of 8.
So all u = 1 tuples lie in Case 1 (E_div empty), closed by t = 1/8.  The programme is:

              CASE 2 (E_div nonempty)   ==>   u(E) < 1.

If sup over Case 2 is attained below 1, that is a clean theorem target.  If it creeps to 1
as the box grows, no uniform bound exists and the argument must be non-uniform.
"""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd
import sys

BADC={}
def badc(e,t):
    k=(e%8,t%8)
    if k not in BADC:
        BADC[k]=frozenset(r for r in range(8) if ((e%8)*r+(t%8))%8 in (0,7))
    return BADC[k]

def u_of(E):
    pts={F(0),F(1)}
    for e in E:
        for j in range(1,e+1):
            q=F(j,e)
            if 0<q<1: pts.add(q)
    p=sorted(pts); tot=F(0)
    for a,b in zip(p,p[1:]):
        cov=set()
        for e in E:
            v=e*a; cov|=badc(e,v.numerator//v.denominator)
            if len(cov)==8: break
        if len(cov)==8: tot+=b-a
    return tot

print(f"{'box':>8} {'#Case2':>9} {'max u (Case 2)':>18} {'~':>10} {'1-u':>12}  argmax")
for N in [14,16,18,20,22]:
    best=None; n=0
    for E in combinations(range(1,N+1),7):
        if reduce(gcd,E)!=1: continue
        if not any(e%8==0 for e in E): continue     # Case 2 only
        n+=1
        uu=u_of(list(E))
        if best is None or uu>best[0]: best=(uu,E)
    if best is None:
        print(f"[1..{N}]".rjust(8), "     none"); continue
    uu,E=best
    print(f"{('[1..'+str(N)+']'):>8} {n:>9} {str(uu):>18} {float(uu):10.6f} "
          f"{float(1-uu):12.6f}  {E}")
