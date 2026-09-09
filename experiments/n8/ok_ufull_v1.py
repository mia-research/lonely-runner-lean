r"""
ok_ufull_v1 -- the whole problem, in one quantity.

A witness exists iff some x has an unblocked residue, i.e. iff U(E) is not all of [0,1).
U(E) is a finite union of cells, so that is exactly

        LRC(8) for integer speeds   <==>   u(E) < 1  for every admissible 7-tuple E.

No case tree, no split into E_non and E_div: the split u(E_non) + |union B_m| < 1 is a
LOSSY sufficient condition, and ok_umax_v1 shows it fails at every |E_div| (max u(E_non)
is 1/3 at k=4 vs the 1/4 needed, 9/14 at k=5 vs 1/2, 125/154 at k=6 vs 3/4).

This measures the real thing: max u(E) over admissible E, and where the maximum sits.
"""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd
import sys

def bad(e,t): return frozenset(r for r in range(8) if (e*r+t)%8 in (0,7))
BADC={}
def badc(e,t):
    k=(e%8,t%8)
    if k not in BADC: BADC[k]=bad(e%8,t%8)
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

N=int(sys.argv[1]) if len(sys.argv)>1 else 18
best=[]; n=0
for E in combinations(range(1,N+1),7):
    if reduce(gcd,E)!=1: continue
    n+=1
    uu=u_of(list(E))
    best.append((uu,E))
best.sort(key=lambda r:-r[0])
print(f"# admissible 7-tuples from [1..{N}] with gcd 1 : {n}")
print(f"# LRC(8) for these <==> every one has u < 1\n")
print(f"{'E':34} {'u(E)':>14} {'~':>9}  {'#(rho=4)':>9} {'#div':>5}")
for uu,E in best[:10]:
    r4=sum(1 for e in E if e%8==4); rd=sum(1 for e in E if e%8==0)
    print(f"{str(E):34} {str(uu):>14} {float(uu):9.6f}  {r4:>9} {rd:>5}")
mx=best[0][0]
print(f"\nMAX u(E) = {mx} = {float(mx):.6f}     margin to 1 : {1-mx} = {float(1-mx):.6f}")
print(f"tuples with u >= 3/4 : {sum(1 for uu,_ in best if uu>=F(3,4))}")
print(f"tuples with u >= 1/2 : {sum(1 for uu,_ in best if uu>=F(1,2))}")
print(f"tuples with u = 1    : {sum(1 for uu,_ in best if uu==1)}   <-- must be 0")
# does the max always carry rho=4 runners?
top=[E for uu,E in best[:50]]
print(f"\nof the top 50 by u, how many contain a runner = 4 mod 8: "
      f"{sum(1 for E in top if any(e%8==4 for e in E))}/50")
print(f"of ALL {n} tuples, fraction containing a 4 mod 8 runner: "
      f"{sum(1 for _,E in best if any(e%8==4 for e in E))/n:.3f}")
