r"""
Where does the a-priori fibre condition take over?

For the four unit runners: O = {x : all four ODD residues blocked}, o = |O|;
U = {x : all of Z/8 blocked}, u = |U| <= o.  The rho0 = 4 fibre closes A PRIORI when
u = 0 or u + 2o <= 1/2.  Under equidistribution of (t_1,t_3,t_5,t_7) mod 8 the 24 good
tau-vectors out of 4^4 give o -> 24/256 = 3/32 = 0.09375 and u -> 16/4096 = 1/256,
so u + 2o -> 0.1914 < 1/2.  The question is the DISCREPANCY: how large must the unit
speeds be before u + 2o <= 1/2 holds?  Exact rational arithmetic, entry-point evaluation.
"""
from fractions import Fraction as F
from math import gcd
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
FULL=frozenset(range(8)); ODD=frozenset({1,3,5,7})
def o_u(U4):
    o=F(0); u=F(0)
    for a,b in cells(U4):
        cov=set()
        for e in U4: cov|=bad(e,fl(e,a))
        if ODD<=cov: o+=b-a
        if cov==FULL: u+=b-a
    return o,u

QMAX=int(sys.argv[1]) if len(sys.argv)>1 else 5
rows=[]
for qs in itertools.product(range(0,QMAX+1),repeat=4):
    U4=tuple(8*q+r for q,r in zip(qs,(1,3,5,7)))
    if len(set(U4))!=4: continue
    o,u=o_u(list(U4))
    rows.append((u+2*o, o, u, U4, max(U4)))
print(f"unit 4-tuples with q <= {QMAX}: {len(rows)}")
apriori=[r for r in rows if r[2]==0 or r[0]<=F(1,2)]
print(f"   closed A PRIORI (u = 0 or u+2o <= 1/2): {len(apriori)}  ({100*len(apriori)/len(rows):.1f}%)")
print(f"   of those, by u = 0: {sum(1 for r in rows if r[2]==0)};"
      f"  by u+2o <= 1/2 with u > 0: {sum(1 for r in rows if r[2]>0 and r[0]<=F(1,2))}")
rows.sort(reverse=True)
print(f"\n   largest u+2o:")
for s,o,u,U4,mx in rows[:6]:
    print(f"      {str(U4):>24} max={mx:>3}  o={float(o):.4f} u={float(u):.4f}  u+2o={float(s):.4f}")
print(f"\n   smallest o seen: {float(min(r[1] for r in rows)):.4f}"
      f"   (equidistribution limit 3/32 = 0.09375)")
nz=[r for r in rows if r[2]>0]
print(f"   tuples with u > 0: {len(nz)} of {len(rows)}")
if nz:
    print(f"   among those, max speed range {min(r[4] for r in nz)}..{max(r[4] for r in nz)};"
          f" min u+2o = {float(min(r[0] for r in nz)):.4f}")
