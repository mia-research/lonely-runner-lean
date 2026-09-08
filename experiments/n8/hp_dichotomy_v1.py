r"""
Testing a DICHOTOMY that would close (H').

From |S^c| = |A_none n U| + 2|A_even n O| and the partition of O by the three A-sets
(alpha = |A_even n O|, beta = |A_odd n O|, gamma = |A_none n O|, alpha+beta+gamma = o):

    |S^c| <= gamma + 2*alpha = o - beta + alpha  <=  o - beta + min(1/4, o).

Under equidistribution beta -> o/4, giving |S^c| <~ (3/4)o + min(1/4,o), which is
<= 1/2 exactly when o <= 1/3.  So the natural a-priori pair is

    u = 0        (then |S^c| <= u + 1/2 = 1/2)
    o <= 1/3     (then the displayed bound closes, up to a discrepancy term in beta)

CONJECTURED DICHOTOMY:  every primitive unit 4-tuple has  u = 0  or  o <= 1/3,
with the single exception (1,3,5,7), where o = 16/35 and u = 1/7.

If true, (H') reduces to the discrepancy term alone.  Exact arithmetic, entry-point
evaluation only.
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
FULL=frozenset(range(8)); ODD=frozenset({1,3,5,7})
def o_u(U4):
    o=F(0); u=F(0)
    for a,b in cells(U4):
        cov=set()
        for e in U4: cov|=bad(e,fl(e,a))
        if ODD<=cov: o+=b-a
        if cov==FULL: u+=b-a
    return o,u

QMAX=int(sys.argv[1]) if len(sys.argv)>1 else 6
THIRD=F(1,3)
tot=0; viol=[]; ou=[]
for qs in itertools.product(range(0,QMAX+1),repeat=4):
    U4=tuple(8*q+r for q,r in zip(qs,(1,3,5,7)))
    if len(set(U4))!=4: continue
    if reduce(gcd,U4)!=1: continue
    tot+=1
    o,u=o_u(list(U4))
    ou.append((o,u,U4))
    if u!=0 and o>THIRD: viol.append((o,u,U4))
viol.sort(reverse=True)
print(f"PRIMITIVE unit 4-tuples, q <= {QMAX}: {tot}")
print(f"   with u > 0 AND o > 1/3  (i.e. NOT closed by the dichotomy): {len(viol)}")
for o,u,U4 in viol:
    print(f"      {str(U4):>24}  o = {o} = {float(o):.5f}   u = {u} = {float(u):.5f}")
mx=max(ou, key=lambda z: z[0])
print(f"\n   max o overall: {mx[0]} = {float(mx[0]):.5f} at {mx[2]} (u = {mx[1]})")
pos=[z for z in ou if z[1]>0]
print(f"   tuples with u > 0: {len(pos)};  among them max o = "
      f"{max(z[0] for z in pos)} = {float(max(z[0] for z in pos)):.5f}")
second=sorted({z[0] for z in pos}, reverse=True)[:4]
print(f"   the four largest o values among u>0 tuples: {[str(s)+f' ({float(s):.4f})' for s in second]}")
