r"""
A NEW necessary condition for O, and the bound it gives.

By the pair rule the unit runner of residue rho blocks the odd residue -tau_rho*rho,
where tau_rho is the odd member of {t_rho, t_rho+1}.  Put s_rho = tau_rho mod 8 in
(Z/8)^* = {1,3,5,7}, a Klein four-group.  Then
     O = { x : rho -> s_rho * rho  is a BIJECTION of (Z/8)^* }.
Summing a bijection over the group equals summing the identity over the group, and in
an elementary abelian 2-group every element is its own inverse, so the product of all
group elements is 1.  Hence
     PRODUCT LAW:   x in O  =>  s_1 * s_3 * s_5 * s_7 = 1  (mod 8).
This is 64 of the 4^4 = 256 s-vectors (density 1/4), against the 24 that are actually
bijections (density 3/32).  So  o <= |Pi|,  Pi = {x : s_1 s_3 s_5 s_7 = 1 mod 8},
and Pi is cut out by just TWO parity conditions on the a_rho = floor(e_rho x/2) mod 4.

Checked below: (i) the product law holds on every cell of O; (ii) how tight o <= |Pi| is;
(iii) whether |Pi| <= 1/3 outside a finite list.  Exact arithmetic, entry-point only.
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
ODD=frozenset({1,3,5,7})
def s_of(t): return (2*(t//2)+1)%8          # odd member of {t,t+1}, mod 8

def stats(U4):
    o=F(0); pi=F(0); viol=0
    for a,b in cells(U4):
        ts=[fl(e,a) for e in U4]
        cov=set()
        for e,t in zip(U4,ts): cov|=bad(e,t)
        inO = ODD<=cov
        prod=1
        for t in ts: prod=(prod*s_of(t))%8
        inPi = (prod==1)
        if inO and not inPi: viol+=1
        if inO: o+=b-a
        if inPi: pi+=b-a
    return o,pi,viol

QMAX=int(sys.argv[1]) if len(sys.argv)>1 else 5
tot=0; badviol=0; rows=[]
for qs in itertools.product(range(0,QMAX+1),repeat=4):
    U4=tuple(8*q+r for q,r in zip(qs,(1,3,5,7)))
    if len(set(U4))!=4: continue
    if reduce(gcd,U4)!=1: continue
    tot+=1
    o,pi,v = stats(list(U4))
    badviol += v
    rows.append((pi,o,U4,max(U4)))
print(f"PRIMITIVE unit 4-tuples q <= {QMAX}: {tot}")
print(f"(i)  PRODUCT LAW violations (cell in O with s_1 s_3 s_5 s_7 != 1): {badviol}")
rows.sort(reverse=True)
print(f"(ii) o <= |Pi| held in all rows: {all(r[1]<=r[0] for r in rows)}")
print(f"(iii) tuples with |Pi| > 1/3: {sum(1 for r in rows if r[0]>F(1,3))}")
print(f"\n   {'tuple':>22} {'max':>4} {'|Pi|':>12} {'|Pi|~':>8} {'o':>12} {'o~':>8}")
for pi,o,U4,mx in rows[:8]:
    print(f"   {str(U4):>22} {mx:>4} {str(pi):>12} {float(pi):>8.4f} {str(o):>12} {float(o):>8.4f}")
print(f"\n   min |Pi| seen: {float(min(r[0] for r in rows)):.4f}   (equidistribution limit 1/4)")
