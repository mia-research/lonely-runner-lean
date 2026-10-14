r"""
Is large o caused by a SMALL LINEAR RELATION among the unit speeds?

Observations to test:
   (1,3,5,7):    1 - 3 - 5 + 7 = 0
   (1,11,5,7):   1 + 11 - 5 - 7 = 0
   translates 8q+(1,3,5,7):  (8q+1)-(8q+3)-(8q+5)+(8q+7) = 0, same relation, o = 1/4.
Generic tuples have no such relation and give o -> 3/32.

o = |O| with O = {x : rho -> s_rho * rho is a bijection of (Z/8)^*}, s_rho = odd member
of {floor(e_rho x), floor(e_rho x)+1} mod 8.  Exact arithmetic, entry-point evaluation.
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
def o_of(U4):
    o=F(0)
    for a,b in cells(U4):
        cov=set()
        for e in U4: cov|=bad(e,fl(e,a))
        if ODD<=cov: o+=b-a
    return o
def relations(U4):
    """nonzero sign vectors (up to global sign) with sum 0"""
    out=[]
    for sg in itertools.product((1,-1),repeat=4):
        if sg[0]!=1: continue
        if sum(s*e for s,e in zip(sg,U4))==0: out.append(sg)
    return out

QMAX=int(sys.argv[1]) if len(sys.argv)>1 else 6
THIRD=F(1,3); QUART=F(1,4)
withrel=[]; norel_max=None; rel_over_third=[]
tot=0
for qs in itertools.product(range(0,QMAX+1),repeat=4):
    U4=tuple(8*q+r for q,r in zip(qs,(1,3,5,7)))
    if len(set(U4))!=4: continue
    if reduce(gcd,U4)!=1: continue
    tot+=1
    rel=relations(U4); o=o_of(list(U4))
    if rel:
        withrel.append((o,U4,rel))
        if o>THIRD: rel_over_third.append((o,U4,rel))
    else:
        if norel_max is None or o>norel_max[0]: norel_max=(o,U4)
print(f"PRIMITIVE unit 4-tuples q <= {QMAX}: {tot}")
print(f"   with a +-1 relation sum(s_i e_i) = 0 : {len(withrel)}")
print(f"   WITHOUT any such relation           : {tot-len(withrel)}")
print(f"\n   max o among tuples WITHOUT a relation: {norel_max[0]} = {float(norel_max[0]):.5f}"
      f"  at {norel_max[1]}   ( <= 1/3 ? {norel_max[0]<=THIRD} )")
withrel.sort(reverse=True)
print(f"\n   the tuples WITH a relation, largest o first:")
for o,U4,rel in withrel[:10]:
    print(f"      {str(U4):>22}  o = {str(o):>12} = {float(o):.5f}  relations {rel}")
print(f"\n   among relation-tuples, how many have o = 1/4 exactly: "
      f"{sum(1 for o,_,_ in withrel if o==QUART)} of {len(withrel)}")
print(f"   among relation-tuples, o > 1/3: {len(rel_over_third)}")
for o,U4,rel in rel_over_third: print(f"      {U4}  o={o}  rel={rel}")
