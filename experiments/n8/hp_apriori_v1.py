r"""
A sharper a-priori closure condition for the rho0 = 4 fibre.

SETUP.  e_4 = 4w, w odd.  bad(e_4,t) = evens if t = 0 or 7 (mod 8); odds if t = 3 or 4;
empty otherwise.  So [0,1) partitions into A_even (t_4 = 0,7), A_odd (t_4 = 3,4),
A_none (t_4 = 1,2,5,6), of densities 1/4, 1/4, 1/2.  With
   O = {x : the four units block all four ODD residues},  o = |O|
   V = {x : they block all four EVEN residues},           |V| = o  (by x -> 1-x)
   U = O n V,                                             u = |U|
covering all of Z/8 needs the units to supply whatever the non-unit does not:

   |S^c| = |A_none n U| + |A_even n O| + |A_odd n V|.                          (*)

TWO A-PRIORI BOUNDS from (*), both proved here:

 (B1)  |A_even n O| <= |A_even| = 1/4 and |A_odd n V| <= 1/4, so |S^c| <= u + 1/2.
       Hence  u = 0  =>  |S^c| <= 1/2.                       [the known condition]

 (B2)  U is contained in O and A_none, A_even are DISJOINT, so
          |A_none n U| + |A_even n O| <= |A_none n O| + |A_even n O| <= |O| = o,
       and |A_odd n V| <= min(1/4, o).  Hence
          |S^c| <= o + min(o, 1/4),
       so  o <= 1/4  =>  |S^c| <= 2o <= 1/2.                  [NEW, strictly weaker
       hypothesis than the previously used u + 2o <= 1/2, which forces o <= 1/4]

|S| >= 1/2 suffices by the B-lemma (|B_m1 u B_m2| < 1/2 strictly), so <= is enough.
Exact rational arithmetic, entry-point evaluation only.
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
FULL=frozenset(range(8)); ODD=frozenset({1,3,5,7}); EVEN=frozenset({0,2,4,6})

def o_u(U4):
    o=F(0); u=F(0)
    for a,b in cells(U4):
        cov=set()
        for e in U4: cov|=bad(e,fl(e,a))
        if ODD<=cov: o+=b-a
        if cov==FULL: u+=b-a
    return o,u

QMAX=int(sys.argv[1]) if len(sys.argv)>1 else 6
tot=0; old=0; new=0; both=0; neither=[]
for qs in itertools.product(range(0,QMAX+1),repeat=4):
    U4=tuple(8*q+r for q,r in zip(qs,(1,3,5,7)))
    if len(set(U4))!=4: continue
    if reduce(gcd,U4)!=1: continue
    tot+=1
    o,u=o_u(list(U4))
    A_old = (u==0) or (u+2*o<=F(1,2))
    A_new = (u==0) or (o<=F(1,4))
    old+=A_old; new+=A_new; both+= (A_new and not A_old)
    if not A_new: neither.append((float(o),float(u),U4))
print(f"PRIMITIVE unit 4-tuples, q <= {QMAX}: {tot}")
print(f"   closed by OLD a-priori (u=0 or u+2o<=1/2):  {old}  ({100*old/tot:.2f}%)")
print(f"   closed by NEW a-priori (u=0 or o<=1/4):     {new}  ({100*new/tot:.2f}%)")
print(f"   newly closed by (B2) that OLD missed:       {both}")
print(f"   still needing the finite check:             {len(neither)}")
for o,u,U4 in sorted(neither)[:10]:
    print(f"      {str(U4):>24} o={o:.4f} u={u:.4f}")
