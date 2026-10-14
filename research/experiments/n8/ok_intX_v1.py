r"""
ok_intX_v1 -- the sharp constant.

X(x) = number of residues unblocked at x.  u(E) = |{X = 0}|, and a witness exists iff
X > 0 somewhere, i.e. iff  int X > 0.  int X = sum over r of |W_r|,
W_r = { x : (e*r + floor(e x)) mod 8 in {1..6} for every e }.

Independence heuristic: each runner leaves a fixed r unblocked with probability 3/4, so
int X ~ 8*(3/4)^7 = 17496/16384 = 1.0679 -- barely above 1.  n = 8 is exactly where this
first-moment margin turns positive (n=7 gives 7*(5/7)^6 = 0.933 < 1), which is why the
general machinery has no room here.

Reports min int X over Case 2, and the shape of the maximiser of u.
"""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd

UNITS={1,3,5,7}
def blocked(e,t,r): return ((e%8)*r + t) % 8 in (0,7)
def cells(E):
    pts={F(0),F(1)}
    for e in E:
        for j in range(1,e+1):
            q=F(j,e)
            if 0<q<1: pts.add(q)
    p=sorted(pts); return list(zip(p,p[1:]))
def fl(e,a): v=e*a; return v.numerator//v.denominator

def stats(E):
    u=F(0); intX=F(0)
    for a,b in cells(E):
        w=b-a; t={e:fl(e,a) for e in E}
        X=sum(1 for r in range(8) if not any(blocked(e,t[e],r) for e in E))
        intX+=X*w
        if X==0: u+=w
    return u,intX

def shape(E):
    res=[e%8 for e in E]; Ediv=[e for e,r in zip(E,res) if r==0]
    Rnon={r for r in res if r!=0}
    uc = UNITS<=Rnon
    covered = (not Ediv) or (not uc and len(Rnon)==5) or (uc and len(Rnon)==5 and len(Ediv) in (1,2))
    return (f"{'UnitComplete' if uc else 'droppedUnit'} |R_non|={len(Rnon)} |E_div|={len(Ediv)}",
            covered, sorted(Rnon), Ediv)

M=(2,6,7,8,10,13,14)
u,iX=stats(list(M))
s,cov,R,D=shape(M)
print(f"MAXIMISER of u over Case 2 : E = {M}")
print(f"  residues mod 8 : {[e%8 for e in M]}")
print(f"  shape          : {s}     COVERED BY A PROVED LEAF? {cov}")
print(f"  R_non = {R}   E_div = {D}   units present {sorted(set(R)&UNITS)}  missing {sorted(UNITS-set(R))}")
print(f"  u(E)   = {u} = {float(u):.6f}")
print(f"  int X  = {iX} = {float(iX):.6f}     (independence heuristic 8*(3/4)^7 = 1.0679)")

print("\nscanning Case 2 over [1..20] for the MINIMUM of int X ...")
best=None; n=0
for E in combinations(range(1,21),7):
    if reduce(gcd,E)!=1: continue
    if not any(e%8==0 for e in E): continue
    n+=1
    uu,iXX=stats(list(E))
    if best is None or iXX<best[1]: best=(E,iXX,uu)
E,iXX,uu=best
s,cov,R,D=shape(E)
print(f"  {n} Case-2 tuples;  MIN int X = {iXX} = {float(iXX):.6f}  at E = {E}")
print(f"  its u = {uu} = {float(uu):.6f};  shape {s}  covered? {cov}")
print(f"\n  ==> target: int X >= {iXX} > 0 for every Case-2 tuple.")
