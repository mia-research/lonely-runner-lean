#!/usr/bin/env sage
# D1 FAST — test the LEVER CONDITION directly, no discrete logs needed.
# A usable transfer needs ell(d)=dlog(Q([d]G)) affine in d. Affine <=> for every arithmetic triple
# d1+d3=2*d2 :  Q(d1)+Q(d3)-2*Q(d2) ~ 0 (principal).  Also test raw additivity (Hom=0 predicts FAIL).
# Principality of a degree-0 divisor D  <=>  dim L(D) >= 1.   CONTROLS included and must fire.
from sage.all import *
import sys
def P(*a): print(*a); sys.stdout.flush()
p=43
E=EllipticCurve(GF(p),[0,7]); n=E.order(); G=E.gens()[0]
K=FunctionField(GF(p),'x'); x=K.gen()
Rt=PolynomialRing(K,'T'); T=Rt.gen()
L=K.extension(T**4-(x**3+7),'w'); w=L.gen()
P("p=%d n=%d genus=%d"%(p,n,L.genus()))
def Qdiv(d):
    Pt=d*G
    if Pt.is_zero(): return None
    xp,yp=Pt.xy()
    if not yp.is_square(): return None
    wp=yp.sqrt()
    base=[b for b in (x-K(xp)).zeros() if b.degree()==1][0]
    plus=minus=None
    for pl in L.places_above(base):
        if pl.degree()!=1: continue
        if (w-L(wp)).valuation(pl)>0: plus=pl
        if (w+L(wp)).valuation(pl)>0: minus=pl
    if plus is None or minus is None: return None
    return plus.divisor()-minus.divisor()
def principal(D): return D.degree()==0 and D.dimension()>=1
Q={}
for d in range(1,n):
    q=Qdiv(d)
    if q is not None: Q[d]=q
lift=sorted(Q); P("liftable d (y_P a QR): %s  -> %d of %d"%(lift,len(lift),n-1))
# CONTROLS
f=w  # a function on C
P("CONTROL+ div(f) principal? %s  (must be True)"%principal(f.divisor()))
d0=lift[0]
P("CONTROL- Q(%d) principal?  %s  (must be False => lift is non-trivial)"%(d0,principal(Q[d0])))
# order: is Q(d) killed by a small integer?
for m in (2,3):
    cnt=sum(1 for d in lift if principal(m*Q[d]))
    P("order test: %d*Q(d) ~ 0 for %d/%d liftable d"%(m,cnt,len(lift)))
# RAW ADDITIVITY (Hom(E,A_new)=0 predicts this FAILS)
tri=[(a,b) for a in lift for b in lift if a<b and (a+b)%n in Q]
ok=sum(1 for a,b in tri if principal(Q[a]+Q[b]-Q[(a+b)%n]))
P("additivity Q(a)+Q(b)==Q(a+b): %d/%d triples hold"%(ok,len(tri)))
# AFFINE TEST (the lever condition)
trip=[(a,b,c) for a in lift for b in lift for c in lift if a<c and (a+c)==2*b]
ok2=sum(1 for a,b,c in trip if principal(Q[a]+Q[c]-2*Q[b]))
P("AFFINE  Q(d1)+Q(d3)-2Q(d2)~0 for d1+d3=2d2: %d/%d triples hold"%(ok2,len(trip)))
P("READ: affine holding on ALL triples => ell is affine => usable transfer (LEVER).")
P("      affine failing => no affine transfer through this lift at p=%d."%p)
