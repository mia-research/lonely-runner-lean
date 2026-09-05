#!/usr/bin/env sage
# D1 RE-TEST — fixes the sign-ambiguity flaw in d1_fast_affine_v1.py.
# Q(P)=[P+ - P-] is defined only up to sign (choice of sqrt(y_P)). The earlier test fixed Sage's
# arbitrary root, so an "additive up to sign" map (which WOULD transfer the DLP, recovering +-d)
# would have read 0/N. Here: (A) test ALL sign combinations; (B) use the CANONICAL root
# (at p=3 mod4 exactly one of +-w is itself a QR) and re-test plainly.
from sage.all import *
import sys
def PR(*a): print(*a); sys.stdout.flush()
def run(p):
    E=EllipticCurve(GF(p),[0,7]); n=E.order(); G=E.gens()[0]
    K=FunctionField(GF(p),'x'); x=K.gen()
    Rt=PolynomialRing(K,'T'); T=Rt.gen()
    L=K.extension(T**4-(x**3+7),'w'); w=L.gen()
    F=GF(p)
    def places(xp,wp):
        base=[b for b in (x-K(xp)).zeros() if b.degree()==1][0]
        pl_p=pl_m=None
        for pl in L.places_above(base):
            if pl.degree()!=1: continue
            if (w-L(wp)).valuation(pl)>0: pl_p=pl
            if (w+L(wp)).valuation(pl)>0: pl_m=pl
        return pl_p,pl_m
    def Qdiv(d,canonical):
        Pt=d*G
        if Pt.is_zero(): return None
        xp,yp=Pt.xy()
        if not yp.is_square(): return None
        wp=yp.sqrt()
        if canonical and not F(wp).is_square():   # canonical: pick the root that is itself a QR
            wp=-wp
        a,b=places(xp,wp)
        if a is None or b is None: return None
        return a.divisor()-b.divisor()
    def principal(D): return D.degree()==0 and D.dimension()>=1
    out={}
    for canon in (False,True):
        Q={}
        for d in range(1,n):
            q=Qdiv(d,canon)
            if q is not None: Q[d]=q
        lift=sorted(Q)
        # ADDITIVITY, all sign combos
        tri=[(a,b) for a in lift for b in lift if a<b and (a+b)%n in Q]
        add_any=0
        for a,b in tri:
            c=(a+b)%n
            if any(principal(s1*Q[a]+s2*Q[b]+s3*Q[c])
                   for s1,s2,s3 in [(1,1,-1),(1,1,1),(1,-1,-1),(1,-1,1)]): add_any+=1
        # AFFINE, all sign combos
        trip=[(a,b,c) for a in lift for b in lift for c in lift if a<c and (a+c)==2*b]
        aff_any=0
        for a,b,c in trip:
            if any(principal(s1*Q[a]+s3*Q[c]+s2*2*Q[b])
                   for s1,s2,s3 in [(1,-1,1),(1,1,1),(1,-1,-1),(1,1,-1)]): aff_any+=1
        out[canon]=(len(lift),len(tri),add_any,len(trip),aff_any)
    return out
for p in (43,67,79):
    o=run(p)
    for canon in (False,True):
        L_,nt,aa,ntp,af=o[canon]
        PR("p=%-3d root=%-9s lift=%-3d  additivity(ANY sign) %d/%d   AFFINE(ANY sign) %d/%d"
           %(p,"canonical" if canon else "arbitrary",L_,aa,nt,af,ntp))
