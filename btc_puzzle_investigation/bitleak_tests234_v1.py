#!/usr/bin/env sage
from sage.all import *
import sys, random
def PR(*a): print(*a); sys.stdout.flush()
def chi2(v,p):
    v=GF(p)(v); return 0 if v==0 else (1 if v.is_square() else -1)
def best_acc(lab,m,n):
    tab={}
    for d in range(1,n):
        tab.setdefault(lab[d],{}); tab[lab[d]][d%m]=tab[lab[d]].get(d%m,0)+1
    return sum(max(v.values()) for v in tab.values())/(n-1)
for p in (43,67,79):
    E=EllipticCurve(GF(p),[0,7]); n=E.order(); G=E.gens()[0]
    PR("="*72); PR("p=%d n=%d"%(p,n))
    Y={};X={}
    for d in range(1,n):
        Q=d*G; xq,yq=Q.xy(); X[d]=chi2(xq,p); Y[d]=chi2(yq,p)

    # ---------- TEST 2: is Delta killed by small torsion? ----------
    K=FunctionField(GF(p),'x'); xv=K.gen()
    Rt=PolynomialRing(K,'T'); T=Rt.gen()
    L=K.extension(T**4-(xv**3+7),'w'); w=L.gen()
    def Qdiv(d):
        Pt=d*G
        if Pt.is_zero(): return None
        xp,yp=Pt.xy()
        if not yp.is_square(): return None
        wp=yp.sqrt()
        base=[b for b in (xv-K(xp)).zeros() if b.degree()==1][0]
        pl_p=pl_m=None
        for pl in L.places_above(base):
            if pl.degree()!=1: continue
            if (w-L(wp)).valuation(pl)>0: pl_p=pl
            if (w+L(wp)).valuation(pl)>0: pl_m=pl
        return None if (pl_p is None or pl_m is None) else pl_p.divisor()-pl_m.divisor()
    def princ(D): return D.degree()==0 and D.dimension()>=1
    QD={}
    for d in range(1,n):
        q=Qdiv(d)
        if q is not None: QD[d]=q
    lift=sorted(QD)
    PR("  TEST 2  torsion test on Delta = Q(a)+Q(b)-Q(a+b)   (liftable %d)"%len(lift))
    for m in (1,2,3,4,6,12):
        tri=[(a,b) for a in lift for b in lift if a<b and (a+b)%n in QD]
        hit=sum(1 for a,b in tri if princ(m*(QD[a]+QD[b]-QD[(a+b)%n])))
        PR("    m=%-2d : m*Delta ~ 0 for %d/%d triples"%(m,hit,len(tri)))
    for m in (2,3,4,6,12):
        z=sum(1 for d in lift if princ(m*QD[d]))
        PR("    [check] m*Q(d) ~ 0 for %d/%d  (if 0, Hom=0 forbids m*Q being additive)"%(z,len(lift)))

    # ---------- TEST 3: GLV / mu3 ----------
    Rn=PolynomialRing(GF(n),'t'); t=Rn.gen()
    F_=GF(p); gg=F_.multiplicative_generator(); beta=gg**((p-1)//3)
    lam=None
    for r,_ in (t**2+t+1).roots():
        if (Integer(r)*G).xy()[0]==beta*G.xy()[0]: lam=Integer(r); break
    PR("  TEST 3  beta=%s chi2(beta)=%d  lambda=%s"%(beta,chi2(beta,p),lam))
    if lam:
        iy=sum(1 for d in range(1,n) if Y[d]==Y[(lam*d)%n])
        ix=sum(1 for d in range(1,n) if X[d]==X[(lam*d)%n])
        PR("    chi2(y) mu3-invariant %d/%d ; chi2(x) mu3-invariant %d/%d"%(iy,n-1,ix,n-1))
        PR("    predict d mod 3 from chi2(x): %.1f%% (baseline 33.3%%)"%(100*best_acc(X,3,n)))

    # ---------- TEST 4: local window sum, matched null ----------
    PR("  TEST 4  S(Q,k)=sum_{i=1..k} chi2(y_{Q+iG})   vs d mod m")
    pairs=[(d,n-d) for d in range(1,(n+1)//2)]; random.seed(7); B=300
    for k in (1,2,3,5,10):
        S={d: sum(Y[(d+i)%n] if (d+i)%n!=0 else 0 for i in range(1,k+1)) for d in range(1,n)}
        for m in (2,3):
            real=best_acc(S,m,n); null=[]
            for _ in range(B):
                Yr={}
                for (a,b) in pairs:
                    s=random.choice([1,-1]); Yr[a]=s; Yr[b]=-s
                Sr={d: sum(Yr[(d+i)%n] if (d+i)%n!=0 else 0 for i in range(1,k+1)) for d in range(1,n)}
                null.append(best_acc(Sr,m,n))
            mu=sum(null)/B; sd=(sum((v-mu)**2 for v in null)/B)**0.5
            PR("    k=%-2d m=%d real %5.1f%% null %5.1f%% z=%+5.2f rank-p=%.3f"
               %(k,m,100*real,100*mu,(real-mu)/sd if sd>0 else 0,
                 (sum(1 for v in null if v>=real)+1)/(B+1)))
