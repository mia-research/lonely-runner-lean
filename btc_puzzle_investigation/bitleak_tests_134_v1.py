#!/usr/bin/env sage
from sage.all import *
import sys
def PR(*a): print(*a); sys.stdout.flush()
def chi2(v,p):
    v=GF(p)(v)
    return 0 if v==0 else (1 if v.is_square() else -1)

for p in (43,67,79):
    E=EllipticCurve(GF(p),[0,7]); n=E.order(); G=E.gens()[0]
    PR("="*70); PR("p=%d  n=#E=%d  (n prime: %s)"%(p,n,is_prime(n)))
    X={}; Y={}
    for d in range(1,n):
        Q=d*G; xq,yq=Q.xy(); X[d]=chi2(xq,p); Y[d]=chi2(yq,p)
    # --- structural check: chi2(y_d) odd under d -> n-d ?
    odd_ok=sum(1 for d in range(1,n) if Y[d]==-Y[n-d])
    PR("  [struct] chi2(y_{n-d}) == -chi2(y_d) : %d/%d"%(odd_ok,n-1))

    # --- TEST 1: predict d mod m from (chi2(x),chi2(y))
    PR("  TEST 1  predict d mod m from the coordinate Legendre symbols")
    for m in (2,3,4,6,12):
        for name,F in (("chi2(y)",Y),("chi2(x)",X),("(chi2x,chi2y)",None)):
            tab={}
            for d in range(1,n):
                k=(X[d],Y[d]) if F is None else F[d]
                tab.setdefault(k,{}).setdefault(d%m,0)
                tab[k][d%m]=tab[k].get(d%m,0)+1
            best=sum(max(v.values()) for v in tab.values()); tot=n-1
            PR("    m=%-2d %-14s best accuracy %3d/%3d = %5.1f%%   (baseline %5.1f%%)"
               %(m,name,best,tot,100.0*best/tot,100.0/m))

    # --- TEST 3: GLV / mu3 orbit
    F_=GF(p); g=F_.multiplicative_generator(); beta=g**((p-1)//3)
    lam=None
    for cand in [r for r,_ in (x**2+x+1).roots(GF(n))] if True else []:
        if (cand*G).xy()[0]==beta*G.xy()[0]: lam=cand; break
    PR("  TEST 3  GLV: beta=%s  lambda found: %s  chi2(beta)=%d"%(beta,lam is not None,chi2(beta,p)))
    if lam is not None:
        inv_y=sum(1 for d in range(1,n) if Y[d]==Y[(lam*d)%n])
        inv_x=sum(1 for d in range(1,n) if X[d]==X[(lam*d)%n])
        PR("    chi2(y) mu3-invariant: %d/%d ; chi2(x) mu3-invariant: %d/%d"%(inv_y,n-1,inv_x,n-1))
        tab={}
        for d in range(1,n):
            tab.setdefault(X[d],{}); tab[X[d]][d%3]=tab[X[d]].get(d%3,0)+1
        best=sum(max(v.values()) for v in tab.values())
        PR("    predict d mod 3 from chi2(x): %d/%d = %.1f%% (baseline 33.3%%)"%(best,n-1,100.0*best/(n-1)))

    # --- TEST 4: localized window sum S(Q,k)=sum_{i=1..k} chi2(y_{Q+iG})
    PR("  TEST 4  local window sum vs d mod 2 / mod 3")
    for k in (1,2,3,5,10):
        S={d: sum(Y[(d+i)%n] if (d+i)%n!=0 else 0 for i in range(1,k+1)) for d in range(1,n)}
        for m in (2,3):
            tab={}
            for d in range(1,n):
                tab.setdefault(S[d],{}); tab[S[d]][d%m]=tab[S[d]].get(d%m,0)+1
            best=sum(max(v.values()) for v in tab.values())
            PR("    k=%-2d m=%d  best accuracy %3d/%3d = %5.1f%%  (baseline %5.1f%%)"
               %(k,m,best,n-1,100.0*best/(n-1),100.0/m))
