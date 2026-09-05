#!/usr/bin/env sage
# v2: adds SYMMETRY-MATCHED NULLS (the v1 "best accuracy" statistic overfits post-hoc).
#  chi2(y) is ODD under d->n-d (verified); chi2(x) is EVEN (x_{-d}=x_d).
#  Null must preserve those symmetries and destroy only the d-alignment.
from sage.all import *
import sys, random
def PR(*a): print(*a); sys.stdout.flush()
def chi2(v,p):
    v=GF(p)(v); return 0 if v==0 else (1 if v.is_square() else -1)
def best_acc(lab, m, n):
    tab={}
    for d in range(1,n):
        tab.setdefault(lab[d],{}); tab[lab[d]][d%m]=tab[lab[d]].get(d%m,0)+1
    return sum(max(v.values()) for v in tab.values())/(n-1)
for p in (43,67,79):
    E=EllipticCurve(GF(p),[0,7]); n=E.order(); G=E.gens()[0]
    X={};Y={}
    for d in range(1,n):
        Q=d*G; xq,yq=Q.xy(); X[d]=chi2(xq,p); Y[d]=chi2(yq,p)
    PR("="*72); PR("p=%d n=%d   [chi2(y) odd under d->n-d: %d/%d]"
       %(p,n,sum(1 for d in range(1,n) if Y[d]==-Y[n-d]),n-1))
    pairs=[(d,n-d) for d in range(1,(n+1)//2)]
    random.seed(20260719); B=400
    for m in (2,3,4,6,12):
        for nm,lab,kind in (("chi2(y)",Y,'odd'),("chi2(x)",X,'even'),("joint",{d:(X[d],Y[d]) for d in range(1,n)},'both')):
            real=best_acc(lab,m,n); null=[]
            for _ in range(B):
                L={}
                for (a,b) in pairs:
                    if kind=='odd':
                        s=random.choice([1,-1]); L[a]=s; L[b]=-s
                    elif kind=='even':
                        s=random.choice([X[d] for d in range(1,n)]); L[a]=s; L[b]=s
                    else:
                        sy=random.choice([1,-1]); sx=random.choice([X[d] for d in range(1,n)])
                        L[a]=(sx,sy); L[b]=(sx,-sy)
                null.append(best_acc(L,m,n))
            mu=sum(null)/B; sd=(sum((v-mu)**2 for v in null)/B)**0.5
            z=(real-mu)/sd if sd>0 else 0.0
            rank=(sum(1 for v in null if v>=real)+1)/(B+1)
            PR("  m=%-2d %-8s real %5.1f%%  matched-null %5.1f%%  z=%+5.2f  rank-p=%.3f"
               %(m,nm,100*real,100*mu,z,rank))
