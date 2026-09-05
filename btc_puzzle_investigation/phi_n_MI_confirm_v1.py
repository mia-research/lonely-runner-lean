#!/usr/bin/env python3
"""
Confirm the only non-q210 candidate above the noise line: (X*Y) mod 64 vs D mod 64
(G-test z=4.87). Permutation null is the honest arbiter (χ² breaks on sparse/skewed
tables). Controls: a clean-feature channel (X mod 64 vs D) and the product artifact
seen alone. If perm p is unremarkable, the residue/resonance scan is fully null.
"""
import csv, random, math
from math import gcd
random.seed(4242); NMAX=256
def best_nk(d,N):
    A=1<<(N-1); num=d-A; best=None
    for n in range(1,NMAX+1):
        k=(2*n*num+A)//(2*A)
        if k<0:k=0
        if k>n:k=n
        for kk in (k-1,k,k+1):
            if 0<=kk<=n:
                key=(abs(n*num-kk*A),n,kk)
                if best is None or key<best: best=key
    _,n,k=best; g=gcd(k,n) if n else 1
    if g>1: n//=g; k//=g
    return n,k
def gz(fa,tb):
    joint={};ca={};cb={}
    for a,b in zip(fa,tb):
        joint[(a,b)]=joint.get((a,b),0)+1; ca[a]=ca.get(a,0)+1; cb[b]=cb.get(b,0)+1
    N=len(fa); mi=0.0
    for (a,b),c in joint.items(): mi+=(c/N)*math.log((c*N)/(ca[a]*cb[b]))  # noqa: float
    df=(len(ca)-1)*(len(cb)-1)
    return ((2*N*mi-df)/math.sqrt(2*df)) if df>0 else 0.0                   # noqa: float
def perm_p(fa,tb,B=1000):
    z0=gz(fa,tb); tb=tb[:]; ge=0
    for _ in range(B):
        random.shuffle(tb)
        if gz(fa,tb)>=z0: ge+=1
    return z0,(ge+1)/(B+1)                                                  # noqa: float

BITS=[];DS=[];XS=[];YS=[]
with open("constructed_keys_1to160_100k.csv") as fh:
    for r in csv.DictReader(fh):
        N=int(r["bits"])
        if N<64: continue
        BITS.append(N); DS.append(int(r["d"])); XS.append(int(r["X"],16)); YS.append(int(r["Y"],16))
M=len(XS); DD=[]
for i in range(M):
    n,k=best_nk(DS[i],BITS[i]); A=1<<(BITS[i]-1); DD.append(DS[i]-(A+(A*k)//n))
q=64; Dq=[d%q for d in DD]
for lab,fa in [("(X*Y)mod64", [ (XS[i]*YS[i])%q for i in range(M)]),
               ("X mod64",    [ XS[i]%q for i in range(M)]),
               ("(X+Y)mod64", [ (XS[i]+YS[i])%q for i in range(M)])]:
    z0,pp=perm_p(fa,Dq,B=1000)
    print(f"{lab:12s} vs D mod64: G-test z={z0:+.2f}  permutation p={pp:.3f}")
