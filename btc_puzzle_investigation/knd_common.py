#!/usr/bin/env python3
"""
Shared, exact machinery for the φ(n) (X,Y)-information investigation.
Signal path exact int; MI/log & residuals are ranked statistics (permutation-
validated), per the no-float rule. Import, don't run.
"""
import csv, os, pickle, random, math
from math import gcd

P_FIELD=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
NMAX=256
_CACHE="_decomp_cache_N64.pkl"

def best_nk(d,N):
    A=1<<(N-1); num=d-A; best=None
    for n in range(1,NMAX+1):
        k=(2*n*num+A)//(2*A); k=0 if k<0 else (n if k>n else k)
        for kk in (k-1,k,k+1):
            if 0<=kk<=n:
                key=(abs(n*num-kk*A),n,kk)
                if best is None or key<best: best=key
    _,n,k=best; g=gcd(k,n) if n else 1
    return (n//g,k//g) if g>1 else (n,k)

def load_decomp(min_bits=64, path="constructed_keys_1to160_100k.csv"):
    """returns dict of parallel lists: bits,d,X,Y,n,k,D,signD  (cached)."""
    if os.path.exists(_CACHE):
        with open(_CACHE,"rb") as fh: c=pickle.load(fh)
        if c.get("min_bits")==min_bits: return c
    B=[];D=[];X=[];Y=[]
    with open(path) as fh:
        for r in csv.DictReader(fh):
            N=int(r["bits"])
            if N<min_bits: continue
            B.append(N); D.append(int(r["d"])); X.append(int(r["X"],16)); Y.append(int(r["Y"],16))
    NN=[];KK=[];DD=[];SG=[]
    for i in range(len(D)):
        n,k=best_nk(D[i],B[i]); A=1<<(B[i]-1); res=D[i]-(A+(A*k)//n)
        NN.append(n); KK.append(k); DD.append(res); SG.append(1 if res>=0 else 0)
    c=dict(min_bits=min_bits,bits=B,d=D,X=X,Y=Y,n=NN,k=KK,D=DD,signD=SG)
    with open(_CACHE,"wb") as fh: pickle.dump(c,fh)
    return c

def legendre(x,p=P_FIELD): return 1 if pow(x,(p-1)//2,p)==1 else 0

def a_ell(l):
    """Frobenius trace a_l of y^2=x^3+7 over F_l, exact by point count.
    a_l = -sum_x legendre(x^3+7, l).  a_l=0 <=> supersingular (l≡2 mod 3)."""
    s=0
    for x in range(l):
        v=(x*x*x+7)%l
        if v==0: continue
        s+= 1 if pow(v,(l-1)//2,l)==1 else -1
    return -s

def mi_nats_df(fa,tb):
    joint={};ca={};cb={}
    for a,b in zip(fa,tb):
        joint[(a,b)]=joint.get((a,b),0)+1; ca[a]=ca.get(a,0)+1; cb[b]=cb.get(b,0)+1
    N=len(fa); mi=0.0
    for (a,b),c in joint.items(): mi+=(c/N)*math.log((c*N)/(ca[a]*cb[b]))  # noqa: float
    return mi,(len(ca)-1)*(len(cb)-1),N

def gtest_z(fa,tb):
    mi,df,N=mi_nats_df(fa,tb)
    return ((2*N*mi-df)/math.sqrt(2*df)) if df>0 else 0.0                   # noqa: float

def mi_bits_bc(fa,tb):
    mi,df,N=mi_nats_df(fa,tb)
    return (mi-df/(2*N))/math.log(2)                                        # noqa: float

def min_resid(fa,tb):
    O={};ra={};cb={}
    for a,b in zip(fa,tb): O[(a,b)]=O.get((a,b),0)+1; ra[a]=ra.get(a,0)+1; cb[b]=cb.get(b,0)+1
    N=len(fa); mn=9e9; empty=0                                              # noqa: float
    for a in ra:
        for b in cb:
            E=ra[a]*cb[b]/N; o=O.get((a,b),0)                              # noqa: float
            r=(o-E)/math.sqrt(E) if E>0 else 0.0                           # noqa: float
            if r<mn: mn=r
            if o==0 and E>=5: empty+=1
    return mn,empty

def perm_p(fa,tb,stat,B=500,worse="ge",seed=20260710):
    """generic permutation p for stat(fa,tb). worse='ge' (stat>=obs) or 'le'."""
    rnd=random.Random(seed); obs=stat(fa,tb); tb=tb[:]; cnt=0
    for _ in range(B):
        rnd.shuffle(tb); v=stat(fa,tb)
        if (worse=="ge" and v>=obs) or (worse=="le" and v<=obs): cnt+=1
    return obs,(cnt+1)/(B+1)                                                # noqa: float
