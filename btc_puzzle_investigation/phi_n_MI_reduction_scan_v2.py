#!/usr/bin/env python3
"""
v2 — rank every residue/resonance channel by a CARDINALITY-FAIR statistic so a
small real reduction in a low-q channel can't hide under high-q estimator bias.

For each channel: G = 2N·MI_nats ~ χ²(df) under independence (df=(|F|-1)(|T|-1)),
so z = (G - df)/sqrt(2·df) is 'sd above the bias floor', comparable across
cardinalities. Rank by z; permutation-confirm the top few. Pure noise over C
channels => max z ≈ sqrt(2 ln C) (~3 for C~350). Anything with z≫that AND
replicating is a real (tiny) reduction. Signal path exact int; MI/log = ranked
statistic (noqa).
"""
import csv, random, math
from math import gcd
random.seed(20260710)
NMAX=256
def factorize(m):
    f={}; d=2
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1; m//=d
        d += 1 if d==2 else 2
    if m>1: f[m]=f.get(m,0)+1
    return f
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
def mi_nats_and_df(fa,tb):
    joint={}; ca={}; cb={}
    for a,b in zip(fa,tb):
        joint[(a,b)]=joint.get((a,b),0)+1
        ca[a]=ca.get(a,0)+1; cb[b]=cb.get(b,0)+1
    N=len(fa); mi=0.0
    for (a,b),c in joint.items():
        mi += (c/N)*math.log((c*N)/(ca[a]*cb[b]))   # noqa: float
    df=(len(ca)-1)*(len(cb)-1)
    return mi,df,N
def gz(fa,tb):
    mi,df,N=mi_nats_and_df(fa,tb)
    if df<=0: return 0.0,mi,df
    G=2*N*mi
    return (G-df)/math.sqrt(2*df), mi, df       # noqa: float

BITS=[];DS=[];XS=[];YS=[]
with open("constructed_keys_1to160_100k.csv") as fh:
    for r in csv.DictReader(fh):
        N=int(r["bits"])
        if N<64: continue
        BITS.append(N); DS.append(int(r["d"]))
        XS.append(int(r["X"],16)); YS.append(int(r["Y"],16))
M=len(XS)
NS=[];KS=[];DD=[]
for i in range(M):
    n,k=best_nk(DS[i],BITS[i]); A=1<<(BITS[i]-1); base=A+(A*k)//n
    NS.append(n); KS.append(k); DD.append(DS[i]-base)
print(f"N>=64 keys: {M}\n")

QF=[2,3,4,5,6,7,8,9,11,13,16,17,19,23,25,29,31,32,37,41,43,47,53,59,61,64,30,210]
feat_kinds={"Xmodq":lambda x,y,q:x%q,"Ymodq":lambda x,y,q:y%q,
            "(X+Y)modq":lambda x,y,q:(x+y)%q,"(X*Y)modq":lambda x,y,q:(x*y)%q}
tgt_kinds={"n%q":NS,"k%q":KS,"D%q":DD}
scan=[]
for q in QF:
    feats={fn:[f(XS[i],YS[i],q) for i in range(M)] for fn,f in feat_kinds.items()}
    for tn,tv in tgt_kinds.items():
        tb=[v%q for v in tv]
        for fn,fa in feats.items():
            z,mi,df=gz(fa,tb)
            scan.append((z,fn,q,tn,mi,df))
scan.sort(key=lambda r:-r[0])
C=len(scan)
print(f"channels: {C}; noise expectation max-z ≈ {math.sqrt(2*math.log(C)):.2f}")
print("top-12 by cardinality-fair z (G-test sd above bias floor):")
for z,fn,q,tn,mi,df in scan[:12]:
    print(f"  {fn:10s} q={q:<3d} vs {tn:4s}: z={z:+.2f}  MI={mi/math.log(2):.2e} bits (df={df})")  # noqa: float
print("bottom-3 (most negative z):")
for z,fn,q,tn,mi,df in scan[-3:]:
    print(f"  {fn:10s} q={q:<3d} vs {tn:4s}: z={z:+.2f}")

# permutation-confirm the top-3 by z + split-half on z
def perm_z(fa,tb,B=500):
    z0,_,_=gz(fa,tb); tb=tb[:]; ge=0; zs=[]
    for _ in range(B):
        random.shuffle(tb); z,_,_=gz(fa,tb); zs.append(z)
        if z>=z0: ge+=1
    return z0,(ge+1)/(B+1)                       # noqa: float
print("\npermutation-confirm top-3 by z + split-half:")
for z,fn,q,tn,mi,df in scan[:3]:
    fa=[feat_kinds[fn](XS[i],YS[i],q) for i in range(M)]
    tb=[dict(tgt_kinds)[tn][i]%q for i in range(M)]
    z0,pp=perm_z(fa,tb,B=500)
    h=M//2
    z1,_,_=gz(fa[:h],tb[:h]); z2,_,_=gz(fa[h:],tb[h:])
    print(f"  {fn:10s} q={q:<3d} vs {tn:4s}: z={z0:+.2f} perm p={pp:.3f}  "
          f"half1 z={z1:+.2f} half2 z={z2:+.2f}")
print("\nverdict: if top perm p is unremarkable and z doesn't hold across halves,")
print("no residue/resonance channel reduces n/k/D above the bias floor.")
