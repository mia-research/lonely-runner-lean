#!/usr/bin/env python3
"""
Characterise the (X*Y) mod 64 vs D candidate (perm p=0.002). Three discriminators:

  1. 2-adic SWEEP q ∈ {16,32,64,128,256}: real structure is consistent across
     powers of 2; look-elsewhere fires only at q=64.
  2. SPLIT-HALF: real => z>0 in both disjoint halves.
  3. DECISIVE target test — (X*Y) mod q vs:
        D mod q   (residual; D = d - base, base=A+⌊Ak/n⌋)
        d mod q   (the actual low bits of the private key)
        n mod q   (position denominator, control)
     If it tracks d mod q  => a genuine low-bit leak (extraordinary).
     If it tracks D but NOT d => artifact via the construction's `base`, not a
     leak of the key.  Also report bias-corrected MI in BITS (the real size).
Permutation null is the arbiter (χ² unreliable on these tables). Exact signal path.
"""
import csv, random, math
from math import gcd
random.seed(20260710); NMAX=256
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
def mi_nats_df(fa,tb):
    joint={};ca={};cb={}
    for a,b in zip(fa,tb):
        joint[(a,b)]=joint.get((a,b),0)+1; ca[a]=ca.get(a,0)+1; cb[b]=cb.get(b,0)+1
    N=len(fa); mi=0.0
    for (a,b),c in joint.items(): mi+=(c/N)*math.log((c*N)/(ca[a]*cb[b]))  # noqa: float
    return mi,(len(ca)-1)*(len(cb)-1),N
def zscore(fa,tb):
    mi,df,N=mi_nats_df(fa,tb)
    return ((2*N*mi-df)/math.sqrt(2*df)) if df>0 else 0.0, mi, df, N       # noqa: float
def mi_bits_bc(fa,tb):
    mi,df,N=mi_nats_df(fa,tb)
    return (mi-df/(2*N))/math.log(2)                                        # noqa: float
def perm_p(fa,tb,B=1000):
    z0,_,_,_=zscore(fa,tb); tb=tb[:]; ge=0
    for _ in range(B):
        random.shuffle(tb)
        if zscore(fa,tb)[0]>=z0: ge+=1
    return z0,(ge+1)/(B+1)                                                  # noqa: float

BITS=[];DS=[];XS=[];YS=[]
with open("constructed_keys_1to160_100k.csv") as fh:
    for r in csv.DictReader(fh):
        N=int(r["bits"])
        if N<64: continue
        BITS.append(N); DS.append(int(r["d"])); XS.append(int(r["X"],16)); YS.append(int(r["Y"],16))
M=len(XS); NS=[];DD=[]
for i in range(M):
    n,k=best_nk(DS[i],BITS[i]); A=1<<(BITS[i]-1); NS.append(n); DD.append(DS[i]-(A+(A*k)//n))

print(f"N>=64 keys: {M}\n")
print("2-adic sweep — (X*Y) mod q  vs {D, d, n} mod q  (perm p, MI in bits, split-half z):")
for q in (16,32,64,128,256):
    xy=[(XS[i]*YS[i])%q for i in range(M)]
    for tname,tv in (("D",DD),("d",DS),("n",NS)):
        tb=[v%q for v in tv]
        z0,pp=perm_p(xy,tb,B=1000)
        bits=mi_bits_bc(xy,tb)
        h=M//2
        z1,_,_,_=zscore(xy[:h],tb[:h]); z2,_,_,_=zscore(xy[h:],tb[h:])
        flag=" <==" if pp<0.01 else ""
        print(f"  q={q:<4d} (X*Y)mod q vs {tname} mod q: z={z0:+6.2f} p={pp:.3f} "
              f"MI_bc={bits:+.2e} bits  half z=({z1:+.2f},{z2:+.2f}){flag}")
    print()
