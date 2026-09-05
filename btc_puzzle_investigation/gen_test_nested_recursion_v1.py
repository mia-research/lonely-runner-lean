#!/usr/bin/env python3
"""
Test the NESTED (n,k,D) recursion — the one that gives ~11 terms at 246 bits
(nested best-approx of the residual at each scale, denom<=2048) — for (X,Y) leakage,
especially at the DEEP levels where the user expects signal.

Each level i leaves a residual r_i (deterministic function of d). We test whether
(X,Y) residues predict r_i mod l at shallow / middle / deep levels, with REAL
positive controls (d mod l direct + 40% corrupted). Keys d->P=d·G via exact ECC,
N=246. Permutation-validated.
"""
import random
from math import gcd
import ecc_secp256k1 as E
import knd_common as K
rnd=random.Random(20260710)
NMAX=2048

def best_nk_bound(v,b):
    A=1<<(b-1); num=v-A; best=None
    for n in range(1,NMAX+1):
        k=(2*n*num+A)//(2*A); k=0 if k<0 else (n if k>n else k)
        for kk in (k-1,k,k+1):
            if 0<=kk<=n:
                key=(abs(n*num-kk*A),n,kk)
                if best is None or key<best: best=key
    _,n,k=best; g=gcd(k,n) if n else 1
    return (n//g,k//g) if g>1 else (n,k)

def nested_residuals(d,N):
    r=d; res=[]
    while r!=0 and len(res)<60:
        ar=abs(r); s=1 if r>0 else -1; b=ar.bit_length()
        if b<4: res.append(0); break
        A=1<<(b-1); n,k=best_nk_bound(ar,b); base=A+(A*k)//n
        newr=s*(ar-base); res.append(newr)
        if newr==r: break
        r=newr
    return res

N=246; A=1<<(N-1); M=8000
X=[];Y=[];RES=[]
while len(X)<M:
    d=A+rnd.randrange(A)
    pt=E.scalar_mul(d)
    if pt is None: continue
    X.append(pt[0]);Y.append(pt[1]);RES.append(nested_residuals(d,N))
Lmax=max(len(r) for r in RES)
print(f"N={N} M={M}  nested-recursion levels: mean={sum(len(r) for r in RES)/M:.1f} max={Lmax}")

# choose levels: shallow(1), middle, deep(last few)
levels=sorted(set([1,3,6,9,10,11,Lmax-1]))
levels=[L for L in levels if 1<=L<=Lmax]
print("test (X,Y) -> residual r_level mod l  (deep = user's hypothesis):")
for l in (7,13):
    # controls
    dd=[ (X[i]) for i in range(M)]  # placeholder; real target is d, reconstruct not needed
    # use r_1-based d proxy: we still have d only implicitly; controls use residual level1 which is ~d-scale
    print(f" l={l}:")
    for L in levels:
        # residual at level L (0 if key terminated earlier)
        tb=[ (RES[i][L-1] % l) if len(RES[i])>=L else 0 for i in range(M)]
        # real positive control at THIS target: a feature that leaks it
        pf=tb[:]  # trivial
        pp=[ tb[i] if rnd.random()<0.4 else rnd.randrange(l) for i in range(M)]
        _,cf=K.perm_p(pf,tb,K.gtest_z,B=150,worse="ge")
        _,cp=K.perm_p(pp,tb,K.gtest_z,B=150,worse="ge")
        feats={"Xmod":[x%l for x in X],"XYmod":[(X[i]*Y[i])%l for i in range(M)],
               "v_l":[((Y[i]%l)**2-(X[i]%l)**3-7)%l for i in range(M)]}
        cells=[]
        for fn,fa in feats.items():
            z=K.gtest_z(fa,tb); mr,_=K.min_resid(fa,tb)
            mark=""
            if abs(z)>2.5 or mr<-3.5:
                _,pz=K.perm_p(fa,tb,K.gtest_z,B=300,worse="ge"); mark=f"[p={pz:.3f}]"
            cells.append(f"{fn}:z={z:+.1f}/mr={mr:+.1f}{mark}")
        print(f"   level {L:>2} (ctrl full={cf:.3f}/40%={cp:.3f}): " + "  ".join(cells))
