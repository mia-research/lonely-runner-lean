#!/usr/bin/env python3
"""
The full-bit-range dataset the user asked for: random constructed keys spanning
N = 132..252 (the 100k set stopped ~130). Unfrozen (natural n,k,D). Two goals:
  1. Report D_terms across the FULL range (does the recursion depth grow with N?).
  2. Test (X,Y) residues -> d mod l DIRECTLY (d is the key; no base confound) with
     REAL positive controls, pooled and in a high-N-only slice.
Exact ECC construction. Permutation-validated.
"""
import random
import ecc_secp256k1 as E
import knd_common as K
rnd=random.Random(1234)

def d1_terms(d,N,res):
    A=1<<(N-1); e=res
    if e==0: return 0,0
    cur=d-res; t=0
    while e!=0 and t<80:
        Di=A//abs(e)
        if Di==0: break
        cur+=(1 if e>0 else -1)*(A//Di); e=d-cur; t+=1
    return 0,t

X=[];Y=[];DS=[];BITS=[];DT=[]
Ns=list(range(132,253,4))
per=380
for N in Ns:
    A=1<<(N-1)
    for _ in range(per):
        d=A+rnd.randrange(A)
        n,k=K.best_nk(d,N); base=A+(A*k)//n; res=d-base
        pt=E.scalar_mul(d)
        if pt is None: continue
        _,t=d1_terms(d,N,res)
        X.append(pt[0]);Y.append(pt[1]);DS.append(d);BITS.append(N);DT.append(t)
M=len(X)
print(f"full-range dataset: {M} keys, N in [{Ns[0]},{Ns[-1]}]")

# D_terms across the range (low/mid/high thirds)
def terms_dist(lo,hi):
    dd={}
    for i in range(M):
        if lo<=BITS[i]<hi: dd[DT[i]]=dd.get(DT[i],0)+1
    return dict(sorted(dd.items()))
print(f"  D_terms N<170:  {terms_dist(0,170)}")
print(f"  D_terms 170-210:{terms_dist(170,210)}")
print(f"  D_terms N>=210: {terms_dist(210,999)}")

# test (X,Y) -> d mod l, pooled and high-N slice, with real controls
def run(idx,label):
    m=len(idx)
    print(f"\n{label} (m={m}):")
    for l in (7,13):
        dd=[DS[i]%l for i in idx]
        pf=[DS[i]%l for i in idx]                             # full control
        pp=[(DS[i]%l) if rnd.random()<0.4 else rnd.randrange(l) for i in idx]
        _,cf=K.perm_p(pf,dd,K.gtest_z,B=200,worse="ge")
        _,cp=K.perm_p(pp,dd,K.gtest_z,B=200,worse="ge")
        feats={"Xmod":[X[i]%l for i in idx],
               "XYmod":[(X[i]*Y[i])%l for i in idx],
               "v_l":[((Y[i]%l)**2-(X[i]%l)**3-7)%l for i in idx]}
        cells=[]
        for fn,fa in feats.items():
            z=K.gtest_z(fa,dd); mr,_=K.min_resid(fa,dd)
            mark=""
            if abs(z)>2.5 or mr<-3.5:
                _,pz=K.perm_p(fa,dd,K.gtest_z,B=300,worse="ge"); mark=f"[p={pz:.3f}]"
            cells.append(f"{fn}:z={z:+.1f}/mr={mr:+.1f}{mark}")
        print(f"  l={l} controls: full p={cf:.3f} / 40%-signal p={cp:.3f} ;  "
              + "  ".join(cells))

run(list(range(M)),"POOLED all N")
run([i for i in range(M) if BITS[i]>=210],"HIGH-N slice (N>=210)")
