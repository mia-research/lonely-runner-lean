#!/usr/bin/env python3
"""
v2 — fix the two problems in v1:
 (A) VALIDATE my D-recursion against the dataset's own D_terms column (must match,
     else I'm testing the wrong recursion).
 (B) REAL positive controls (v1's (X+d)modl was a one-time-pad = 0 info):
       pos_full    = d mod l              -> must fire hard (p≈1/(B+1))
       pos_partial = d mod l, 55% corrupted-> weak real signal, tests sensitivity
Then the decisive frozen-(n,k) test at high N (D≡d up to const): does (X,Y) leak D?
Two frozen n (127 and 13 -> deeper recursion), N=200 & 248, larger M.
"""
import csv, random
import ecc_secp256k1 as E
import knd_common as K
rnd=random.Random(20260710)

def d1_terms(d,N,res):
    A=1<<(N-1); e=res
    if e==0: return 0,0
    D1=A//abs(e); cur=d-res; t=0
    while e!=0 and t<80:
        Di=A//abs(e)
        if Di==0: break
        cur+=(1 if e>0 else -1)*(A//Di); e=d-cur; t+=1
    return D1,t

# ---- (A) validate recursion vs dataset D_terms column ----
match=tot=0; hi_terms={}
for r in csv.DictReader(open("constructed_keys_1to160_100k.csv")):
    N=int(r["bits"])
    if N<100: continue
    d=int(r["d"]); n=int(r["n"]); k=int(r["k"])
    A=1<<(N-1); base=A+(A*k)//n; D=d-base
    _,t=d1_terms(d,N,D)
    tot+=1
    if "D_terms" in r and r["D_terms"]!="":
        if t==int(r["D_terms"]): match+=1
    if N>=125: hi_terms[t]=hi_terms.get(t,0)+1
print(f"(A) D-recursion vs dataset D_terms (bits>=100): {match}/{tot} match")
print(f"    my D_terms distribution at bits>=125: {dict(sorted(hi_terms.items()))}")

# ---- (B+C) frozen high-N with real controls ----
def gen(N,n,k,M):
    A=1<<(N-1); base=A+(A*k)//n; w=A//(512*n)
    X=[];Y=[];Ds=[];DT=[];dd=[]
    while len(X)<M:
        D=rnd.randrange(-w,w+1); d=base+D
        if d<A or d>=(1<<N) or K.best_nk(d,N)!=(n,k): continue
        pt=E.scalar_mul(d)
        if pt is None: continue
        _,t=d1_terms(d,N,D)
        X.append(pt[0]);Y.append(pt[1]);Ds.append(D);DT.append(t);dd.append(d)
    return X,Y,Ds,DT,dd

for (n,k,N) in [(127,64,248),(13,8,248),(13,8,200)]:
    M=12000
    X,Y,Ds,DT,dd=gen(N,n,k,M)
    print(f"\n=== frozen n={n},k={k}  N={N}  M={M}  mean D_terms={sum(DT)/M:.2f} "
          f"max={max(DT)} ===")
    for l in (7,13):
        # real positive controls
        pf=[d%l for d in dd]
        pp=[(dd[i]%l) if rnd.random()<0.45 else rnd.randrange(l) for i in range(M)]
        tb=[d%l for d in dd]
        _,cf=K.perm_p(pf,tb,K.gtest_z,B=200,worse="ge")
        _,cp=K.perm_p(pp,tb,K.gtest_z,B=200,worse="ge")
        print(f"  l={l} [controls] d%l vs d%l p={cf:.3f} (must≈0) ; 45%-signal p={cp:.3f} (should be small)")
        # real tests: (X,Y) features vs D (=d up to const)
        feats={"Xmod":[x%l for x in X],"XYmod":[(X[i]*Y[i])%l for i in range(M)],
               "v_l":[((Y[i]%l)**2-(X[i]%l)**3-7)%l for i in range(M)]}
        td=[v%l for v in Ds]
        cells=[]
        for fn,fa in feats.items():
            z=K.gtest_z(fa,td); mr,_=K.min_resid(fa,td)
            mark=""
            if abs(z)>2.5 or mr<-3.5:
                _,pz=K.perm_p(fa,td,K.gtest_z,B=300,worse="ge")
                mark=f"[MIp={pz:.3f}]"
            cells.append(f"{fn}:z={z:+.1f}/mr={mr:+.1f}{mark}")
        print(f"       vs D: " + "  ".join(cells))
