#!/usr/bin/env python3
"""
Frozen-(n,k) HIGH-N test — the sharpest version of the D-recursion question.

Fix n,k => base = A+floor(A*k/n) is CONSTANT => d = base + D.  Therefore D and d
differ only by a constant, so (X,Y) leaking D mod l  <=>  leaking d mod l  (the
base-confound that neutralised every prior D-hit is GONE). We sweep N to test the
user's hypothesis directly: if the recursive error leaks, LONGER N (richer
recursion, 5-6 terms) is where it shows. Keys constructed d -> P=d·G (exact ECC).

Planted POSITIVE CONTROL: feature (X+d) mod l MUST leak d — proves the detector
works at this N and cardinality. Everything permutation-validated.
"""
import random
import ecc_secp256k1 as E
import knd_common as K
rnd=random.Random(20260710)

def best_nk(d,N): return K.best_nk(d,N)
def d1_terms(d,N,res):
    A=1<<(N-1); e=res
    if e==0: return 0,0
    D1=A//abs(e); cur=d-res; t=0
    while e!=0 and t<64:
        Di=A//abs(e)
        if Di==0: break
        cur+=(1 if e>0 else -1)*(A//Di); e=d-cur; t+=1
    return D1,t

def gen(N,n,k,M):
    A=1<<(N-1); base=A+(A*k)//n; w=A//(512*n)
    Xs=[];Ys=[];Ds=[];D1s=[];DTs=[];dd=[];bad=0
    while len(Xs)<M:
        D=rnd.randrange(-w,w+1); d=base+D
        if d< A or d>=(1<<N): continue
        if best_nk(d,N)!=(n,k): bad+=1; continue
        pt=E.scalar_mul(d)
        if pt is None: continue
        x,y=pt; D1,t=d1_terms(d,N,D)
        Xs.append(x);Ys.append(y);Ds.append(D);D1s.append(D1);DTs.append(t);dd.append(d)
    return Xs,Ys,Ds,D1s,DTs,dd,bad,w

print("frozen n=127,k=64 ; sweeping N (larger N = richer D-recursion):")
for N in (160,208,248):
    M=9000
    Xs,Ys,Ds,D1s,DTs,dd,bad,w=gen(N,127,64,M)
    avgT=sum(DTs)/len(DTs)
    print(f"\n=== N={N}  M={M}  window≈2^{w.bit_length()-1}  mean D_terms={avgT:.2f} "
          f"(reject {bad} off-cell) ===")
    # planted positive control: (X+d) mod l leaks d
    for l in (7,13):
        fa=[(Xs[i]+dd[i])%l for i in range(M)]; tb=[dd[i]%l for i in range(M)]
        _,pc=K.perm_p(fa,tb,K.gtest_z,B=200,worse="ge")
        print(f"  [control] (X+d) mod {l} vs d mod {l}: MI perm p={pc:.3f}  (must be small)")
    # real tests: (X,Y) features vs D / D1 / D_terms  (= d, since base const)
    for l in (7,13):
        feats={"Xmod":[x%l for x in Xs],
               "XYmod":[(Xs[i]*Ys[i])%l for i in range(M)],
               "v_l":[((Ys[i]%l)**2-(Xs[i]%l)**3-7)%l for i in range(M)]}
        tgts={"Dmod":[v%l for v in Ds],"D1mod":[v%l for v in D1s],
              "DT":[min(t,7) for t in DTs]}
        for fn,fa in feats.items():
            cells=[]
            for tn,tb in tgts.items():
                z=K.gtest_z(fa,tb); mr,_=K.min_resid(fa,tb)
                mark=""
                if abs(z)>3 or mr<-4:
                    _,pz=K.perm_p(fa,tb,K.gtest_z,B=300,worse="ge")
                    _,pm=K.perm_p(fa,tb,lambda a,b:K.min_resid(a,b)[0],B=300,worse="le")
                    mark=f"[MIp={pz:.3f}/exl={pm:.3f}]"
                cells.append(f"{tn}:z={z:+.1f}/mr={mr:+.1f}{mark}")
            print(f"  l={l:>2} {fn:6s}: " + "  ".join(cells))
