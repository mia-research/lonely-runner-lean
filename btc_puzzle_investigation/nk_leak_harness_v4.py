#!/usr/bin/env python3
"""
n/k leak harness v4  (2026-07-06) -- systematic battery over the REMAINING ideas
================================================================================
The supervised (X,Y)->n ceiling (v2/v3) came back null with a sensitive control.
This run tests the idea clusters NOT covered by that ceiling, each -> number + null:

  Part 1  Necessary-condition MI screen (known d): does the quantity even correlate
          with n given full access?  d mod l (Frobenius), Y-parity, sign(D), chi3(X),
          D_terms.  MI minus shuffle-null (bias-corrected).            [ideas 8,6; upg6]
  Part 2  GLV (d1 mod n, d2 mod n) clustering: conditional entropy vs uniform.  [upg3]
  Part 3  Marginals vs MATCHED-UNIFORM null: n vs phi(n)/sampler, D_terms vs
          Gauss-Kuzmin, n-prime rate z, Y-parity.        [cross-ref 8,10; mirror 3,7]
  Part 4  Fiber-membership kNN: does a held-out key's n match its neighbours' n
          above chance? per-n purity.                    [amorphous 1,5; mirror 10]
  Part 5  D=0 exact-match structural fact: D_terms==0 => P==base*G exactly (the only
          regime where the "closest base point" attack is real).            [upg4]

Everything cheap + foreground-friendly. Public vs known-d annotated per test.
"""
import math, random
from fractions import Fraction
from collections import Counter, defaultdict
import numpy as np, pandas as pd
from sympy import isprime
from sklearn.metrics import mutual_info_score

P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
Nord=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
BETA=0x7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE
LAMBDA=0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72
a1=0x3086D221A7D46BCDE86C90E49284EB15; b1=-0xE4437ED6010E88286F547FA90ABFE4C3
a2=0x114CA50F7A8E2F3F657C1108D9D44CFD8; b2=0x3086D221A7D46BCDE86C90E49284EB15

def ec_add(A,B):
    if A is None: return B
    if B is None: return A
    x1,y1=A; x2,y2=B
    if x1==x2 and (y1+y2)%P==0: return None
    l=((3*x1*x1)*pow(2*y1,-1,P) if A==B else (y2-y1)*pow(x2-x1,-1,P))%P
    x3=(l*l-x1-x2)%P; return (x3,(l*(x1-x3)-y1)%P)
def ec_mul(k,Pt=(Gx,Gy)):
    R=None
    while k:
        if k&1:R=ec_add(R,Pt)
        Pt=ec_add(Pt,Pt);k>>=1
    return R
def decompose(d,bits,md=256):
    A=1<<(bits-1); f=Fraction(d-A,A).limit_denominator(md); n,k=f.denominator,f.numerator
    return n,k,d-(A+(A*k)//n)
def glv(d):
    c1=round(Fraction(b2*d,Nord)); c2=round(Fraction(-b1*d,Nord))
    d1=(d-c1*a1-c2*a2)%Nord; d2=(-c1*b1-c2*b2)%Nord
    if d1>Nord//2: d1-=Nord
    if d2>Nord//2: d2-=Nord
    return d1,d2
def mi_adj(x,y,rng):
    x=np.asarray(x); y=np.asarray(y)
    real=mutual_info_score(x,y); null=np.mean([mutual_info_score(x,rng.permutation(y)) for _ in range(5)])
    return real,null,real-null

def main():
    rng=np.random.default_rng(0); random.seed(0)
    df=pd.read_csv("constructed_keys_1to160_100k.csv")
    df["Xi"]=df.X.apply(lambda s:int(s,16)); df["Yi"]=df.Y.apply(lambda s:int(s,16))
    print(f"loaded {len(df)} keys"); n=df.n.values

    print("\n=== Part 1: necessary-condition MI screen (uses known d) [MI - null, nat] ===")
    print("  (quantity ~ n given full d-access; adv>0 => passes stage-1; PUBLIC? flags attack-reachability)")
    d=df.d.values.astype(object)
    for lab,q,pub in [("d mod 3",[int(v)%3 for v in df.d],"no(needs d)"),
                      ("d mod 5",[int(v)%5 for v in df.d],"no"),
                      ("d mod 7",[int(v)%7 for v in df.d],"no"),
                      ("d mod 11",[int(v)%11 for v in df.d],"no"),
                      ("Y parity",(df.Yi.values&1),"YES(public)"),
                      ("sign(D)",np.sign(df.D.values),"no"),
                      ("D_terms",df.D_terms.values,"no"),
                      ("chi3(X)cls",[pow(int(x),(P-1)//3,P)%3 for x in df.Xi],"YES(public)")]:
        r,nu,adv=mi_adj(q,n,rng); print(f"  {lab:12s} PUBLIC={pub:11s}: MI={r:.4f} null={nu:.4f} adv={adv:+.4f}")

    print("\n=== Part 2: GLV (d1 mod n, d2 mod n) clustering (uses known d) [upg3] ===")
    sg=df.sample(20000,random_state=0)
    # gate: verify split
    ok=all(((glv(int(r.d))[0]+glv(int(r.d))[1]*LAMBDA)%Nord==int(r.d)%Nord) for _,r in sg.head(20).iterrows())
    print(f"  GLV split gate (d1+d2*lambda==d mod Nord): {ok}")
    clust={}
    for _,r in sg.iterrows():
        d1,d2=glv(int(r.d)); nn=int(r.n)
        clust.setdefault(nn,[]).append((d1%nn,d2%nn))
    ent_ratio=[]
    for nn,pairs in clust.items():
        if nn<2 or len(pairs)<30: continue
        c=Counter(pairs); tot=len(pairs); pr=np.array(list(c.values()))/tot
        H=-(pr*np.log2(pr)).sum(); Hmax=2*math.log2(nn)
        ent_ratio.append(H/Hmax if Hmax>0 else 1.0)
    er=np.array(ent_ratio)
    print(f"  mean H/Hmax over n-groups (>=30 keys): {er.mean():.4f}  (1.0=uniform=no clustering; <0.9 notable)  [{len(er)} groups]")

    print("\n=== Part 3: marginals vs matched-uniform null [cross-ref 8,10; mirror 3,7] ===")
    # matched null: uniform random d per bit-band, same multiset, real decomposition
    null_n=[]; null_dt=Counter()
    for bits,cnt in df.bits.value_counts().items():
        A=1<<(bits-1); hi=1<<bits
        for _ in range(min(cnt,1500)):
            dd=random.randrange(A,hi); nn,kk,DD=decompose(dd,bits)
            null_n.append(nn)
            # crude D_terms proxy: recompute via limit_denominator convergent depth ~ skip; use 0 if DD==0
            null_dt[0 if DD==0 else 1]+=1
    null_n=np.array(null_n)
    p0=np.mean([isprime(int(v)) for v in null_n]); pobs=np.mean([isprime(int(v)) for v in n])
    se=math.sqrt(p0*(1-p0)/len(n)); z=(pobs-p0)/se
    print(f"  P(n prime): observed={pobs:.4f} matched-null={p0:.4f}  z={z:+.2f}")
    # n-distribution chi-square (top denominators)
    from collections import Counter as Ct
    obs=Ct(n); nul=Ct(null_n); keys=sorted(set(list(obs)[:50]))
    print(f"  most common n observed: {[k for k,_ in Ct(n).most_common(8)]}")
    print(f"  most common n matched : {[k for k,_ in Ct(null_n).most_common(8)]}")
    dt_obs=Counter(0 if v==0 else 1 for v in df.D.values)
    print(f"  P(D==0): observed={dt_obs[0]/len(df):.4f} matched-null={null_dt[0]/sum(null_dt.values()):.4f}")
    print(f"  Y-parity marginal: {(df.Yi.values&1).mean():.4f} (0.5=unbiased)")

    print("\n=== Part 4: fiber-membership kNN (public features) [amorphous 1,5; mirror 10] ===")
    from sklearn.neighbors import KNeighborsClassifier
    from sklearn.preprocessing import StandardScaler
    from sklearn.model_selection import train_test_split
    s=df.sample(8000,random_state=0).reset_index(drop=True)
    Q=[3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61]
    def kf(X,Y,b):
        f={"bits":b,"Yp":Y&1}
        for q in Q: f[f"X{q}"]=X%q; f[f"Y{q}"]=Y%q
        for m in range(2,48): f[f"Xs{m}"]=X%m
        return f
    F=pd.DataFrame([kf(int(x),int(y),int(b)) for x,y,b in zip(s.Xi,s.Yi,s.bits)]).values.astype(float)
    y=s.n.values
    def knn_top5(Y):
        a,b,c,d=train_test_split(F,Y,test_size=0.3,random_state=1)
        sc=StandardScaler().fit(a); a,b=sc.transform(a),sc.transform(b)
        m=KNeighborsClassifier(n_neighbors=15).fit(a,c); pr=m.predict_proba(b)
        cl=m.classes_; t=cl[np.argsort(pr,1)[:,-5:]]
        return np.mean([u in v for u,v in zip(d,t)])
    real=knn_top5(y); nul=np.array([knn_top5(rng.permutation(y)) for _ in range(8)])
    print(f"  kNN n top-5: real={real:.4f} null={nul.mean():.4f}±{nul.std():.4f} z={(real-nul.mean())/(nul.std()+1e-12):+.2f}")

    print("\n=== Part 5: D=0 exact-match structural fact [upg4] ===")
    z0=df[df.D==0].sample(min(5,len(df[df.D==0])),random_state=0) if (df.D==0).any() else df.head(0)
    okz=0
    for _,r in z0.iterrows():
        A=1<<(int(r.bits)-1); base=A+(A*int(r.k))//int(r.n)
        okz+= (ec_mul(base)==(int(r.Xi),int(r.Yi)))
    print(f"  D==0 keys with P==base*G exactly: {okz}/{len(z0)}  (frac of dataset with D==0: {(df.D==0).mean():.3f})")
    print("  => 'closest base point' is a real hit ONLY on the D==0 subset (a known label); D!=0 => P-B random.")
    print("\nDONE")

if __name__=="__main__": main()
