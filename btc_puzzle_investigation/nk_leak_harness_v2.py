#!/usr/bin/env python3
"""
n/k leak harness v2  (2026-07-06) -- CURVE-AWARE
================================================
Builds on v1 by taking the ideation seriously: the curve is designed to obscure
the link, so probe it WITH the curve's own structure instead of treating (X,Y)
as opaque integers.

New vs v1:
  Part B2  Curve-aware feature views: phi(P)=(beta*X,Y), phi^2(P), -P=(X,-Y),
           2P, and quadratic/cubic residue characters of X,Y. Ask directly:
           does curve-awareness BEAT raw-integer features at predicting n?
  Part D   Endomorphism structure-transfer: with known d, does the Farey
           coordinate n survive d -> lambda*d (the phi map) and d -> Nord-d
           (negation)?  MI(n, n_lambda), MI(n, n_neg). Tests "curve obscures link".
  Part E   Fiber-membership (stratification): kNN in curve-aware space -- does a
           held-out key sit in its own n-cloud better than chance? Per-n tightness.

Controls kept from v1: perm null on every distinguisher; planted positive control;
bounded phrasing. Ground-truth d/n/k/D used ONLY for labels + necessary-condition
transfer test; all FEATURES are public (X,Y,bits + public curve maps thereof).
"""
import argparse, math, random
from fractions import Fraction
import numpy as np, pandas as pd
from sympy import isprime

P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
Nord=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
BETA  =0x7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE
LAMBDA=0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72

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

def decompose(d, bits, max_den=256):
    A=1<<(bits-1); u=Fraction(d-A,A); f=u.limit_denominator(max_den)
    n,k=f.denominator,f.numerator; base=A+(A*k)//n
    return n,k,d-base
def decompose_any(d, max_den=256):
    if d<=1: return 1
    return decompose(d, d.bit_length(), max_den)[0]

SMALL_Q=[3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
SWEEP_M=list(range(2,65))
def feat_point(X,Y,prefix,full=False):
    f={f"{prefix}Yp":Y&1,f"{prefix}pX":bin(X).count("1"),f"{prefix}pY":bin(Y).count("1")}
    for q in SMALL_Q: f[f"{prefix}Xm{q}"]=X%q; f[f"{prefix}Ym{q}"]=Y%q; f[f"{prefix}XYm{q}"]=(X*Y)%q
    if full:
        f[f"{prefix}Xlo"]=X&0xFFFF; f[f"{prefix}Ylo"]=Y&0xFFFF
        for m in SWEEP_M: f[f"{prefix}Xs{m}"]=X%m; f[f"{prefix}Ys{m}"]=Y%m
    return f
def chi(v,e): return pow(v%P,(P-1)//e,P)
def features(X,Y,bits):
    f={"bits":bits}
    f.update(feat_point(X,Y,"",full=True))                     # raw P (base battery)
    # ---- curve-aware public views ----
    phiX=BETA*X%P; f.update(feat_point(phiX,Y,"phi"))          # phi(P)=(beta X, Y)=lambda.P
    phi2X=BETA*phiX%P; f.update(feat_point(phi2X,Y,"phi2"))    # phi^2(P)
    f.update(feat_point(X,(-Y)%P,"neg"))                       # -P=(X,-Y) = pubkey of Nord-d
    dbl=ec_mul(2,(X,Y)); f.update(feat_point(dbl[0],dbl[1],"dbl"))
    f["chi2X"]=chi(X,2); f["chi3X"]=chi(X,3)%1000; f["chi2Y"]=chi(Y,2)  # residue characters
    return f
BASE_KEYS=None  # filled after first row to split base vs curve feature columns

def eval_target(Xmat,y,kind,planted=None,reps=12,seed=0,knn=False):
    from sklearn.ensemble import HistGradientBoostingClassifier as HGBC, HistGradientBoostingRegressor as HGBR
    from sklearn.neighbors import KNeighborsClassifier
    from sklearn.preprocessing import StandardScaler
    from sklearn.model_selection import train_test_split
    rng=np.random.default_rng(seed)
    Xin=Xmat if planted is None else np.column_stack([Xmat,planted])
    def one(yv):
        Xtr,Xte,ytr,yte=train_test_split(Xin,yv,test_size=0.3,random_state=1)
        if knn:
            sc=StandardScaler().fit(Xtr); Xtr,Xte=sc.transform(Xtr),sc.transform(Xte)
            m=KNeighborsClassifier(n_neighbors=15).fit(Xtr,ytr)
            proba=m.predict_proba(Xte); cls=m.classes_
            top5=cls[np.argsort(proba,axis=1)[:,-5:]]
            return np.mean([yt in row for yt,row in zip(yte,top5)])
        if kind=="reg":
            m=HGBR(max_iter=180,random_state=1).fit(Xtr,ytr)
            p=m.predict(Xte); return 1-((yte-p)**2).sum()/((yte-yte.mean())**2).sum()
        m=HGBC(max_iter=180,random_state=1).fit(Xtr,ytr)
        if kind=="top5":
            proba=m.predict_proba(Xte); cls=m.classes_
            top5=cls[np.argsort(proba,axis=1)[:,-5:]]
            return np.mean([yt in row for yt,row in zip(yte,top5)])
        return m.score(Xte,yte)
    real=one(y); null=np.array([one(rng.permutation(y)) for _ in range(reps)])
    mu,sd=null.mean(),null.std()+1e-12
    return real,mu,sd,(real-mu)/sd

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--csv",default="constructed_keys_1to160_100k.csv")
    ap.add_argument("--sample",type=int,default=25000); ap.add_argument("--seed",type=int,default=0)
    a=ap.parse_args(); random.seed(a.seed); np.random.seed(a.seed)
    df=pd.read_csv(a.csv); df["Xi"]=df.X.apply(lambda s:int(s,16)); df["Yi"]=df.Y.apply(lambda s:int(s,16))
    print(f"loaded {len(df)} keys; bits {df.bits.min()}..{df.bits.max()}")

    print("\n=== Part A: validation gates (must pass) ===")
    phiG=(BETA*Gx%P,Gy); print(f"  endomorphism  phi(G)==lambda*G : {phiG==ec_mul(LAMBDA)}")
    chk=df.sample(150,random_state=a.seed); ec=dec=0
    for _,r in chk.iterrows():
        ec+= (ec_mul(int(r.d))==(int(r.Xi),int(r.Yi))); dec+=(decompose(int(r.d),int(r.bits))==(r.n,r.k,r.D))
    print(f"  EC reproduces (X,Y):  {ec}/{len(chk)}   decompose reproduces (n,k,D): {dec}/{len(chk)}")

    # ---- Part D: structure-transfer (cheap, full 100k) ----
    print("\n=== Part D: does Farey coord n survive the curve's maps? (needs known d) ===")
    from sklearn.metrics import mutual_info_score
    sd_=df.sample(min(30000,len(df)),random_state=a.seed)
    nL=[decompose_any(LAMBDA*int(d)%Nord) for d in sd_.d]
    nN=[decompose_any((Nord-int(d))%Nord) for d in sd_.d]
    nT=sd_.n.values
    Hn=mutual_info_score(nT,nT)
    print(f"  H(n) (self-MI upper bound)        : {Hn:.4f} nat")
    print(f"  MI(n, n_lambda) [phi endomorphism]: {mutual_info_score(nT,nL):.4f} nat   (>0 => curve carries a 2nd view)")
    print(f"  MI(n, n_neg)    [negation -P]     : {mutual_info_score(nT,nN):.4f} nat")
    print(f"  MI(n, shuffled) [null]            : {mutual_info_score(nT,np.random.permutation(nT)):.4f} nat")

    # ---- feature build ----
    s=df.sample(min(a.sample,len(df)),random_state=a.seed).reset_index(drop=True)
    print(f"\nbuilding curve-aware features on {len(s)} keys ...")
    feats=[features(int(x),int(y),int(b)) for x,y,b in zip(s.Xi,s.Yi,s.bits)]
    Fdf=pd.DataFrame(feats).fillna(0)
    base_cols=[c for c in Fdf.columns if not c.startswith(("phi","phi2","neg","dbl","chi"))]
    Xall=Fdf.values.astype(float); Xbase=Fdf[base_cols].values.astype(float)
    print(f"  {Xall.shape[0]} keys | base feats={Xbase.shape[1]} | +curve feats total={Xall.shape[1]}")

    print("\n=== Part B: positive control (MUST fire) ===")
    planted=((s.n.values%5)+ (np.random.rand(len(s))<0.2)*np.random.randint(1,5,len(s)))%5
    r,mu,sd,z=eval_target(Xall,(s.n.values%5),"clf",planted=planted.reshape(-1,1).astype(float),seed=a.seed)
    print(f"  n mod 5 w/ planted feature: acc={r:.3f} null={mu:.3f}±{sd:.3f} z={z:+.1f}  (large => pipeline is sensitive)")

    print("\n=== Part B2: does CURVE-AWARENESS beat raw integers at predicting n? ===")
    for name,kind,y in [("n top-5","top5",s.n.values),
                        ("n is prime","clf",s.n.apply(lambda v:int(isprime(int(v)))).values),
                        ("log2 n [R2]","reg",np.log2(s.n.values.astype(float))),
                        ("D_terms","clf",s.D_terms.values)]:
        rb,mb,sb,zb=eval_target(Xbase,y,kind,seed=a.seed)
        ra,ma,sa,za=eval_target(Xall,y,kind,seed=a.seed)
        print(f"  {name:14s} | RAW: real={rb:.4f} adv={rb-mb:+.4f} z={zb:+.2f}"
              f"  || CURVE: real={ra:.4f} adv={ra-ma:+.4f} z={za:+.2f}")

    print("\n=== Part E: fiber-membership (kNN in curve-aware space) ===")
    rk,mk,sk,zk=eval_target(Xall,s.n.values,"top5",seed=a.seed,knn=True)
    print(f"  kNN n top-5: real={rk:.4f} null={mk:.4f}±{sk:.4f} z={zk:+.2f}  (>null => points cluster in n-fibers)")

    print("\n--- bounded conclusion ---")
    print(f"  Advantages are 'distinguishing advantage <= (real-null) at N={len(s)}'.")
    print("  A lead requires: z large, curve>raw, and survives fresh seed + bigger N.")

if __name__=="__main__": main()
