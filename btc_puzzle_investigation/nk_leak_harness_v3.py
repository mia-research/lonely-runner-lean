#!/usr/bin/env python3
"""
n/k leak harness v3  (2026-07-06) -- bugfix + chase the one blip
================================================================
v2 gave: n-top5, n-prime => null (curve no better than raw). log2(n) R^2 showed
CURVE z=+3.99 (raw z=+0.99) at one seed -- a weak above-null blip on a TINY effect
(R^2~0.002). Two things to settle, honestly:
  (1) Is it the `bits` confound?  Small bands (N<=~9) are enumerable and have
      non-generic n-distributions, so log2(n) is partly predictable from bits
      ALONE -- present in raw AND curve. Isolate with a bits-only baseline.
  (2) Does the curve>raw gap survive a fresh seed + larger N + more permutations,
      or is it look-elsewhere across the ~8 tests? (the F1 / d-mod-23 discipline)

Fixes: HGB early_stopping=False (kills the stratified-split crash on rare D_terms).
Adds:  bits-only baseline for log2(n); |corr| feature screen to see what drives it;
       two seeds. Everything still perm-null controlled + positive control.
"""
import argparse, math, random
from fractions import Fraction
import numpy as np, pandas as pd
from sympy import isprime

P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
BETA=0x7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE
def decompose(d,bits,md=256):
    A=1<<(bits-1); f=Fraction(d-A,A).limit_denominator(md); n,k=f.denominator,f.numerator
    return n,k,d-(A+(A*k)//n)
SMALL_Q=[3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
SWEEP_M=list(range(2,65))
def fp(X,Y,pfx,full=False):
    f={f"{pfx}Yp":Y&1,f"{pfx}pX":bin(X).count("1"),f"{pfx}pY":bin(Y).count("1")}
    for q in SMALL_Q: f[f"{pfx}Xm{q}"]=X%q; f[f"{pfx}Ym{q}"]=Y%q; f[f"{pfx}XYm{q}"]=(X*Y)%q
    if full:
        f[f"{pfx}Xlo"]=X&0xFFFF; f[f"{pfx}Ylo"]=Y&0xFFFF
        for m in SWEEP_M: f[f"{pfx}Xs{m}"]=X%m; f[f"{pfx}Ys{m}"]=Y%m
    return f
def chi(v,e): return pow(v%P,(P-1)//e,P)
def features(X,Y,bits):
    f={"bits":bits}; f.update(fp(X,Y,"",True))
    px=BETA*X%P; f.update(fp(px,Y,"phi")); f.update(fp(BETA*px%P,Y,"phi2")); f.update(fp(X,(-Y)%P,"neg"))
    f["chi2X"]=chi(X,2); f["chi3X"]=chi(X,3)%1000; f["chi2Y"]=chi(Y,2)
    return f

def evalt(Xin,y,kind,reps=20,seed=0):
    from sklearn.ensemble import HistGradientBoostingClassifier as C, HistGradientBoostingRegressor as R
    from sklearn.model_selection import train_test_split
    rng=np.random.default_rng(seed)
    def one(yv):
        Xtr,Xte,ytr,yte=train_test_split(Xin,yv,test_size=0.3,random_state=1)
        if kind=="reg":
            m=R(max_iter=200,early_stopping=False,random_state=1).fit(Xtr,ytr)
            p=m.predict(Xte); return 1-((yte-p)**2).sum()/((yte-yte.mean())**2).sum()
        m=C(max_iter=200,early_stopping=False,random_state=1).fit(Xtr,ytr)
        if kind=="top5":
            pr=m.predict_proba(Xte); cl=m.classes_; t5=cl[np.argsort(pr,axis=1)[:,-5:]]
            return np.mean([a in b for a,b in zip(yte,t5)])
        return m.score(Xte,yte)
    real=one(y); null=np.array([one(rng.permutation(y)) for _ in range(reps)])
    return real,null.mean(),null.std()+1e-12,(real-null.mean())/(null.std()+1e-12)

def main():
    ap=argparse.ArgumentParser(); ap.add_argument("--csv",default="constructed_keys_1to160_100k.csv")
    ap.add_argument("--sample",type=int,default=40000); a=ap.parse_args()
    df=pd.read_csv(a.csv); df["Xi"]=df.X.apply(lambda s:int(s,16)); df["Yi"]=df.Y.apply(lambda s:int(s,16))
    print(f"loaded {len(df)} keys")

    for seed in (0,1):
        print(f"\n########## SEED {seed}, sample {a.sample} ##########")
        random.seed(seed); np.random.seed(seed)
        s=df.sample(min(a.sample,len(df)),random_state=seed).reset_index(drop=True)
        F=pd.DataFrame([features(int(x),int(y),int(b)) for x,y,b in zip(s.Xi,s.Yi,s.bits)]).fillna(0)
        base=[c for c in F.columns if not c.startswith(("phi","phi2","neg","chi"))]
        Xall=F.values.astype(float); Xbase=F[base].values.astype(float)
        Xbits=F[["bits"]].values.astype(float)
        y_log=np.log2(s.n.values.astype(float))

        # positive control
        pl=((s.n.values%5)+(np.random.rand(len(s))<0.2)*np.random.randint(1,5,len(s)))%5
        r,mu,sd,z=evalt(np.column_stack([Xall,pl.reshape(-1,1)]),(s.n.values%5),"clf",seed=seed)
        print(f"  [pos ctrl] n%5 acc={r:.3f} null={mu:.3f} z={z:+.1f}")

        # log2(n): confound isolation
        print("  log2(n) R^2:")
        for nm,Xin in [("bits-only ",Xbits),("base      ",Xbase),("curve(all)",Xall)]:
            r,mu,sd,z=evalt(Xin,y_log,"reg",seed=seed)
            print(f"    {nm}: real={r:+.4f} null={mu:+.4f}±{sd:.4f} adv={r-mu:+.4f} z={z:+.2f}")

        # n-prime + n-top5 recap at this seed
        for nm,kind,y in [("n is prime","clf",s.n.apply(lambda v:int(isprime(int(v)))).values),
                          ("n top-5   ","top5",s.n.values)]:
            r,mu,sd,z=evalt(Xall,y,kind,seed=seed)
            print(f"  {nm} (curve): real={r:.4f} null={mu:.4f} adv={r-mu:+.4f} z={z:+.2f}")

        if seed==0:
            # what drives any log2(n) signal? |corr| of each feature with log2(n)
            cor=F.apply(lambda c: np.corrcoef(c.values.astype(float),y_log)[0,1] if c.std()>0 else 0.0)
            top=cor.abs().sort_values(ascending=False).head(10)
            print("  top-10 |corr(feature, log2 n)|:")
            for name,val in top.items(): print(f"    {name:10s} {cor[name]:+.4f}")
    print("\n--- bounded conclusion ---")
    print("  A lead requires curve>base>bits-only AND z stable across both seeds.")

if __name__=="__main__": main()
