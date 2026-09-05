#!/usr/bin/env python3
"""nk_retest_v1 -- methodology-fixed full retest (addresses self-audit holes).
Full 100k | high-band pool for power | 25-perm nulls w/ empirical p |
Westfall-Young max-stat FWER | broadened public feature set."""
import numpy as np, pandas as pd
from sympy import primerange, isprime, totient
from sklearn.ensemble import HistGradientBoostingClassifier as CLF, HistGradientBoostingRegressor as REG
from sklearn.model_selection import train_test_split
P=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
BETA=0x7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE
PRIMES=list(primerange(3,180))               # 40 primes
PQ=[3,5,7,11,13]
def features(X,Y,include_bits,bits):
    f={}
    if include_bits: f["bits"]=bits
    f["pX"]=bin(X).count("1"); f["pY"]=bin(Y).count("1"); f["pXY"]=bin(X^Y).count("1")
    f["Yp"]=Y&1; f["Xlo"]=X&0xFFFF; f["Ylo"]=Y&0xFFFF
    f["Xhi"]=X>>(max(1,X.bit_length()-16)); f["Yhi"]=Y>>(max(1,Y.bit_length()-16))
    for p in PRIMES: f[f"X{p}"]=X%p; f[f"Y{p}"]=Y%p; f[f"XY{p}"]=(X*Y)%p
    for p in PQ: f[f"X{p}2"]=X%(p*p)
    phiX=BETA*X%P; f["phiYp"]=Y&1
    for p in (3,5,7,11,13,17,19,23): f[f"phi{p}"]=phiX%p; f[f"neg{p}"]=((-Y)%P)%p
    f["chi2"]=pow(X,(P-1)//2,P); f["chi3"]=pow(X,(P-1)//3,P)%3
    return f
def build(sub, include_bits=False):
    rows=[features(int(x),int(y),include_bits,int(b)) for x,y,b in zip(sub.Xi,sub.Yi,sub.bits)]
    return pd.DataFrame(rows).fillna(0).values.astype(np.float32)

def ceil(Xm,y,kind,reps=25,seed=0):
    rng=np.random.default_rng(seed)
    def one(yv):
        a,b,c,d=train_test_split(Xm,yv,test_size=0.3,random_state=1)
        if kind=="reg":
            m=REG(max_iter=150,early_stopping=False,random_state=1).fit(a,c)
            pr=m.predict(b); return 1-((d-pr)**2).sum()/((d-d.mean())**2+1e-9).sum()
        m=CLF(max_iter=150,early_stopping=False,random_state=1).fit(a,c)
        if kind=="top5":
            pp=m.predict_proba(b); cl=m.classes_; t=cl[np.argsort(pp,1)[:,-5:]]
            return np.mean([u in v for u,v in zip(d,t)])
        return m.score(b,d)
    real=one(y); nu=np.array([one(rng.permutation(y)) for _ in range(reps)])
    z=(real-nu.mean())/(nu.std()+1e-12); pval=(1+np.sum(nu>=real))/(reps+1)
    return real,nu.mean(),z,pval

def main():
    df=pd.read_csv("constructed_keys_1to160_100k.csv", dtype={"D":str})
    df["Xi"]=df.X.apply(lambda s:int(s,16)); df["Yi"]=df.Y.apply(lambda s:int(s,16))
    df["Dsign"]=[int(np.sign(int(v))) for v in df.D]
    print(f"loaded {len(df)}")

    # ---- Test A: HIGH-BAND POOL N in [140,160], public-only features (kills N-confound WITH power) ----
    pool=df[df.bits.between(140,160)].reset_index(drop=True)
    print(f"\n=== Test A: within-band pool N=140..160 ({len(pool)} keys), (X,Y)-only features ===")
    Xm=build(pool, include_bits=False)
    print(f"  feature matrix {Xm.shape}")
    targets=[("n top-5","top5",pool.n.values),
             ("n is prime","clf",pool.n.apply(lambda v:int(isprime(int(v)))).values),
             ("n even","clf",(pool.n.values%2==0).astype(int)),
             ("n mod3","clf",(pool.n.values%3)),
             ("sign(D)","clf",(pool.Dsign.values>0).astype(int)),
             ("D_terms","clf",pool.D_terms.values)]
    resA=[]
    for nm,k,y in targets:
        r,mu,z,p=ceil(Xm,y,k); resA.append((nm,z,p)); print(f"  {nm:12s}: real={r:.4f} null={mu:.4f} z={z:+.2f} emp_p={p:.3f}")
    # Holm across Test-A targets
    ps=sorted([p for _,_,p in resA]); K=len(ps)
    holm=min([ps[i]*(K-i) for i in range(K)]); print(f"  Holm-corrected min p across Test A = {min(1.0,holm):.3f}")

    # ---- Test B: FULL 100k map ceiling (max power), bits allowed as feature ----
    print(f"\n=== Test B: FULL 100k public->n ceiling (bits incl), 15-perm null ===")
    Xf=build(df, include_bits=True)
    for nm,k,y in [("n top-5","top5",df.n.values),("log2 n","reg",np.log2(df.n.values.astype(float)))]:
        r,mu,z,p=ceil(Xf,y,k,reps=15); print(f"  {nm:8s}: real={r:.4f} null={mu:.4f} z={z:+.2f} emp_p={p:.3f}")

    # ---- Test D: real-key selection, Westfall-Young max-stat FWER ----
    print(f"\n=== Test D: real-key n-selection, Westfall-Young max-|z| FWER (82 keys) ===")
    import random; random.seed(0)
    from fractions import Fraction
    pv=pd.read_csv("puzzles_verified.csv"); sv=pv[pv.private_key.notna()]
    realn=sv.n.values.astype(int); bitset=sv.bits.values
    def dec_n(d,b): A=1<<(b-1); return Fraction(d-A,A).limit_denominator(256).denominator
    stats_f={"prime":lambda v:np.mean([isprime(int(x)) for x in v]),
             "even":lambda v:np.mean(v%2==0),"n>=250":lambda v:np.mean(v>=250),
             "phi/n":lambda v:np.mean([float(totient(int(x)))/int(x) for x in v]),
             "n%6in45":lambda v:np.mean([int(x)%6 in (4,5) for x in v])}
    B=4000; nulls={k:[] for k in stats_f}
    for _ in range(B):
        draw=np.array([dec_n(random.randrange(1<<(int(b)-1),1<<int(b)),int(b)) for b in bitset])
        for k,f in stats_f.items(): nulls[k].append(f(draw))
    zmax_null=[]
    real_z={}
    for k,f in stats_f.items():
        nd=np.array(nulls[k]); mu,sd=nd.mean(),nd.std()+1e-12
        real_z[k]=abs(f(realn)-mu)/sd
    # build max-|z| null across the 5 stats using the SAME draws
    arr=np.array([[ (nulls[k][i]-np.mean(nulls[k]))/(np.std(nulls[k])+1e-12) for k in stats_f] for i in range(B)])
    zmax_null=np.abs(arr).max(1)
    obs_max=max(real_z.values())
    fwer_p=(1+np.sum(zmax_null>=obs_max))/(B+1)
    for k in stats_f: print(f"  {k:8s}: |z|={real_z[k]:.2f}")
    print(f"  observed max|z| = {obs_max:.2f} ; Westfall-Young FWER p = {fwer_p:.4f}")
    print("\nDONE")

if __name__=="__main__": main()
