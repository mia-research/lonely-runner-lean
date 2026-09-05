import random, numpy as np, pandas as pd
from fractions import Fraction
from sympy import isprime
from sklearn.ensemble import HistGradientBoostingClassifier as C, HistGradientBoostingRegressor as R
from sklearn.model_selection import train_test_split
P=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
BETA=0x7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE
Q=[3,5,7,11,13,17,19,23,29,31,37,41,43,47]
def fp(X,Y,p):
    f={f"{p}Yp":Y&1,f"{p}pX":bin(X).count("1")}
    for q in Q: f[f"{p}X{q}"]=X%q; f[f"{p}Y{q}"]=Y%q
    return f
def feats(X,Y,b):
    f={"bits":b}; f.update(fp(X,Y,""))
    for m in range(2,48): f[f"Xs{m}"]=X%m; f[f"Ys{m}"]=Y%m
    px=BETA*X%P; f.update(fp(px,Y,"phi")); f.update(fp(BETA*px%P,Y,"ph2")); f.update(fp(X,(-Y)%P,"neg"))
    f["c2"]=pow(X,(P-1)//2,P); f["c3"]=pow(X,(P-1)//3,P)%1000
    return f
def ev(Xin,y,kind,reps=6,seed=0):
    rng=np.random.default_rng(seed)
    def one(yv):
        a,b,c,d=train_test_split(Xin,yv,test_size=0.3,random_state=1)
        if kind=="reg":
            m=R(max_iter=60,early_stopping=False,random_state=1).fit(a,c); p=m.predict(b)
            return 1-((d-p)**2).sum()/((d-d.mean())**2).sum()
        m=C(max_iter=60,early_stopping=False,random_state=1).fit(a,c)
        if kind=="top5":
            pr=m.predict_proba(b); cl=m.classes_; t=cl[np.argsort(pr,1)[:,-5:]]
            return np.mean([u in v for u,v in zip(d,t)])
        return m.score(b,d)
    r=one(y); nu=np.array([one(rng.permutation(y)) for _ in range(reps)])
    return r,nu.mean(),(r-nu.mean())/(nu.std()+1e-12)
df=pd.read_csv("constructed_keys_1to160_100k.csv")
df["Xi"]=df.X.apply(lambda s:int(s,16)); df["Yi"]=df.Y.apply(lambda s:int(s,16))
for seed in (0,1):
    random.seed(seed); np.random.seed(seed)
    s=df.sample(15000,random_state=seed).reset_index(drop=True)
    F=pd.DataFrame([feats(int(x),int(y),int(b)) for x,y,b in zip(s.Xi,s.Yi,s.bits)]).fillna(0)
    base=[c for c in F.columns if not c.startswith(("phi","ph2","neg","c2","c3"))]
    Xa=F.values.astype(float); Xb=F[base].values.astype(float); Xbits=F[["bits"]].values.astype(float)
    yl=np.log2(s.n.values.astype(float))
    print(f"\n### seed {seed} (N=15000) ###")
    pl=((s.n.values%5)+(np.random.rand(len(s))<0.2)*np.random.randint(1,5,len(s)))%5
    r,mu,z=ev(np.column_stack([Xa,pl.reshape(-1,1)]),(s.n.values%5),"clf",seed=seed); print(f"  pos-ctrl n%5: acc={r:.3f} null={mu:.3f} z={z:+.0f}")
    for nm,X in [("bits-only",Xbits),("base(raw)",Xb),("curve   ",Xa)]:
        r,mu,z=ev(X,yl,"reg",seed=seed); print(f"  log2n {nm}: R2={r:+.4f} adv={r-mu:+.4f} z={z:+.2f}")
    r,mu,z=ev(Xa,s.n.apply(lambda v:int(isprime(int(v)))).values,"clf",seed=seed); print(f"  n-prime(curve): adv={r-mu:+.4f} z={z:+.2f}")
    r,mu,z=ev(Xa,s.n.values,"top5",seed=seed); print(f"  n-top5(curve):  adv={r-mu:+.4f} z={z:+.2f}")
print("\nDONE")
