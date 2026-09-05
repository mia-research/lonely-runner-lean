import numpy as np, pandas as pd
from sklearn.ensemble import HistGradientBoostingClassifier as C
from sklearn.model_selection import train_test_split
P=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
df=pd.read_csv("constructed_keys_1to160_100k.csv")
df["Xi"]=df.X.apply(lambda s:int(s,16)); df["Yi"]=df.Y.apply(lambda s:int(s,16))
print("D_terms distribution:", dict(df.D_terms.value_counts().sort_index()))
print("corr(bits, D_terms):", np.corrcoef(df.bits,df.D_terms)[0,1].round(4))
Q=[3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71]
s=df.sample(15000,random_state=0).reset_index(drop=True)
def kf(X,Y,b,use_bits):
    f={"Yp":Y&1,"pX":bin(X).count("1"),"pY":bin(Y).count("1")}
    if use_bits: f["bits"]=b
    for q in Q: f[f"X{q}"]=X%q; f[f"Y{q}"]=Y%q
    for m in range(2,48): f[f"Xs{m}"]=X%m; f[f"Ys{m}"]=Y%m
    return f
rng=np.random.default_rng(0)
def ceil(F,y,reps=6):
    def one(yv):
        a,b,c,d=train_test_split(F,yv,test_size=0.3,random_state=1)
        return C(max_iter=80,early_stopping=False,random_state=1).fit(a,c).score(b,d)
    r=one(y); nu=np.array([one(rng.permutation(y)) for _ in range(reps)])
    return r,nu.mean(),(r-nu.mean())/(nu.std()+1e-12)
y=s.D_terms.values
Fbits=np.array([[b] for b in s.bits]).astype(float)
Fxy =pd.DataFrame([kf(int(x),int(y_),int(b),False) for x,y_,b in zip(s.Xi,s.Yi,s.bits)]).values.astype(float)
Ffull=pd.DataFrame([kf(int(x),int(y_),int(b),True ) for x,y_,b in zip(s.Xi,s.Yi,s.bits)]).values.astype(float)
print("\nD_terms prediction (confound isolation):")
for nm,F in [("bits-only        ",Fbits),("(X,Y) NO bits    ",Fxy),("full (X,Y)+bits  ",Ffull)]:
    r,mu,z=ceil(F,y); print(f"  {nm}: acc={r:.4f} null={mu:.4f} adv={r-mu:+.4f} z={z:+.2f}")
# also: within a SINGLE bit-band (bits fixed) does (X,Y) still predict D_terms?
print("\nwithin fixed bit-bands (bits held constant, so no bits confound):")
for bb in [130,140,150,160]:
    sub=df[df.bits==bb]
    if len(sub)<400: print(f"  bits={bb}: only {len(sub)} keys, skip"); continue
    sub=sub.sample(min(4000,len(sub)),random_state=0).reset_index(drop=True)
    F=pd.DataFrame([kf(int(x),int(y_),int(b),False) for x,y_,b in zip(sub.Xi,sub.Yi,sub.bits)]).values.astype(float)
    r,mu,z=ceil(F,sub.D_terms.values,reps=5)
    print(f"  bits={bb} ({len(sub)} keys): acc={r:.4f} null={mu:.4f} adv={r-mu:+.4f} z={z:+.2f}")
print("\nDONE")
