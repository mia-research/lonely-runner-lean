import numpy as np, pandas as pd
from fractions import Fraction
df=pd.read_csv("constructed_keys_1to160_100k.csv", dtype={"D":str})
df["Yi"]=df.Y.apply(lambda s:int(s,16)); df["Dsign"]=[int(np.sign(int(v))) for v in df.D]
def cfpar(k,n):
    a=[];f=Fraction(int(k),int(n))
    for _ in range(24):
        w=f.__floor__();a.append(w);f=f-w
        if f==0:break
        f=1/f
    return len(a)%2
work=df[(df.n>=2)&(df.Dsign!=0)].copy()
work=work.assign(cfpar=[cfpar(int(k),int(nn)) for k,nn in zip(work.k,work.n)])
yp=(work.Yi.values&1).astype(float); ds=work.Dsign.values.astype(float); cp=work.cfpar.values
print(f"working keys: {len(work)}  (D!=0, n>=2)")

def boot_corr(mask,B=2000,seed=0):
    rng=np.random.default_rng(seed); idx=np.where(mask)[0]; y=yp[idx]; d=ds[idx]
    real=np.corrcoef(y,d)[0,1]
    bs=np.array([np.corrcoef(y[s],d[s])[0,1] for s in (rng.integers(0,len(idx),len(idx)) for _ in range(B))])
    return real, np.percentile(bs,2.5), np.percentile(bs,97.5), real/(bs.std()+1e-12)

print("\n=== corr(Y-parity, sign(D)) by convergent parity, bootstrap CI ===")
for par in (0,1):
    r,lo,hi,z=boot_corr(cp==par); print(f"  CF-parity={par} (n={ (cp==par).sum() }): corr={r:+.4f}  95%CI[{lo:+.4f},{hi:+.4f}]  z~{z:+.2f}")
# class difference
r1=np.corrcoef(yp[cp==1],ds[cp==1])[0,1]; r0=np.corrcoef(yp[cp==0],ds[cp==0])[0,1]
rng=np.random.default_rng(1)
# permutation test of class difference: shuffle cfpar labels
perm=[]
for _ in range(2000):
    pc=rng.permutation(cp)
    perm.append(np.corrcoef(yp[pc==1],ds[pc==1])[0,1]-np.corrcoef(yp[pc==0],ds[pc==0])[0,1])
perm=np.array(perm); diff=r1-r0
print(f"\n  class difference r1-r0 = {diff:+.4f} ; perm-null p = {2*min((perm<=diff).mean(),(perm>=diff).mean()):.3f}")

print("\n=== does PUBLIC Y-parity predict sign(D) within CF-parity=1? (acc vs 0.5) ===")
g=work[work.cpar==1] if 'cpar' in work else work[cp==1]
ypg=(g.Yi.values&1); dsg=(g.Dsign.values>0).astype(int)
# majority-rule per Y-parity bucket
acc=max(np.mean(dsg[ypg==0]==round(dsg[ypg==0].mean())), 0)  # placeholder
from sklearn.model_selection import cross_val_score
from sklearn.linear_model import LogisticRegression
X=ypg.reshape(-1,1).astype(float)
cv=cross_val_score(LogisticRegression(),X,dsg,cv=5).mean()
print(f"  CF-par=1: predict sign(D)>0 from Y-parity alone, 5-fold acc={cv:.4f} (base rate {max(dsg.mean(),1-dsg.mean()):.4f})")

print("\n=== broaden: corr(Y-parity, sign(D)) conditioned on n parity & n mod 4 ===")
for lab,mask in [("n even",(work.n.values%2==0)),("n odd",(work.n.values%2==1)),
                 ("n%4==1",(work.n.values%4==1)),("n%4==3",(work.n.values%4==3))]:
    if mask.sum()<200: continue
    r=np.corrcoef(yp[mask],ds[mask])[0,1]; print(f"  {lab:8s} (n={mask.sum()}): corr={r:+.4f}")
print("\nDONE")
