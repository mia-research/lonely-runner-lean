"""
Continuous-regression angle (fixes coarse-binning): predict CONTINUOUS k/n, n, k
from (X,Y)-only features with a fast HistGradientBoostingRegressor. Held-out R^2
vs shuffled-target null + positive control + best single-feature Spearman.
"""
import leak_lib as L
import numpy as np
from sklearn.ensemble import HistGradientBoostingRegressor
from sklearn.model_selection import train_test_split
from sklearn.metrics import r2_score

d=L.load(); X=d["X"]; Y=d["Y"]; n=d["n"]; k=d["k"]
cols=[]
for m in [3,5,7,11,13,17,19,23,29,31,37,41,43,47]:
    cols.append(L.col_mod(X,m)); cols.append(L.col_mod(Y,m)); cols.append(L.col_mod(L.tf_prod(X,Y),m))
for p in [3,5,7,11,13,17,19,23]:
    cols.append(L.col_legendre(X,p)); cols.append(L.col_legendre(Y,p))
for b in range(0,80,2): cols.append(L.col_bit(X,b)); cols.append(L.col_bit(Y,b))
for m in [7,11,13,16,31,64]: cols.append(L.col_mod(L.tf_glv(X),m)); cols.append(L.col_mod(L.tf_slope(X,Y),m))
F=np.column_stack(cols).astype(float)
print(f"feature matrix {F.shape}")

def r2run(y):
    Xtr,Xte,ytr,yte=train_test_split(F,y,test_size=0.3,random_state=1)
    m=HistGradientBoostingRegressor(max_iter=200,max_depth=6,random_state=1).fit(Xtr,ytr)
    return r2_score(yte,m.predict(Xte))

rng=np.random.default_rng(0)
print(f"\n{'target':>10} {'heldout_R2':>11} {'shuffled_null_R2':>17}")
for name,y in (("k/n",k/n),("n",n.astype(float)),("k",k.astype(float))):
    r2=r2run(y); r2n=r2run(rng.permutation(y))
    print(f"{name:>10} {r2:>11.4f} {r2n:>17.4f}")
# positive control: target genuinely built from 2 features
ctrl=(F[:,0]*7 + F[:,3] + 0.01*F[:,10]).astype(float)
print(f"{'CONTROL':>10} {r2run(ctrl):>11.4f} {r2run(rng.permutation(ctrl)):>17.4f}   <-- must be >>0")
# best single-feature Spearman vs k/n
def spear(a,b):
    ra=np.argsort(np.argsort(a)).astype(float); rb=np.argsort(np.argsort(b)).astype(float)
    ra-=ra.mean(); rb-=rb.mean(); dd=np.sqrt((ra@ra)*(rb@rb)); return (ra@rb)/dd if dd>0 else 0
s=k/n; best=max(range(F.shape[1]),key=lambda j:abs(spear(F[:,j],s)))
print(f"\nbest single-feature Spearman vs k/n = {spear(F[:,best],s):+.4f}")
print("Read: real R2 <=0 and matching shuffled null => no continuous (X,Y)->n/k signal.")
print("Control R2 >>0 confirms the regressor recovers a real feature-based target.")
