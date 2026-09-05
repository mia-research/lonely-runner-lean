"""
Fixes assumption #1 (coarse binning). Target n and k at FULL resolution:
- GBM top-1 and top-5 held-out accuracy for the exact n (250-way) and exact k,
  vs base rate. A leak would put the true n in the top-5 more than chance.
- continuous: best single-feature Spearman vs k/n (full resolution, no binning).
Features from (X,Y) only. Positive control included.
"""
import leak_lib as L
import numpy as np
from sklearn.ensemble import HistGradientBoostingClassifier
from sklearn.model_selection import train_test_split

d=L.load(); N=d["N"]; X=d["X"]; Y=d["Y"]; n=d["n"]; k=d["k"]
cols=[]
for m in [3,5,7,11,13,17,19,23,29,31,37,41]:
    cols.append(L.col_mod(X,m)); cols.append(L.col_mod(Y,m)); cols.append(L.col_mod(L.tf_prod(X,Y),m))
for p in [3,5,7,11,13,17,19]:
    cols.append(L.col_legendre(X,p)); cols.append(L.col_legendre(Y,p))
for b in range(0,64,2): cols.append(L.col_bit(X,b)); cols.append(L.col_bit(Y,b))
for m in [7,11,13,16,31]: cols.append(L.col_mod(L.tf_glv(X),m)); cols.append(L.col_mod(L.tf_slope(X,Y),m))
F=np.column_stack(cols).astype(float)
print(f"feature matrix {F.shape}")

def topk_acc(target, label, kk=5, control=None):
    y=target
    Xtr,Xte,ytr,yte=train_test_split(F if control is None else np.column_stack([F,control]),
                                     y,test_size=0.3,random_state=1)
    m=HistGradientBoostingClassifier(max_iter=100,max_depth=6,random_state=1,early_stopping=False).fit(Xtr,ytr)
    classes=m.classes_
    proba=m.predict_proba(Xte)
    top1=(classes[proba.argmax(1)]==yte).mean()
    topk=np.mean([yte[i] in classes[np.argsort(proba[i])[-kk:]] for i in range(len(yte))])
    # base rates
    vals,cnts=np.unique(ytr,return_counts=True); order=np.argsort(cnts)[::-1]
    base1=cnts.max()/cnts.sum(); basek=cnts[order[:kk]].sum()/cnts.sum()
    print(f"  {label:22s} classes={len(vals):3d}  top1={top1:.4f} (base {base1:.4f})  "
          f"top5={topk:.4f} (base {basek:.4f})  lift5={topk-basek:+.4f}")

print("\nFULL-RESOLUTION classification (top-5 held-out):")
topk_acc(n, "n (full ~250-way)")
topk_acc(k, "k (full)")
# positive control: a feature that IS a function of n -> top-5 should jump
ctrl=(n%37).reshape(-1,1).astype(float)
topk_acc(n, "n WITH planted n%37", control=ctrl)

# continuous: best Spearman vs k/n (full resolution)
def spear(a,b):
    ra=np.argsort(np.argsort(a)).astype(float); rb=np.argsort(np.argsort(b)).astype(float)
    ra-=ra.mean(); rb-=rb.mean(); dd=np.sqrt((ra@ra)*(rb@rb)); return (ra@rb)/dd if dd>0 else 0
s=k/n
best=max(range(F.shape[1]), key=lambda j:abs(spear(F[:,j],s)))
print(f"\ncontinuous k/n: best single-feature Spearman = {spear(F[:,best],s):+.4f} (col {best})")
print("Read: top5 lift ~0 and Spearman ~0 => (X,Y) puts the exact n/k no better than")
print("chance and no monotone k/n trend, at full resolution. Control lift confirms power.")
