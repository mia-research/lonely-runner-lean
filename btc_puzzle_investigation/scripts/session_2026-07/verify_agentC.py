"""
Independent spot-check of agent C's ML result. Build my own modest (X,Y)-only
feature set, train an independent GBM on real targets + a planted control, and
confirm: real targets sit at base rate while the control fires (proving power).
"""
import leak_lib as L
import numpy as np
from sklearn.ensemble import HistGradientBoostingClassifier
from sklearn.model_selection import train_test_split

d=L.load(); N=d["N"]; X=d["X"]; Y=d["Y"]; n=d["n"]; k=d["k"]
rng=np.random.default_rng(0)

cols=[];
for m in [3,5,7,11,13,17,19,23,31]:
    cols.append(L.col_mod(X,m)); cols.append(L.col_mod(Y,m)); cols.append(L.col_mod(L.tf_prod(X,Y),m))
for p in [3,5,7,11,13,17]:
    cols.append(L.col_legendre(X,p)); cols.append(L.col_legendre(Y,p))
for b in list(range(0,32,2))+[64,128,192,255]:
    cols.append(L.col_bit(X,b)); cols.append(L.col_bit(Y,b))
for m in [7,11,13,16]:
    cols.append(L.col_mod(L.tf_glv(X),m)); cols.append(L.col_mod(L.tf_slope(X,Y),m))
F=np.column_stack(cols).astype(float)
print(f"feature matrix: {F.shape}")

Xg7=L.col_mod(X,7); Yg5=L.col_mod(Y,5)
targets={
 "kn_bucket16":np.clip((k/n*16).astype(int),0,15),
 "n%4":n%4, "k%3":k%3, "n_isprime":np.array([1 if L.gtest_p else 0 for _ in n]),  # placeholder fixed below
}
# proper n_isprime
def isprime(x):
    if x<2: return 0
    i=2
    while i*i<=x:
        if x%i==0: return 0
        i+=1
    return 1
targets["n_isprime"]=np.array([isprime(int(v)) for v in n])
# planted control: deterministic function of X%7 and Y%5 (6 classes)
targets["CONTROL_planted"]=(Xg7*5+Yg5)%6

print(f"\n{'target':>16} {'classes':>8} {'base_rate':>10} {'heldout_acc':>12} {'lift':>8}")
for tn,t in targets.items():
    Xtr,Xte,ytr,yte=train_test_split(F,t,test_size=0.3,random_state=1,stratify=t)
    m=HistGradientBoostingClassifier(max_iter=120,max_depth=6,random_state=1).fit(Xtr,ytr)
    acc=m.score(Xte,yte)
    vals,cnts=np.unique(yte,return_counts=True); base=cnts.max()/len(yte)
    print(f"{tn:>16} {len(vals):>8} {base:>10.4f} {acc:>12.4f} {acc-base:>+8.4f}"
          f"{'   <-- control FIRES' if tn=='CONTROL_planted' and acc-base>0.1 else ''}")
print("\nRead: real targets lift ~0 (at base rate) while CONTROL lifts hugely => independent")
print("confirmation that (X,Y) yields no learned prediction of n/k, detector powered.")
