"""
Stage-2 done correctly: does (X,Y) reduced by the KNOWN n add information about k
BEYOND what n alone gives? (Predicting k from features that include n picks up the
n<->k arithmetic -- k coprime to n -- which is NOT an (X,Y) leak. So we measure the
LIFT of [n, bits, (X,Y)-mod-n features] over a baseline of [n, bits] only.)
n and public bit-length are allowed inputs; k and d are never features.
"""
import leak_lib as L
import numpy as np
from math import gcd
from sklearn.ensemble import HistGradientBoostingClassifier, HistGradientBoostingRegressor
from sklearn.model_selection import train_test_split
from sklearn.metrics import r2_score

d=L.load(); N=d["N"]; X=d["X"]; Y=d["Y"]; n=d["n"]; k=d["k"]; bits=d["bits"]
ni=[int(v) for v in n]
def perrow(fn): return np.array([fn(int(X[i]),int(Y[i]),ni[i]) for i in range(N)],dtype=float)
def invmod(a,m):
    try: return pow(a%m,-1,m)
    except ValueError: return 0
# (X,Y) reduced by KNOWN n (legitimate stage-2 features)
Xn   = perrow(lambda x,y,nn: x%nn)
Yn   = perrow(lambda x,y,nn: y%nn)
XYn  = perrow(lambda x,y,nn: (x*y)%nn)
XYn2 = perrow(lambda x,y,nn: (x*y)%(nn*nn))
XpYn = perrow(lambda x,y,nn: (x+y)%nn)
Xinvy= perrow(lambda x,y,nn: (x*invmod(y,nn))%nn)
# plain small-prime residues too
extra=[L.col_mod(X,p) for p in (3,5,7,11,13)]+[L.col_mod(Y,p) for p in (3,5,7,11,13)]

base_cols=[n.astype(float), bits.astype(float)]
full_cols=base_cols+[Xn,Yn,XYn,XYn2,XpYn,Xinvy]+extra
Fbase=np.column_stack(base_cols); Ffull=np.column_stack(full_cols)
print(f"base features {Fbase.shape}, full features {Ffull.shape}")

def clf_acc(F,y):
    Xtr,Xte,ytr,yte=train_test_split(F,y,test_size=0.3,random_state=1)
    m=HistGradientBoostingClassifier(max_iter=120,max_depth=6,random_state=1,early_stopping=False).fit(Xtr,ytr)
    return m.score(Xte,yte)
def reg_r2(F,y):
    Xtr,Xte,ytr,yte=train_test_split(F,y,test_size=0.3,random_state=1)
    m=HistGradientBoostingRegressor(max_iter=150,max_depth=6,random_state=1).fit(Xtr,ytr)
    return r2_score(yte,m.predict(Xte))

print(f"\n{'target':>8} {'base(n,bits)':>12} {'full(+XYmodn)':>13} {'LIFT':>8}  (lift>0 = (X,Y) adds info given n)")
for name,y in (("k%6",k%6),("k%8",k%8),("k%12",k%12)):
    a=clf_acc(Fbase,y); b=clf_acc(Ffull,y); print(f"{name:>8} {a:>12.4f} {b:>13.4f} {b-a:>+8.4f}")
# k/n regression
a=reg_r2(Fbase,k/n); b=reg_r2(Ffull,k/n); print(f"{'k/n R2':>8} {a:>12.4f} {b:>13.4f} {b-a:>+8.4f}")

# positive control: add a feature that genuinely encodes k -> full must jump vs base
ctrlF=np.column_stack(base_cols+[(k%6).astype(float)])
ac=clf_acc(Fbase,k%6); bc=clf_acc(ctrlF,k%6)
print(f"\n[CONTROL] k%6 with a planted k-feature: base={ac:.4f} full+plant={bc:.4f} lift={bc-ac:+.4f}  <-- must be large")
print("\nRead: LIFT ~0 => (X,Y)-mod-n adds nothing about k beyond the known-n arithmetic.")
print("A positive LIFT beating the control's demonstrated power = a real stage-2 leak.")
