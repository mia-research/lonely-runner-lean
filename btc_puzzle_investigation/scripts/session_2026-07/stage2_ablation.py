"""
Ablation for the stage-2 hunt: is the pooled k-regression signal (R2~0.37)
coming from the ALLOWED inputs n & bits alone (which bound k in [0,n]), or does
(X,Y) reduced mod n add anything on top?

Fit HistGBM regressor on k with THREE feature sets, identical 70/30 split:
  A) [n, bits] only            -- the allowed known/public inputs
  B) (X,Y)-mod-n features only -- the (X,Y) reductions, NO n, NO bits
  C) everything                -- A + B + small-prime residues (full model)

If C ~ A and B ~ 0, then (X,Y) mod n contributes no extra k-information beyond
knowing n: the pooled lift is entirely the range-bounding effect of the allowed
inputs, NOT a leak from the public key coordinates.
"""
import time, math
import numpy as np
import leak_lib as L
from sklearn.ensemble import HistGradientBoostingRegressor, HistGradientBoostingClassifier
from sklearn.model_selection import train_test_split
from sklearn.metrics import mean_absolute_error, r2_score, accuracy_score

def log(*a): print(*a, flush=True)
SEED=20260706; t0=time.time()
d=L.load(); X_list,Y_list=d["X"],d["Y"]
n_arr=d["n"].astype(np.int64); k_arr=d["k"].astype(np.int64); bits_arr=d["bits"].astype(np.int64); N=d["N"]
log(f"N={N} ({time.time()-t0:.1f}s)")

M=N
Xmodn=np.empty(M,np.int64); Ymodn=np.empty(M,np.int64); XYmodn2=np.empty(M,np.int64)
XYmodn2n=np.empty(M,np.float64); XYmodn=np.empty(M,np.int64); XpY=np.empty(M,np.int64)
Xinvy=np.empty(M,np.int64); haveinv=np.empty(M,np.int64); Xmodn2=np.empty(M,np.int64)
for i in range(M):
    Xi=X_list[i]; Yi=Y_list[i]; ni=int(n_arr[i]); n2=ni*ni
    xr=Xi%ni; yr=Yi%ni; Xmodn[i]=xr; Ymodn[i]=yr
    xy2=(Xi*Yi)%n2; XYmodn2[i]=xy2; XYmodn2n[i]=xy2/n2
    XYmodn[i]=(Xi*Yi)%ni; XpY[i]=(Xi+Yi)%ni; Xmodn2[i]=Xi%n2
    if ni>1 and math.gcd(yr,ni)==1: Xinvy[i]=(Xi*pow(yr,-1,ni))%ni; haveinv[i]=1
    else: Xinvy[i]=-1; haveinv[i]=0

xy_feats=[Xmodn,Ymodn,XYmodn2,XYmodn2n,XYmodn,XpY,Xmodn2,Xinvy,haveinv]
for p in L.SMALL_PRIMES:
    xy_feats.append(np.fromiter((Xi%p for Xi in X_list),np.int64,M))
    xy_feats.append(np.fromiter((Yi%p for Yi in Y_list),np.int64,M))

A_feats=np.column_stack([n_arr,bits_arr]).astype(np.float32)                 # allowed inputs
B_feats=np.column_stack(xy_feats).astype(np.float32)                          # (X,Y) mod n etc, no n/bits
C_feats=np.column_stack([n_arr,bits_arr]+xy_feats).astype(np.float32)         # full
log(f"features built ({time.time()-t0:.1f}s)  A{A_feats.shape} B{B_feats.shape} C{C_feats.shape}")

KW=dict(max_iter=120,max_depth=8,learning_rate=0.15,random_state=SEED,early_stopping=True)

def reg(Xm,y,name):
    Xtr,Xte,ytr,yte=train_test_split(Xm,y,test_size=0.30,random_state=SEED)
    r=HistGradientBoostingRegressor(**KW).fit(Xtr,ytr); pred=r.predict(Xte)
    mae=mean_absolute_error(yte,pred); base=mean_absolute_error(yte,np.full_like(yte,np.median(ytr)))
    log(f"  k-reg [{name:26s}] MAE={mae:.4g} base_MAE={base:.4g} MAE-lift={base-mae:+.4g} R2={r2_score(yte,pred):+.5f}")
    return base-mae, r2_score(yte,pred)

log("\n=== k-regression ablation (does (X,Y) mod n add over n & bits?) ===")
la,ra=reg(A_feats,k_arr.astype(float),"A: n,bits only (allowed)")
lb,rb=reg(B_feats,k_arr.astype(float),"B: (X,Y) mod n only")
lc,rc=reg(C_feats,k_arr.astype(float),"C: full (A+B)")
log(f"\n  incremental value of (X,Y) mod n over n&bits: dMAE-lift = {lc-la:+.4g}, dR2 = {rc-ra:+.5f}")
log(f"  standalone (X,Y)-mod-n R2 (no n/bits) = {rb:+.5f}")

# Same ablation for k mod 7 classification (a residue target, no range-bounding confound)
def clf(Xm,y,name):
    Xtr,Xte,ytr,yte=train_test_split(Xm,y,test_size=0.30,random_state=SEED)
    c=HistGradientBoostingClassifier(**KW).fit(Xtr,ytr); acc=accuracy_score(yte,c.predict(Xte))
    base=np.bincount(yte.astype(np.int64)).max()/len(yte)
    log(f"  k%7  [{name:26s}] acc={acc:.4f} base={base:.4f} lift={acc-base:+.4f}")
    return acc-base
log("\n=== k mod 7 ablation (residue target, no range-bound confound) ===")
clf(A_feats,(k_arr%7),"A: n,bits only")
clf(B_feats,(k_arr%7),"B: (X,Y) mod n only")
clf(C_feats,(k_arr%7),"C: full")
log(f"\nTotal runtime: {time.time()-t0:.1f}s")
