"""
Robustness follow-up to ml_interaction_hunt.py: repeat the strongest-looking
real targets (n%4, k%2, n_isprime, kn_bucket16 -- picked because their single
split showed the least-negative lift) across 5 independent train/test splits,
and dump top feature importances for n%4 and k%2 to rule out an averaged-away
signal concentrated in one fold.
"""
import time, warnings
import numpy as np
import leak_lib as L
warnings.filterwarnings("ignore")
from sklearn.ensemble import HistGradientBoostingClassifier
from sklearn.model_selection import train_test_split
from sklearn.metrics import accuracy_score, roc_auc_score
from sklearn.inspection import permutation_importance

d = L.load()
X_list, Y_list = d["X"], d["Y"]
N = d["N"]

cols = {}
for m in L.SMALL_MODS:
    cols[f"X%{m}"] = L.col_mod(X_list, m); cols[f"Y%{m}"] = L.col_mod(Y_list, m)
for p in L.SMALL_PRIMES:
    cols[f"legX_{p}"] = L.col_legendre(X_list, p); cols[f"legY_{p}"] = L.col_legendre(Y_list, p)
for b in list(range(0,24))+[32,40,48,64,96,128,160,192,224,255]:
    cols[f"Xbit{b}"]=L.col_bit(X_list,b); cols[f"Ybit{b}"]=L.col_bit(Y_list,b)
hwX=L.col_hamming(X_list); hwY=L.col_hamming(Y_list)
cols["hwX"]=hwX; cols["hwY"]=hwY; cols["hwX%8"]=hwX%8; cols["hwY%8"]=hwY%8
cols["hwXY_diff%16"]=(hwX-hwY)%16
glv=L.tf_glv(X_list); glv2=L.tf_glv2(X_list); slope=L.tf_slope(X_list,Y_list)
prod=L.tf_prod(X_list,Y_list); summ=L.tf_sum(X_list,Y_list); diff=L.tf_diff(X_list,Y_list)
derived={"glv":glv,"glv2":glv2,"slope":slope,"prod":prod,"sum":summ,"diff":diff}
for name,vals in derived.items():
    for m in [3,5,7,8,11,13,16,17,31,251,256]:
        cols[f"{name}%{m}"]=L.col_mod(vals,m)
    for b in [0,1,2,3,4,5,6,7,8,16]:
        cols[f"{name}_bit{b}"]=L.col_bit(vals,b)
small_res=["X%7","X%11","X%13","Y%7","Y%11","Y%13","X%8","Y%8","X%16","Y%16"]
for i in range(len(small_res)):
    for j in range(i+1,len(small_res)):
        a,b_=small_res[i],small_res[j]
        cols[f"{a}*{b_}"]=cols[a]*(cols[b_].max()+1)+cols[b_]
feat_names=sorted(cols.keys())
Fmat=np.column_stack([cols[c] for c in feat_names]).astype(np.float64)
print(f"features: {Fmat.shape}")

T=L.build_target_set(d)

def is_prime(x):
    if x<2: return 0
    for p in [2,3,5,7,11,13]:
        if x%p==0: return int(x==p)
    i=17
    while i*i<=x:
        if x%i==0: return 0
        i+=1
    return 1
T["n_isprime"]=np.array([is_prime(int(x)) for x in d["n"]])
T["k_isprime"]=np.array([is_prime(int(x)) for x in d["k"]])

def fit_eval(y, seed):
    y=np.asarray(y); ncl=int(y.max())+1
    strat = y if ncl<=30 else None
    Xtr,Xte,ytr,yte=train_test_split(Fmat,y,test_size=0.30,random_state=seed,stratify=strat)
    counts=np.bincount(yte,minlength=ncl); base=counts.max()/len(yte)
    m=HistGradientBoostingClassifier(max_iter=150,max_depth=6,learning_rate=0.08,l2_regularization=1.0,random_state=seed)
    m.fit(Xtr,ytr)
    pred=m.predict(Xte); acc=accuracy_score(yte,pred)
    try:
        proba=m.predict_proba(Xte)
        auc = roc_auc_score(yte,proba[:,1]) if ncl==2 else roc_auc_score(yte,proba,multi_class="ovr",average="macro",labels=np.arange(ncl))
    except Exception:
        auc=np.nan
    return acc, auc, base, m, (Xte, yte)

print("\n=== multi-seed robustness (5 seeds) on candidate targets ===")
for tname in ["n%4","k%2","n_isprime","kn_bucket16","n%2","k%4"]:
    accs=[]; aucs=[]; bases=[]
    for seed in range(5):
        acc,auc,base,_,_ = fit_eval(T[tname], seed)
        accs.append(acc); aucs.append(auc); bases.append(base)
    print(f"{tname:<14} acc={np.mean(accs):.4f}+-{np.std(accs):.4f}  auc={np.nanmean(aucs):.4f}+-{np.nanstd(aucs):.4f}  base_mean={np.mean(bases):.4f}")

print("\n=== permutation feature importance (top 10) for n%4 and k%2, seed=0 ===")
for tname in ["n%4","k%2"]:
    acc,auc,base,model,(Xte,yte) = fit_eval(T[tname], 0)
    r = permutation_importance(model, Xte, yte, n_repeats=5, random_state=0, scoring="accuracy", n_jobs=-1)
    order = np.argsort(r.importances_mean)[::-1][:10]
    print(f"\n{tname}: acc={acc:.4f} base={base:.4f}")
    for i in order:
        print(f"  {feat_names[i]:<20} importance_mean={r.importances_mean[i]:+.5f}  std={r.importances_std[i]:.5f}")
