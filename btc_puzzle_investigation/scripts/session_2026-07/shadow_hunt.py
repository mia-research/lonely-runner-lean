"""
SHADOW / EXCLUSION hunt: not "does feature predict target" but "does any
(feature-value, target-value) combination NEVER occur" -> a forbidden combo lets
us EXCLUDE candidate k/n (search reduction even without prediction). At N=100k a
16x16 table expects ~390 per cell, so an empty cell is a real exclusion, not noise.
Also single-feature CRT pairs (X mod a, X mod b) for higher-order exclusions.
Features from X,Y only. Positive control included.
"""
import leak_lib as L
import numpy as np

d=L.load(); N=d["N"]; X=d["X"]; Y=d["Y"]; n=d["n"]; k=d["k"]
print(f"loaded {N} keys")

# feature and target moduli (moderate, so cells are well-populated under independence)
fmods=[7,8,9,11,13,16,17,19,23,25,32,49,64]
tmods=[7,8,9,11,13,16]
rng=np.random.default_rng(0)

def empty_report(fvals_name, fvals, tgt_name, tgt):
    A=int(fvals.max())+1; B=int(tgt.max())+1
    tab=np.zeros((A,B)); np.add.at(tab,(fvals,tgt),1)
    exp=N/(A*B)
    empties=int((tab==0).sum())
    # under independence, with expected ~exp per cell, P(cell empty)~exp(-exp); expected empties:
    exp_empty=A*B*np.exp(-exp)
    return empties, exp_empty, exp, A, B

print("\n=== single-feature exclusion: empty cells in feature x target tables ===")
print(f"{'feature':>10} {'target':>8} {'cells':>7} {'empty':>6} {'exp_empty':>10} {'min_expected/cell':>17}")
hits=[]
Xf={f"X%{m}":L.col_mod(X,m) for m in fmods}
Yf={f"Y%{m}":L.col_mod(Y,m) for m in fmods}
XYf={f"XY%{m}":L.col_mod(L.tf_prod(X,Y),m) for m in fmods}
allf={**Xf,**Yf,**XYf}
tgts={**{f"k%{m}":k%m for m in tmods}, **{f"n%{m}":n%m for m in tmods}}
for fn,fv in allf.items():
    for tn,tv in tgts.items():
        em,exem,exp,A,B=empty_report(fn,fv,tn,tv)
        if em>0 and exp>5:   # empty cells where independence predicts many -> real exclusion candidate
            hits.append((exp,em,fn,tn,A,B))
if hits:
    hits.sort()  # smallest expected-per-cell first (weakest); show the strongest (large exp, empty)
    for exp,em,fn,tn,A,B in sorted(hits,key=lambda h:-h[0])[:20]:
        print(f"{fn:>10} {tn:>8} {A*B:>7} {em:>6} {'~0':>10} {exp:>17.1f}")
    print(f"  -> {len(hits)} (feature,target) tables have an empty cell where >5 expected.")
else:
    print("  no empty cells where independence expects >5 per cell.")

# CRT pairs: (X mod a)*(X mod b) joint vs k -> higher-order forbidden combos
print("\n=== CRT-pair exclusion: (X%a, X%b) joint -> k%m empty cells ===")
pairhits=0
for a in [8,9,16]:
    for b in [7,11,13,17]:
        joint=L.col_mod(X,a)*b + L.col_mod(X,b)   # alphabet a*b
        for m in [8,11,13]:
            tv=k%m; A=a*b; B=m
            tab=np.zeros((A,B)); np.add.at(tab,(joint,tv),1)
            exp=N/(A*B)
            if exp>5 and (tab==0).sum()>0: pairhits+=1
print(f"  CRT-pair tables with an empty cell (expected>5): {pairhits}")

# POSITIVE CONTROL: plant a forbidden combo (k%8 never 0 when X%8==3) and confirm detection
Xm8=L.col_mod(X,8).copy(); k8=(k%8).copy()
mask=(Xm8==3)&(k8==0); k8p=k8.copy()
# reassign those to a different k residue -> creates a forbidden (X%8=3,k%8=0) cell
k8p[mask]=1
tab=np.zeros((8,8)); np.add.at(tab,(Xm8,k8p),1)
print(f"\n[CONTROL] planted forbidden (X%8=3,k%8=0): that cell now has {int(tab[3,0])} (was populated); "
      f"detector flags empty cells -> control {'FIRES' if tab[3,0]==0 else 'check'}")
print("\nRead: any real empty cell where independence expects hundreds = a forbidden")
print("combination = exclude those k/n. None = no exclusion shadow at this resolution/N.")
