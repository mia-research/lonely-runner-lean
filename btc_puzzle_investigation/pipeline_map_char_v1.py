#!/usr/bin/env python3
"""
Edge 2: characterize the deterministic CURVE-CALCULATION / production pipeline
  integer d  ->  decomposition (n,k,D)  ->  point (X,Y)
at FULL 100k power (not the 82-key selection question). Map which information
channels the pipeline leaves open between the POINT and the DECOMPOSITION/integer.
This is a property of the deterministic MAP; synthetic d is exactly right here.

Mutual information (bits) via exact joint counts; compared to a shuffle null (the
finite-sample MI floor). A channel is 'open' iff MI >> null. Known anchor:
(X*Y) mod 2^k tracks D mod 2^k (KNOWN_FACTS 9). We confirm it at power and scan for
any channel reaching (n,k) -- which would matter for search -- vs confined to D.
"""
import csv, math, random
from collections import Counter

def load(nmax=100023):
    d=[];X=[];Y=[];n=[];k=[];D=[]
    with open('constructed_keys_1to160_100k_exact.csv') as f:
        for row in csv.DictReader(f):
            d.append(int(row['d'])); X.append(int(row['X'],16)); Y.append(int(row['Y'],16))
            n.append(int(row['n'])); k.append(int(row['k'])); D.append(int(row['D']))
            if len(d)>=nmax: break
    return d,X,Y,n,k,D
d,X,Y,n,k,D=load()
N=len(d); print(f"loaded {N} pipeline triples (d,(n,k,D),(X,Y))")

def MI(A,B):
    ca=Counter(A); cb=Counter(B); cab=Counter(zip(A,B)); tot=len(A)
    mi=0.0
    for (x,y),c in cab.items():
        pxy=c/tot; px=ca[x]/tot; py=cb[y]/tot
        mi+=pxy*math.log2(pxy/(px*py))
    return mi
def shuffle_null(A,B,reps=5):
    B2=B[:]; vals=[]
    for _ in range(reps):
        random.shuffle(B2); vals.append(MI(A,B2))
    return sum(vals)/len(vals)

def feat_mod(vals,b): return [v & ((1<<b)-1) for v in vals]     # low b bits
random.seed(7)
B=6
point_feats={
    'X mod2^6': feat_mod(X,B), 'Y mod2^6': feat_mod(Y,B),
    'X*Y mod2^6': feat_mod([x*y for x,y in zip(X,Y)],B),
    'X+Y mod2^6': feat_mod([x+y for x,y in zip(X,Y)],B),
}
decomp_feats={
    'D mod2^6': feat_mod(D,B), 'd mod2^6': feat_mod(d,B),
    'k mod2^6': feat_mod(k,B), 'n mod2^6': feat_mod(n,B),
}
print(f"\nMI (bits) between point features and decomposition/integer features, N={N}")
print(f"{'':14}"+"".join(f"{c:>13}" for c in decomp_feats))
null_ref=None
for pf,pv in point_feats.items():
    row=f"{pf:14}"
    for df,dv in decomp_feats.items():
        mi=MI(pv,dv)
        row+=f"{mi:>13.4f}"
    print(row)
# null floor (same alphabet sizes ~ 64x64)
nl=shuffle_null(point_feats['X*Y mod2^6'], decomp_feats['D mod2^6'])
print(f"\nshuffle-null MI floor (64x64, N={N}) ~ {nl:.4f} bits  => channel 'open' iff MI >> this")
# the known anchor, quantified + scaled
print(f"\nANCHOR (X*Y mod2^6 vs D mod2^6): MI={MI(point_feats['X*Y mod2^6'],decomp_feats['D mod2^6']):.4f} bits")
# does the (X*Y) channel reach k or n (search-relevant) or only D (inert)?
for tgt in ['D mod2^6','k mod2^6','n mod2^6','d mod2^6']:
    print(f"  (X*Y) -> {tgt}: MI={MI(point_feats['X*Y mod2^6'],decomp_feats[tgt]):.4f}  (null {nl:.4f})")
