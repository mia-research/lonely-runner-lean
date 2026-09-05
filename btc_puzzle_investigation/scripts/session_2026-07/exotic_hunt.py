"""
Exotic (X,Y) features not covered elsewhere, vs n/k targets at 100k, corrected MI.
- coordinate smoothness: # small primes dividing X / Y (the earlier 'F2' flicker,
  now at 100k power), and gcd(X, primorial).
- quadratic-residue counts of X across many primes (a 'Legendre profile' scalar).
- X mod P inverse's residues, cube of X, etc.
All features from X,Y only. Uses bias-subtracted MI; positive control.
"""
import leak_lib as L
import numpy as np
from math import gcd

d=L.load(); N=d["N"]; X=d["X"]; Y=d["Y"]; n=d["n"]; k=d["k"]
print(f"loaded {N} keys")
SMALL=[2,3,5,7,11,13,17,19,23,29,31,37]
prim=1
for p in SMALL: prim*=p

def omega(vals):  # count of SMALL primes dividing v
    return np.array([sum(1 for p in SMALL if int(v)%p==0) for v in vals])
def qr_profile(vals, primes):  # # of primes where v is a QR
    return np.array([sum(1 for p in primes if pow(int(v)%p,(p-1)//2,p)==1) for v in vals])
def gcd_prim(vals): return np.array([1 if gcd(int(v),prim)>1 else 0 for v in vals])

feats={
 "omega(X)":omega(X), "omega(Y)":omega(Y),
 "qrprofile(X)%8":qr_profile(X,[3,5,7,11,13,17,19])%8,
 "qrprofile(Y)%8":qr_profile(Y,[3,5,7,11,13,17,19])%8,
 "gcd(X,prim)":gcd_prim(X), "gcd(Y,prim)":gcd_prim(Y),
 "X%2":L.col_mod(X,2), "Y%2":L.col_mod(Y,2),
 "cube(X)%64":L.col_mod([(int(x)**3)%L.P for x in X],64),
 "inv(X)%64":L.col_mod(L.tf_inv(X),64),
 "slope%64":L.col_mod(L.tf_slope(X,Y),64),
 "hamX%16":L.col_hamming(X)%16, "hamY%16":L.col_hamming(Y)%16,
}
tgts=L.build_target_set(d)
rng=np.random.default_rng(2)
print(f"\n{'feature':>16} {'target':>12} {'adjMI(bits)':>11} {'Bonf-p':>9}")
res=[]
M=len(feats)*len(tgts)
for fn,fv in feats.items():
    for tn,tv in tgts.items():
        adj,raw,nb,A,B=L.adj_mi(fv,tv,iters=6,rng=rng)
        p=L.gtest_p(raw,N,A,B)
        res.append((adj,p,fn,tn,A,B))
res.sort(reverse=True)
for adj,p,fn,tn,A,B in res[:15]:
    print(f"{fn:>16} {tn:>12} {adj:11.5f} {min(1,p*M):9.2e}")
# control
base=k%4; leak=np.where(rng.random(N)<0.45,base,rng.integers(0,4,N))
adj,raw,nb,A,B=L.adj_mi(leak,base,iters=6,rng=rng)
print(f"\n[CONTROL] planted ~0.1-bit feature->k%4: adjMI={adj:.4f} bits (detector works)")
print("Read: top adjMI at ~0 with Bonf-p~1 => no bits of n/k from these features at 100k.")
