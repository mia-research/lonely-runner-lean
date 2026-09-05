"""
INVESTIGATE the two GECT-native flickers instead of dismissing them:
  F1  Spearman(XY mod n^2 / n^2 , k/n) = 0.245, p=0.027   (GECT's structural invariant)
  F2  gcd(Y,n)>1 low, p=0.036                              (recurring since v2)

Decisive tests:
  [n+-delta control] recompute each using n' = n-2..n+2 (numbers with no role in
     the key). A TRUE-n relationship stands out at delta=0 and dies at neighbors;
     a general-arithmetic artifact is flat across delta.
  [partial rho] for F1, correlation of (XY mod n^2/n^2, k/n) controlling for n and
     bit-length -- kills a confound where both track n.
  [out-of-sample] for F1, fit the monotone rank-map on a train split, score test.
"""
import csv, random
from math import gcd
import numpy as np

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        if int(r['n'])>=5:   # need n-2>=3 for the delta control to stay valid
            rows.append((int(r['bits']),int(r['X'],16),int(r['Y'],16),int(r['n']),int(r['k'])))
Bs=np.array([b for b,_,_,_,_ in rows]); X=[x for _,x,_,_,_ in rows]; Y=[y for _,_,y,_,_ in rows]
Nn=np.array([n for _,_,_,n,_ in rows]); Kk=np.array([k for _,_,_,_,k in rows]); M=len(rows)
rng=np.random.default_rng(3)

def spearman(a,b):
    ra=np.argsort(np.argsort(a)).astype(float); rb=np.argsort(np.argsort(b)).astype(float)
    ra-=ra.mean(); rb-=rb.mean()
    return (ra@rb)/(np.sqrt((ra@ra)*(rb@rb))+1e-30)
def perm_p(a,b,iters=5000):
    obs=abs(spearman(a,b)); c=1
    for _ in range(iters):
        if abs(spearman(a,rng.permutation(b)))>=obs: c+=1
    return obs,c/(iters+1)

s=Kk/Nn
print("F1  XY mod (n')^2 / (n')^2  vs  k/n  -- does the TRUE n matter?")
print(f"    {'delta':>6} | {'|rho|':>6} | perm-p")
for dd in (-2,-1,0,1,2):
    npr=Nn+dd
    r=np.array([((X[i]*Y[i])%(int(npr[i])**2))/(int(npr[i])**2) for i in range(M)])
    o,p=perm_p(r,s)
    print(f"    {dd:>+6} | {o:6.3f} | {p:.3f}{'   <-- true n' if dd==0 else ''}")

# partial correlation of F1 controlling for n and bits (rank-partial)
def resid_rank(v, controls):
    Vr=np.argsort(np.argsort(v)).astype(float)
    Cr=np.column_stack([np.argsort(np.argsort(c)).astype(float) for c in controls]+[np.ones(M)])
    beta,_,_,_=np.linalg.lstsq(Cr,Vr,rcond=None); return Vr-Cr@beta
r0=np.array([((X[i]*Y[i])%(int(Nn[i])**2))/(int(Nn[i])**2) for i in range(M)])
ra=resid_rank(r0,[Nn.astype(float),Bs.astype(float)]); rb=resid_rank(s,[Nn.astype(float),Bs.astype(float)])
print(f"    partial rho (control n & bits): {spearman(ra,rb):+.3f}  "
      f"(vs raw {spearman(r0,s):+.3f}) -> {'survives' if abs(spearman(ra,rb))>0.15 else 'shrinks -> confound with n'}")

# out-of-sample: does the sign/rank relation hold on held-out keys?
oos=[]
for _ in range(400):
    idx=rng.permutation(M); tr,te=idx[:55],idx[55:]
    sign=np.sign(spearman(r0[tr],s[tr]))
    oos.append(sign*spearman(r0[te],s[te]))   # aligned test-set correlation
oos=np.array(oos)
print(f"    out-of-sample aligned rho: mean={oos.mean():+.3f}  (>0 and clear of 0 = real)")

print("\nF2  gcd(Y, n')>1 count -- does the TRUE n matter?")
_r=random.Random(9)
def gcd_count(mods, coord):
    return sum(gcd(coord[i], int(mods[i]))>1 for i in range(M))
for dd in (-2,-1,0,1,2):
    npr=Nn+dd
    obs=gcd_count(npr,Y)
    # matched reference: random residue mod n'
    null=[sum(_r.randrange(int(npr[i]))* 0 == 0 and gcd(_r.randrange(int(npr[i])),int(npr[i]))>1 for i in range(M)) for _ in range(800)]
    null=np.array(null); p=(1+(null<=obs).sum())/(1+len(null))
    print(f"    delta={dd:>+2}: chosen gcd>1 = {obs}  ref-med={np.median(null):.0f}  p(low)={p:.3f}"
          f"{'   <-- true n' if dd==0 else ''}")
print("\nF2 sign-flips across delta => not a true-n effect (v2's read). Flat low across")
print("delta => a real property of Y vs nearby moduli, not the key's n.")
