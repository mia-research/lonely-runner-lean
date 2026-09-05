"""
Is the marginal XY <- k%2 signal a real k-hint, or the n-parity arithmetic in
disguise? gcd(k,n)=1 forces: n even => k odd. So k%2 carries n%2, and any
XY <-> n%2 structure would surface as a fake XY <-> k%2.

Decisive partition: restrict to keys with ODD n, where k parity is FREE (not
forced by n). If the XY<->k%2 association dies on the odd-n subset, it was the
n-parity link, not a public->k leak.
"""
import csv
import numpy as np

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        rows.append((int(r['X'],16),int(r['Y'],16),int(r['n']),int(r['k'])))
Xs=[x for x,_,_,_ in rows]; Ys=[y for _,y,_,_ in rows]
n=np.array([nn for _,_,nn,_ in rows]); k=np.array([kk for _,_,_,kk in rows]); M=len(rows)

# [0] verify the arithmetic confound in the data
forced=[(k[i]%2) for i in range(M) if n[i]%2==0]
print(f"n even -> k odd?  among {len(forced)} even-n keys, k-odd fraction = "
      f"{np.mean(forced):.3f}  (1.000 confirms gcd(k,n)=1 forcing)")
print(f"n parity: {(n%2==0).sum()} even, {(n%2==1).sum()} odd  |  "
      f"k parity: {(k%2==0).sum()} even, {(k%2==1).sum()} odd")

_PR=(2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61)
def buildXY(idx):
    F={}
    for m in _PR:
        F[f"XY%{m}"]=np.array([(Xs[i]*Ys[i])%m for i in idx])
        F[f"X+Y%{m}"]=np.array([(Xs[i]+Ys[i])%m for i in idx])
    for p in (3,5,7,11,13,17,19,23):
        F[f"XYleg{p}"]=np.array([pow((Xs[i]*Ys[i])%p,(p-1)//2,p) for i in idx])
    return F
def mi(f,t):
    A=int(f.max())+1;B=int(t.max())+1;j=np.zeros((A,B))
    for a,b in zip(f,t): j[a,b]+=1
    j/=j.sum();pa=j.sum(1,keepdims=True);pb=j.sum(0,keepdims=True)
    with np.errstate(divide='ignore',invalid='ignore'):
        term=j*np.log2((j+1e-30)/(pa*pb+1e-30))
    return float(term[j>0].sum())
def channel_p(F,t,rng,iters=5000):
    def bestmi(tt): return max(mi(c,tt) for c in F.values())
    obs=bestmi(t);c=1
    for _ in range(iters):
        if bestmi(rng.permutation(t))>=obs: c+=1
    return obs,c/(iters+1)

rng=np.random.default_rng(11)
allidx=list(range(M)); oddidx=[i for i in range(M) if n[i]%2==1]
print(f"\nXY-channel best-MI vs k%2  (channel-corrected perm-p):")
o,p=channel_p(buildXY(allidx),(k%2),rng);           print(f"  ALL {M} keys      : MI={o:.4f}  p={p:.4f}")
o,p=channel_p(buildXY(oddidx),(k[oddidx]%2),rng);   print(f"  ODD-n {len(oddidx)} keys   : MI={o:.4f}  p={p:.4f}   (k parity free here)")
print(f"\nXY-channel best-MI vs n%2  (the suspected real target):")
o,p=channel_p(buildXY(allidx),(n%2),rng);           print(f"  ALL {M} keys      : MI={o:.4f}  p={p:.4f}")

print("\nIf ALL-keys k%2 fires but ODD-n k%2 does NOT, the 'signal' was the")
print("n-even=>k-odd arithmetic, i.e. no public->k leak beyond the n-parity link.")
