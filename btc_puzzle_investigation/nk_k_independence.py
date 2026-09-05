import numpy as np, pandas as pd, random
from math import gcd
from sympy import isprime
random.seed(0)
pv=pd.read_csv("puzzles_verified.csv"); sv=pv[pv.private_key.notna()].copy()
sv=sv[sv.n>=3]  # need a nontrivial coprime set
n=sv.n.values.astype(int); k=sv.k.values.astype(int); N=len(sv)
print(f"real keys with n>=3: {N}")
print("Testing: does k carry structure INDEPENDENT of n? (null = k uniform over coprimes<n, n FIXED)")

def coprimes(nn): return [x for x in range(nn) if gcd(x,nn)==1]
# real statistics
def stats(kv,nv):
    pos=np.array([ (kk/nn) for kk,nn in zip(kv,nv)])            # k/n position
    rank=np.array([ sorted(coprimes(nn)).index(kk)/max(1,len(coprimes(nn))-1) for kk,nn in zip(kv,nv)])
    return {
      "k prime rate":   np.mean([isprime(int(x)) for x in kv if x>1]),
      "k odd rate":     np.mean(kv%2==1),
      "k mod3==0":      np.mean(kv%3==0),
      "mean k/n":       pos.mean(),
      "mean rank(k)":   rank.mean(),      # position within coprime set, 0..1
      "k<n/2 rate":     np.mean(kv< nv/2),
    }
real=stats(k,n)
# n-conditioned null: resample k' uniform over coprimes(n) for each key
NULL=3000
null_rows=[]
for _ in range(NULL):
    kp=np.array([random.choice(coprimes(int(nn))) for nn in n])
    null_rows.append(stats(kp,n))
print("\n  statistic        real     null-mean   null-sd    z       ~p(2-sided)")
for key in real:
    nd=np.array([r[key] for r in null_rows]); mu,sd=nd.mean(),nd.std()+1e-12
    z=(real[key]-mu)/sd; p=2*min((nd<=real[key]).mean(),(nd>=real[key]).mean())
    print(f"  {key:14s} {real[key]:7.3f}   {mu:7.3f}   {sd:7.3f}   {z:+5.2f}   {p:.3f}")
print("\n  If all ~z<2 / p>0.05 => k has NO independent structure; the n<->k loop is already")
print("  priced into the 12.39-bit joint entropy (converges in one pass, does NOT compound).")
print("  If any survives => independent k-info exists => the propagation loop has real teeth.")
print("\nDONE")
