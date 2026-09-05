import numpy as np, pandas as pd, random
from sympy import isprime, factorint, totient
pv=pd.read_csv("puzzles_verified.csv")
sv=pv[pv.private_key.notna()].copy(); sv["d"]=[int(str(v),16) for v in sv.private_key]
realn=sv.n.values.astype(int); N=len(realn)
print(f"real solved keys: {N} (bits {sv.bits.min()}..{sv.bits.max()})")

# matched null: for each real key's bits, draw many uniform d, decompose -> null n pool
from fractions import Fraction
def dec_n(d,bits):
    A=1<<(bits-1); return Fraction(d-A,A).limit_denominator(256).denominator
rng=np.random.default_rng(0); random.seed(0)
null_pool=[]
for _ in range(3000):
    draw=[]
    for b in sv.bits:
        b=int(b); A=1<<(b-1); draw.append(dec_n(random.randrange(A,1<<b),b))
    null_pool.append(draw)
null_pool=np.array(null_pool)   # (3000, N)

def stat(nv):
    nv=np.asarray(nv)
    return {
      "P(n prime)":       np.mean([isprime(int(x)) for x in nv]),
      "P(n even)":        np.mean(nv%2==0),
      "P(n=2^r)":         np.mean([ (int(x)&(int(x)-1))==0 for x in nv]),
      "P(omega(n)<=1)":   np.mean([len(factorint(int(x)))<=1 for x in nv]),
      "mean phi(n)/n":    np.mean([float(totient(int(x)))/int(x) for x in nv]),
      "P(n>=250)":        np.mean(nv>=250),
    }
real_s=stat(realn); null_s={k:np.array([stat(row)[k] for row in null_pool]) for k in real_s}
print("\n  statistic         real     null-mean   z       2-sided p (empirical)")
ps=[]
for k in real_s:
    nd=null_s[k]; mu,sd=nd.mean(),nd.std()+1e-12; z=(real_s[k]-mu)/sd
    p=2*min((nd<=real_s[k]).mean(),(nd>=real_s[k]).mean())
    ps.append(p); print(f"  {k:16s} {real_s[k]:7.3f}   {mu:7.3f}   {z:+5.2f}   {p:.3f}")
# Bonferroni / min-p corrected
import numpy as np
print(f"\n  min p = {min(ps):.3f} ; Bonferroni x{len(ps)} = {min(ps)*len(ps):.3f}")
print("  => verdict: selection lean is real only if min-p survives multiple-testing correction.")
print("\nDONE")
