"""Can Barajas-Serra's Prime Filtering counting be run at n = 8?

BS Lemma 2 is a COUNTING argument over the multiplier group U(Z_N) -- pigeonhole, not measure.
Set, for a disparity d and modulus N,

    BAD(d) = { lambda in U(Z_N) : |lambda*d|_N < N/8 }        (lambda is the instant)

A good instant exists as soon as  sum_d |BAD(d)| < |U(Z_N)|  -- BS's own union bound.

Their engine is that the cage (eq. 2, nu is multiplier-invariant) makes whole LEVELS automatically
clear, so only the remaining level needs counting.  At modulus N = 8M a disparity is auto-clear
when M | d and 8M does not divide d -- its whole orbit is caged at distance >= M/N = 1/8.

So the lever is: choose M killing enough disparities that the rest cannot cover the group.
Each surviving unit-disparity costs about 1/4 of the group, so <= 3 survivors should certify.

MEASURED, not assumed: the exact ratio, minimised over M, on real arrangements.
This is counting over a finite group, as in BS's verified proof -- NOT a measure or density
argument over the reals.  Flagged for the owner's sec 6A ruling either way.
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from math import gcd
from itertools import combinations
import random
from collections import Counter
NR=8
def bad_count(d,N):
    """|BAD(d)| and |U(Z_N)| by direct enumeration over the multiplier group."""
    u=0; b=0
    for lam in range(1,N):
        if gcd(lam,N)!=1: continue
        u+=1
        r=(lam*d)%N
        if min(r,N-r)*NR < N: b+=1
    return b,u
def ratio(ds,M):
    N=NR*M
    tot=0; U=None
    for d in ds:
        b,u=bad_count(d%N,N); U=u
        tot+=b
    return tot/U
rng=random.Random(2222)
best=Counter(); vals=[]; cert=0; tot=0
MRANGE=range(1,61)
for _ in range(150):
    v=speeds(rng.sample(range(1,90),NR))
    for i in range(NR):
        ds=[abs(v[j]-v[i]) for j in range(NR) if j!=i]
        g=0
        for x in ds: g=gcd(g,x)
        ds=[x//g for x in ds]
        r=min((ratio(ds,M),M) for M in MRANGE)
        tot+=1; vals.append(r[0]); best[r[1]]+=1
        if r[0]<1: cert+=1
vals.sort()
print(f"  {tot} subjects, M searched over {MRANGE.start}..{MRANGE.stop-1}")
print(f"  BS union bound CERTIFIES (ratio < 1): {cert} of {tot}   ({cert/tot:.4f})")
print(f"  ratio  min {vals[0]:.4f}   median {vals[len(vals)//2]:.4f}   max {vals[-1]:.4f}")
print(f"  deciles: " + "  ".join(f"{vals[int(len(vals)*k/10)]:.3f}" for k in range(10)))
print(f"  best M (top 8): {best.most_common(8)}")
