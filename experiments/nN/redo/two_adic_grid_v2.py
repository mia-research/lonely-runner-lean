# For integer arrangements where the 2-adic grid (t = k/2^max(v+1,3), k odd) has no lonely instant:
# the first lonely instant t* in (0,1] (exact, Fractions) is an opening t=(8K+1)/(8 r_e). Report (rank of e, K).
import itertools, sys
from fractions import Fraction as F
from collections import Counter
sys.path.insert(0,'.')
def nu(r):
    n=0
    while r%2==0: r//=2; n+=1
    return n
def clear(r,t):
    x=(r*t)%1
    return min(x,1-x)>=F(1,8)
def two_adic_ok(R):
    v=max(nu(r) for r in R); M=2**max(v+1,3)
    return any(all(clear(r,F(k,M)) for r in R) for k in range(1,M,2))
def first(R):
    cands=sorted({(F(8*K+1,8*r),e,K) for e,r in enumerate(R) for K in range(0,r)} )
    for t,e,K in cands:
        if t>1: break
        if all(clear(r,t) for r in R): return t,e,K
    return None
N=int(sys.argv[1]); cnt=Counter(); n=0; Kmax=0; none=0
for R in itertools.combinations(range(1,N+1),7):
    if two_adic_ok(R): continue
    n+=1
    f=first(R)
    if f is None: none+=1; continue
    t,e,K=f; cnt[(e,K)]+=1; Kmax=max(Kmax,K)
print("fails",n,"no lonely instant found in (0,1]:",none,"max K",Kmax)
print(sorted(cnt.items(),key=lambda x:-x[1])[:20])
