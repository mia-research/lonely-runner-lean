"""Why does the SMALLEST flank shadow LESS often than the second-smallest?
Because q_j | e: when e is tiny every q_j is tiny too, and a mover with q=1 has an INTEGER
ratio -- inert unless it is a multiple of 8 (which would make the flank dead).  So a live
flank with e = 1 has no blockers at all and is clear outright."""
from math import gcd, lcm
from functools import lru_cache
from collections import Counter
import random
@lru_cache(maxsize=None)
def cls(a,q):
    M=8*q
    return frozenset(k for k in range(q) if (lambda r:min(r,M-r)<q)((a*(8*k+1))%M))
def flank(ds,e):
    qs=[e//gcd(abs(d),e) for d in ds]; L=lcm(*qs); cov=set()
    if any(d%(8*e)==0 for d in ds): return L,qs,False,True
    for d,q in zip(ds,qs):
        cov|={k for k in range(L) if k%q in cls((d//(e//q))%(8*q), q)}
    return L,qs,(len(cov)==L),False
random.seed(31)
byE=Counter(); shE=Counter(); rank6E=Counter()
for _ in range(60000):
    hi=10**random.choice([1,1,2,2,3,4])
    v=random.sample(range(-hi,hi+1),8); s=random.randrange(8)
    ds=[v[j]-v[s] for j in range(8) if j!=s]
    es=sorted({abs(d) for d in ds}, reverse=True)
    if len(es)<7: continue
    e=es[6]; rank6E[min(e,9)]+=1
    L,qs,sh,dead=flank(ds,e)
    if dead: continue
    byE[min(e,9)]+=1
    if sh: shE[min(e,9)]+=1
print("smallest-flank |e| (9 = '>=9'), how often that flank is live-shadowed:")
for e in sorted(byE):
    lbl=f"{e}" if e<9 else ">=9"
    print(f"   e={lbl:<4} live flanks {byE[e]:7d}   shadowed {100*shE[e]/byE[e]:6.2f}%"
          f"    share of all rank-6 flanks {100*rank6E[e]/sum(rank6E.values()):5.1f}%")
print("\n  e=1 forces every q_j = 1, so every mover has an integer ratio:")
print("  inert unless a multiple of 8, and a multiple of 8 would make the flank DEAD.")
