"""The extremal exception for flank shadowing.
Differences may be taken POSITIVE (dist(-x,Z)=dist(x,Z)), and as a MULTISET (a pair d, -d in the
arrangement gives a repeat).  Normalise by gcd = 1.
Flank e (one of the differences): q_j = e/gcd(d_j,e), L = lcm_j q_j | e, openings k in [0,L).
Shadowed iff every opening is blocked.  Find the MAXIMUM number of shadowed flanks."""
from math import gcd, lcm
from functools import lru_cache, reduce
from itertools import combinations_with_replacement
from collections import Counter
import sys
@lru_cache(maxsize=None)
def cls(a,q):
    M=8*q
    return frozenset(k for k in range(q) if (lambda r:min(r,M-r)<q)((a*(8*k+1))%M))
@lru_cache(maxsize=None)
def shadowed(ds,e):
    qs=tuple(e//gcd(d,e) for d in ds)
    L=reduce(lcm,qs); cov=set()
    for d,q in zip(ds,qs):
        c=cls((d//(e//q))%(8*q), q)
        cov|={k for k in range(L) if k%q in c}
        if len(cov)==L: return True
    return False
def count_shadowed(ds):
    return sum(1 for e in sorted(set(ds)) if shadowed(ds,e)), len(set(ds))
N=int(sys.argv[1]) if len(sys.argv)>1 else 20
best=-1; winners=[]; hist=Counter(); tot=0
for ds in combinations_with_replacement(range(1,N+1),7):
    if reduce(gcd,ds)!=1: continue
    tot+=1
    sh,nf=count_shadowed(ds)
    hist[(sh,nf)]+=1
    if sh>best: best,winners=sh,[ds]
    elif sh==best and len(winners)<40: winners.append(ds)
print(f"exhaustive multisets of 7 positive differences from [1,{N}], gcd=1: {tot}")
print(f"  MAXIMUM shadowed flanks = {best}")
print(f"  attained by {len([w for w in winners])}+ multisets; first few:")
for w in winners[:10]:
    nf=len(set(w)); print(f"     {w}   distinct flanks {nf}   shadowed {best}   CLEAR {nf-best}")
print(f"\n  (shadowed, distinct-flanks) histogram, top: {hist.most_common(10)}")
zero=[k for k in hist if k[0]==k[1]]
print(f"  multisets with ZERO clear flanks: {sum(hist[k] for k in zero)}  {'NONE' if not zero else zero[:5]}")
