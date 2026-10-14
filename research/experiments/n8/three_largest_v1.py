"""DoorThreeLargest, exhaustively.
The tree records it EMPIRICAL over 35,872 sampled sets: the best clear flank, ranked from the
LARGE end, was 1 (35,785), 2 (84), 3 (3), never 4.  Make that exhaustive.
rank 1 = largest flank clear; rank r = the r-th largest is the first clear one."""
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
    qs=tuple(e//gcd(d,e) for d in ds); L=reduce(lcm,qs); cov=set()
    for d,q in zip(ds,qs):
        cov|={k for k in range(L) if k%q in cls((d//(e//q))%(8*q), q)}
        if len(cov)==L: return True
    return False
N=int(sys.argv[1]) if len(sys.argv)>1 else 20
hist=Counter(); worst=0; ex=[]; none=[]
tot=0
for ds in combinations_with_replacement(range(1,N+1),7):
    if reduce(gcd,ds)!=1: continue
    tot+=1
    fl=sorted(set(ds), reverse=True)
    r=next((i+1 for i,e in enumerate(fl) if not shadowed(ds,e)), None)
    if r is None: none.append(ds); continue
    hist[r]+=1
    if r>worst: worst,ex=r,[ds]
    elif r==worst and len(ex)<12: ex.append(ds)
print(f"exhaustive multisets of 7 positive differences from [1,{N}], gcd=1: {tot}")
print(f"  rank of first clear flank from the LARGE end: {dict(sorted(hist.items()))}")
print(f"  WORST rank = {worst}   (tree's sampled record: never worse than 3)")
print(f"  multisets with NO clear flank: {len(none)}")
for d in ex[:12]:
    fl=sorted(set(d), reverse=True)
    st=[('S' if shadowed(d,e) else 'C') for e in fl]
    print(f"     {d}  flanks(desc)={fl}  {''.join(st)}")

# structure of the worst cases: do they all carry a scaled Klein core {g,3g,4g,5g,7g}?
def has_core(ds):
    for g in range(1, max(ds)//7+1):
        if all(g*p in ds for p in (1,3,4,5,7)): return g
    return None
print(f"\n  structure of the {len(ex)} worst-rank sets shown / all rank-{worst} sets:")
allworst=[d for d in combinations_with_replacement(range(1,N+1),7)
          if reduce(gcd,d)==1 and
          next((i+1 for i,e in enumerate(sorted(set(d),reverse=True)) if not shadowed(d,e)),0)==worst]
withcore=[d for d in allworst if has_core(d)]
print(f"    rank-{worst} sets: {len(allworst)};  carrying a scaled Klein core {{g,3g,4g,5g,7g}}: {len(withcore)}")
for d in allworst:
    if not has_core(d): print(f"      NO CORE: {d}")
