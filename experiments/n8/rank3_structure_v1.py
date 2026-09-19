"""What do the rank-3 sets actually have in common?  Test candidate invariants, do not eyeball."""
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
def rank(ds):
    fl=sorted(set(ds), reverse=True)
    return next((i+1 for i,e in enumerate(fl) if not shadowed(ds,e)), 99)
N=int(sys.argv[1]) if len(sys.argv)>1 else 20
R={}
for ds in combinations_with_replacement(range(1,N+1),7):
    if reduce(gcd,ds)!=1: continue
    r=rank(ds)
    if r>=2: R.setdefault(r,[]).append(ds)
for r in sorted(R):
    print(f"rank {r}: {len(R[r])} sets")
w=max(R)
S=R[w]
print(f"\ninvariants over all {len(S)} rank-{w} sets:")
tests={
 "contains 7":            lambda d: 7 in d,
 "contains 1":            lambda d: 1 in d,
 "contains 5":            lambda d: 5 in d,
 "contains a multiple of 8": lambda d: any(x%8==0 for x in d),
 "some even":             lambda d: any(x%2==0 for x in d),
 "max is even":           lambda d: max(d)%2==0,
 "the clear flank is 7":  lambda d: sorted(set(d),reverse=True)[w-1]==7,
 "clear flank <= 7":      lambda d: sorted(set(d),reverse=True)[w-1]<=7,
 "7 distinct values":     lambda d: len(set(d))==7,
}
for name,f in tests.items():
    k=sum(1 for d in S if f(d))
    print(f"   {name:28s}: {k}/{len(S)}  {'ALL' if k==len(S) else ''}")
print(f"\n   value of the first clear flank: {Counter(sorted(set(d),reverse=True)[w-1] for d in S).most_common()}")
print(f"   the two shadowed larger flanks: {Counter(tuple(sorted(set(d),reverse=True)[:w-1]) for d in S).most_common(8)}")
