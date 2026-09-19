"""Two native facts, replacing the density frame entirely.
(A) If the difference multiset has gcd 1, then for EVERY flank e:   L = lcm_j(e/gcd(d_j,e)) = e.
    Reason: g_j = gcd(d_j,e) all divide e and gcd_j(g_j) = gcd(gcd_j d_j, e) = 1, and
    lcm_j(e/g_j) = e/gcd_j(g_j) = e.
    So a flank has EXACTLY e openings, and d_max is the flank with the most openings.
(B) Mover d covers exactly c*gcd(d,e) of those e openings, c = #blocked classes mod q.
    Shadowing therefore needs  sum_j c_j*gcd(d_j,e) >= e  -- a gcd-weighted count, no density."""
from math import gcd, lcm
from functools import lru_cache, reduce
from itertools import combinations_with_replacement
import random
@lru_cache(maxsize=None)
def cls(a,q):
    M=8*q
    return frozenset(k for k in range(q) if (lambda r:min(r,M-r)<q)((a*(8*k+1))%M))
badA=0; badB=0; nA=0; nB=0; tight=[]
random.seed(2)
for _ in range(200000):
    ds=tuple(random.randint(1,60) for _ in range(7))
    g=reduce(gcd,ds); ds=tuple(d//g for d in ds)
    for e in set(ds):
        qs=[e//gcd(d,e) for d in ds]; L=reduce(lcm,qs)
        nA+=1
        if L!=e: badA+=1
        cov=set()
        for d,q in zip(ds,qs):
            c=cls((d//(e//q))%(8*q), q)
            own={k for k in range(L) if k%q in c}
            nB+=1
            if len(own)!=len(c)*gcd(d,e): badB+=1
            cov|=own
        if len(cov)==L:
            tight.append((sum(len(cls((d//(e//(e//gcd(d,e))))%(8*(e//gcd(d,e))), e//gcd(d,e)))*gcd(d,e)
                             for d in ds), e))
print(f"(A) L = e whenever gcd(multiset) = 1: {nA} flanks, {'HOLDS' if badA==0 else f'FAILS {badA}'}")
print(f"(B) mover d covers exactly c*gcd(d,e) openings: {nB} movers, "
      f"{'HOLDS' if badB==0 else f'FAILS {badB}'}")
print(f"(C) on {len(tight)} shadowed flanks, the count sum_j c_j*gcd(d_j,e) >= e: "
      f"{'ALWAYS' if all(s>=e for s,e in tight) else 'FAILS'}; "
      f"min slack (sum - e) = {min(s-e for s,e in tight)}")
print("\n   the extremal set (2,3,4,5,6,7,16): openings e and gcd-weighted cover per flank")
ds=(2,3,4,5,6,7,16)
for e in sorted(set(ds)):
    tot=0; parts=[]
    for d in ds:
        q=e//gcd(d,e); c=len(cls((d//(e//q))%(8*q), q)); tot+=c*gcd(d,e)
        parts.append(f"{d}:{c}x{gcd(d,e)}")
    print(f"     e={e:3d}  openings={e:3d}  cover={tot:3d}  [{' '.join(parts)}]"
          f"   {'shadowed' if tot>=e else ''}")
