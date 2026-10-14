"""The exception mechanism, tested three ways.
(A) Live shadowed flanks split by RANK of |e| -- does the L=2 mode vanish at the largest flank?
(B) Is the L=2 mode always two movers on opposite parities, needing |rho| > 1 (so excluded at
    the largest flank by the proved FlankBridge.no_opposite_parity_halves)?
(C) shadow_needs_full_denom's own regime: all movers with 0 < rho < 1. Is max q >= 8 there?"""
from math import gcd, lcm
from functools import lru_cache
from collections import Counter
from fractions import Fraction
import random, statistics as st
@lru_cache(maxsize=None)
def cls(a,q):
    M=8*q
    return frozenset(k for k in range(q) if (lambda r:min(r,M-r)<q)((a*(8*k+1))%M))
def flank(ds,e):
    qs=[e//gcd(abs(d),e) for d in ds]
    L=lcm(*qs); cov=set()
    if any(d%(8*e)==0 for d in ds): return L,qs,False,True
    for d,q in zip(ds,qs):
        cov|={k for k in range(L) if k%q in cls((d//(e//q))%(8*q), q)}
    return L,qs,(len(cov)==L),False
random.seed(21)
byrank=Counter(); shrank=Counter(); Lrank={r:[] for r in range(7)}
L2_needs_big=0; L2_tot=0
for _ in range(40000):
    hi=10**random.choice([1,1,2,2,3,4])
    v=random.sample(range(-hi,hi+1),8); s=random.randrange(8)
    ds=[v[j]-v[s] for j in range(8) if j!=s]
    for r,e in enumerate(sorted({abs(d) for d in ds}, reverse=True)):
        L,qs,sh,dead=flank(ds,e)
        if dead: continue
        byrank[r]+=1
        if sh:
            shrank[r]+=1; Lrank[r].append(L)
            if L==2:
                L2_tot+=1
                if any(abs(Fraction(d,e))>1 for d in ds): L2_needs_big+=1
print("(A) live shadowed rate and L, by rank of |e| (0 = largest)")
print("    rank    live flanks   shadowed    median L of shadowed   min L")
for r in range(7):
    if byrank[r]:
        Ls=Lrank[r]
        print(f"      {r}      {byrank[r]:8d}   {100*shrank[r]/byrank[r]:6.2f}%"
              f"        {st.median(Ls) if Ls else float('nan'):8.0f}          {min(Ls) if Ls else '-'}")
print(f"\n(B) L=2 live shadowed flanks: {L2_tot}; of those, at least one |rho| > 1: "
      f"{L2_needs_big} ({'ALL' if L2_needs_big==L2_tot else 'NOT all'})")

print("\n(C) shadow_needs_full_denom regime -- every mover with 0 < rho < 1 (so 0 < p < q):")
found=[]; n=0
for _ in range(400000):
    e=random.randint(8,60)
    ds=random.sample(range(1,e),6)          # 0 < d < e  =>  0 < rho < 1
    L,qs,sh,dead=flank(ds,e)
    if dead: continue
    n+=1
    if sh: found.append((e,tuple(ds),L,max(qs)))
print(f"    subjects in regime: {n};  live shadowed: {len(found)}")
if found:
    print(f"    max q >= 8 in every one: {all(m>=8 for _,_,_,m in found)}  (min max-q = {min(m for _,_,_,m in found)})")
    for f in found[:4]: print(f"       e={f[0]} ds={f[1]} L={f[2]} maxq={f[3]}")
