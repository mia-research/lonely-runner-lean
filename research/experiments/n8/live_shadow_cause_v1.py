"""Separate the two exceptions.
DEAD flank: some ratio d/e is a multiple of 8 (that runner is in the way at EVERY opening).
LIVE shadowed flank: no such ratio, yet all openings blocked -- the real exception.
Question: what does L look like for LIVE shadowed flanks, and is max q >= 8 there (as
LastClass.shadow_needs_full_denom requires)?"""
from math import gcd, lcm
from functools import lru_cache
from collections import Counter
import random, statistics as st
@lru_cache(maxsize=None)
def cls(a,q):
    M=8*q
    return frozenset(k for k in range(q) if (lambda r:min(r,M-r)<q)((a*(8*k+1))%M))
def flank(ds,e):
    qs=[e//gcd(abs(d),e) for d in ds]
    L=lcm(*qs); cov=set()
    dead=any(d%(8*e)==0 for d in ds)
    for d,q in zip(ds,qs):
        c=cls((d//(e//q))%(8*q), q)
        cov|={k for k in range(L) if k%q in c}
    return L,qs,(len(cov)==L),dead
random.seed(12)
live_sh=[]; dead_sh=0; live_tot=0
for _ in range(40000):
    hi=10**random.choice([1,1,2,2,3,4])
    v=random.sample(range(-hi,hi+1),8); s=random.randrange(8)
    ds=[v[j]-v[s] for j in range(8) if j!=s]
    for e in sorted({abs(d) for d in ds}):
        L,qs,sh,dead=flank(ds,e)
        if dead:
            if sh: dead_sh+=1
            continue
        live_tot+=1
        if sh: live_sh.append((L,max(qs),tuple(sorted(qs))))
print(f"LIVE flanks: {live_tot};  live+shadowed: {len(live_sh)} ({100*len(live_sh)/live_tot:.3f}%)")
print(f"dead flanks that were shadowed: {dead_sh}  (these are the trivial exception)")
Ls=[a for a,_,_ in live_sh]; MQ=[b for _,b,_ in live_sh]
print(f"\n  live shadowed L: min={min(Ls)} median={st.median(Ls):.0f} max={max(Ls)}")
print(f"  8 | L for every live shadowed flank: {all(a%8==0 for a in Ls)}")
print(f"  max q >= 8 for every live shadowed flank: {all(b>=8 for b in MQ)}   (min = {min(MQ)})")
print(f"\n  L values seen: {Counter(Ls).most_common(12)}")
print(f"  q-multisets seen: {Counter(c for _,_,c in live_sh).most_common(6)}")
