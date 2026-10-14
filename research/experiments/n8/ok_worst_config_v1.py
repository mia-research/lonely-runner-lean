#!/usr/bin/env python3
"""The low point: what is the SMALLEST number of isolation events any runner ever has?
For integer speeds with gcd 1 the period is 1, so events-per-period = event count.
A count of 0 would be an LRC(8) counterexample."""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd
from collections import Counter
from functools import lru_cache

@lru_cache(maxsize=None)
def bsm_good(S):
    iv=[]
    for s in S:
        for k in range(0,s+1):
            lo,hi=max(F(8*k-1,8*s),F(0)),min(F(8*k+1,8*s),F(1))
            if lo<hi: iv.append((lo,hi))
    iv.sort(); m=[]
    for lo,hi in iv:
        if m and lo<m[-1][1]: m[-1][1]=max(m[-1][1],hi)
        else: m.append([lo,hi])
    g=[]; cur=F(0)
    for lo,hi in m:
        if cur<=lo: g.append((cur,lo))
        cur=max(cur,hi)
    if cur<=1: g.append((cur,F(1)))
    return [(a,b) for a,b in g if a<=b and not(a==b==0) and not(a==b==1)]
def cons(V,i): return tuple(sorted({abs(w-V[i]) for w in V if w!=V[i]}))
def globiso(V):
    w=[x-V[0] for x in V]; g=reduce(gcd,[abs(x) for x in w if x]) or 1
    return sorted((x//g)%8 for x in w)==list(range(8))

for N in (16,20):
    hist=Counter(); worst=[]; lo=None
    for V in combinations(range(1,N+1),8):
        if reduce(gcd,V)!=1: continue
        cnt=[len(bsm_good(cons(V,i))) for i in range(8)]
        m=min(cnt); hist[m]+=1
        if lo is None or m<lo: lo=m; worst=[]
        if m==lo and len(worst)<10: worst.append((V,[i+1 for i in range(8) if cnt[i]==m],cnt))
    print(f"8-subsets of [1..{N}], primitive.  min-event-count distribution over configurations:")
    for k in sorted(hist): print(f"      min = {k:>2}: {hist[k]:>7,} configs ({100*hist[k]/sum(hist.values()):5.2f}%)")
    print(f"   LOW POINT = {lo}  (0 would be an LRC counterexample)")
    for V,who,cnt in worst[:6]:
        print(f"      {V}  counts {cnt}  attained by runner(s) {who}  global-iso: {globiso(V)}")
    print()
