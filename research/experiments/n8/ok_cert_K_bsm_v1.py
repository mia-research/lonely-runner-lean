#!/usr/bin/env python3
"""GRID CERTIFICATE and WRAP DEPTH K, redone per-runner with NO adjoined stationary
runner, computed by the BOUNDARY SET METHOD.

A configuration is 8 runners with 8 given speeds V. For runner i the constraints are the
DISTINCT values S_i = {|v_j - v_i|} -- ||.|| is even, so a symmetric pair gives ONE.

BSM (phi_law_paper_v2 §2.2): the predicate ||s t|| >= 1/8 can only change at
t = (8k+-1)/(8s). Collect those, evaluate at entry and exit of each cell. Event-complete
for the PREDICATE (Lemma 2.2) -- which is exactly what a certificate needs.

Certificate: at t = a/8 + eps with r_s = s*a mod 8, constraint s admits
  eps in [ (1-r_s)/(8s) + k/s , (7-r_s)/(8s) + k/s ]  for integer k.
K = max_s |k_s| used.  K=0 is the principal certificate.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
from math import floor

@lru_cache(maxsize=None)
def bsm_goodset(S):
    """closed {t in [0,1]: ||s t|| >= 1/8 for all s in S}, by the boundary set method"""
    iv=[]
    for s in S:
        for k in range(0,s+1):
            lo,hi=max(F(8*k-1,8*s),F(0)),min(F(8*k+1,8*s),F(1))
            if lo<hi: iv.append((lo,hi))
    iv.sort(); m=[]
    for lo,hi in iv:
        if m and lo<m[-1][1]: m[-1][1]=max(m[-1][1],hi)   # STRICT: bad sets are open
        else: m.append([lo,hi])
    g=[]; cur=F(0)
    for lo,hi in m:
        if cur<=lo: g.append((cur,lo))
        cur=max(cur,hi)
    if cur<=1: g.append((cur,F(1)))
    return [(a,b) for a,b in g if a<=b and not(a==b==0) and not(a==b==1)]

def kindex(s,r,eps):
    lo=F(1-r,8*s); k=floor((eps-lo)*s)
    for kk in (k-1,k,k+1):
        if lo+F(kk,s) <= eps <= lo+F(3,4*s)+F(kk,s): return kk
    return None

from functools import lru_cache
@lru_cache(maxsize=None)
def Kmin(S):
    """smallest wrap depth over the four grid points; None if no witness at all"""
    G=bsm_goodset(tuple(S))
    if not G: return None
    best=None
    for a in (1,3,5,7):
        p=F(a,8)
        for lo,hi in G:
            for eps in {lo-p,hi-p} | ({F(0)} if lo<=p<=hi else set()):
                if not (lo<=p+eps<=hi): continue
                ks=[kindex(s,(s*a)%8,eps) for s in S]
                if any(k is None for k in ks): continue
                K=max(abs(k) for k in ks)
                if best is None or K<best: best=K
    return best

N=16
from collections import Counter
hist=Counter(); hist_ext=Counter(); hist_int=Counter(); nowit=0; tot=0
for V in combinations(range(1,N+1),8):
    for i in range(8):
        S=sorted({abs(w-V[i]) for w in V if w!=V[i]})
        K=Kmin(tuple(S)); tot+=1
        if K is None: nowit+=1; continue
        hist[K]+=1
        (hist_ext if i in (0,7) else hist_int)[K]+=1
print(f"8-subsets of [1..{N}], per runner: {tot:,} runner-instances")
print(f"   runners with NO witness at all (would refute LRC): {nowit}")
print()
print(f"   {'K':>3} {'runners':>9} {'share':>8} {'cumulative':>11}   extreme    interior")
c=0
for K in sorted(hist):
    c+=hist[K]
    print(f"   {K:>3} {hist[K]:>9,} {100*hist[K]/tot:>7.2f}% {100*c/tot:>10.2f}%"
          f"   {100*hist_ext[K]/sum(hist_ext.values()):>6.2f}%  {100*hist_int[K]/sum(hist_int.values()):>7.2f}%")
print()
print(f"   PRINCIPAL certificate (K=0) fires: {100*hist[0]/tot:.2f}%")
print(f"   K<=1: {100*(hist[0]+hist[1])/tot:.2f}%    K<=2: {100*(hist[0]+hist[1]+hist[2])/tot:.2f}%")
print(f"   max K needed: {max(hist)}")
print()
print("   old figures (7 distinct speeds + adjoined stationary = EXTREME runners only):")
print("      principal 61.79% of Case 2, K=1 99.94%, K=2 100%")
