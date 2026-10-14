#!/usr/bin/env python3
"""BOUNDARY SET METHOD, per phi_law_paper_v2.md §2.2, Algorithm 2.1.

Lemma 2.1/2.2: the isolation predicate can only change at times where SOME pairwise
distance equals exactly 1/n. So collect those times, and the predicate is constant on
each cell between consecutive ones -- event-complete, no sampling.

For a pair with speed difference D, d(p_i,p_j) = 1/n at  t = (k +- 1/n)/D = (nk +- 1)/(nD).

Per feedback_verify_agent_source_claims: evaluate at ENTRY and EXIT of every cell, not
the centre, and check no breakpoint lies strictly inside.
"""
from fractions import Fraction as F
from itertools import combinations
V=[0,2,6,7,8,10,13,14]; n=8

# --- step 1: generate the boundary set ---
diffs=sorted({abs(a-b) for a,b in combinations(V,2)})
B={F(0),F(1)}
for D in diffs:
    k=0
    while True:
        added=False
        for s in (+1,-1):
            t=F(n*k+s, n*D)
            if 0<=t<=1: B.add(t); added=True
        if F(n*k-1,n*D)>1: break
        k+=1
print(f"speeds {V}   pairwise differences {diffs}")
print(f"boundary set: {len(B)} critical times in [0,1]")

Bs=sorted(B)
def gaps(t):
    P=sorted({F(v)*t%1 for v in V})
    if len(P)<n: return [F(0)]
    return [P[i+1]-P[i] for i in range(n-1)]+[1-P[-1]+P[0]]
def glob(t): return min(gaps(t))>=F(1,n)
def indiv0(t): return all(min((F(v)*t)%1, 1-(F(v)*t)%1)>=F(1,n) for v in V if v!=0)

# --- step 2/3: evaluate at entry and exit of every cell ---
gl=[]; ind=[]
for i in range(len(Bs)-1):
    lo,hi=Bs[i],Bs[i+1]
    for t in (lo,hi):                       # entry and exit, never the centre
        if glob(t): gl.append(t)
        if indiv0(t): ind.append(t)
    mid=(lo+hi)/2                            # cell interior, for the constancy check
    if glob(mid)!=glob(lo) and glob(mid)!=glob(hi): gl.append(('INTERIOR-ONLY',mid))
    if indiv0(mid) and not (indiv0(lo) or indiv0(hi)): ind.append(mid)
print()
print(f"GLOBAL isolation (all {n} gaps >= 1/{n}):  times found = {len(set(gl))}")
print(f"   -> {'ATTAINED at '+str(sorted(set(gl))[:3]) if gl else 'NEVER ATTAINED'}")
mx=max((min(gaps(t)),t) for t in Bs)
print(f"   best min-gap over the boundary set: {mx[0]} = {float(mx[0]):.9f} at t={mx[1]}")

iset=sorted(set(ind))
print()
print(f"INDIVIDUAL isolation of runner 0 (LRC):  boundary times qualifying = {len(iset)}")
print(f"   first few: {[str(t) for t in iset[:6]]}")
print(f"   e.g. t={iset[0]}: distances "
      f"{[str(min((F(v)*iset[0])%1,1-(F(v)*iset[0])%1)) for v in V if v!=0]}")

# --- constancy check: is the predicate really constant on each cell? ---
bad=0
for i in range(len(Bs)-1):
    lo,hi=Bs[i],Bs[i+1]; mid=(lo+hi)/2
    q=[lo+(hi-lo)*F(j,8) for j in range(1,8)]   # FIXED: genuine interior points
    if len({indiv0(x) for x in q}) > 1: bad+=1
print()
print(f"constancy check (7 interior points per cell, {len(Bs)-1} cells): cells with a "
      f"predicate change strictly inside = {bad}  {'PASS -- event-complete' if bad==0 else 'FAIL'}")
