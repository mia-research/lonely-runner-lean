"""THE CRUX, reframed.

Band 2 needs the clear set EMPTY in [1,15], not merely null.  The AP's clear set is the eight odd
integers -- non-empty -- so the AP does NOT cover.  Hence:

    uncovered length > 0  ->  clear set has positive measure  ->  non-empty  ->  R <= 15
    uncovered length = 0  ->  ??? profiles ???                ->  need the clear set anyway

If the AP is the UNIQUE profile with zero uncovered length, then every profile either has positive
uncovered length (so a clear interval) or is the AP (so eight clear points).  Either way the clear
set is non-empty and R < 16.

So: hammer the uniqueness.  Search hard for ANY profile with uncovered length 0 that is not the AP.
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
import random, statistics as st
def unc(S, lo, hi):
    bad=[]
    for s in S:
        k=0
        while (8*k-1)/s <= hi+1:
            a,b=(8*k-1)/s,(8*k+1)/s
            if b>lo and a<hi: bad.append((max(a,lo),min(b,hi)))
            k+=1
    bad.sort(); merged=[]
    for a,b in bad:
        if merged and a<=merged[-1][1]: merged[-1]=(merged[-1][0],max(merged[-1][1],b))
        else: merged.append((a,b))
    u=hi-lo
    for a,b in merged: u-=(b-a)
    return max(u,0.0)
def joint(S): return unc(S,1.0,7.0)+unc(S,9.0,15.0)
AP=[2.0,3.0,4.0,5.0,6.0,7.0]
print(f"  AP joint uncovered length: {joint(AP):.12f}")
print(f"  ...but its clear set is the eight odd integers -- NOT a cover.\n")
rng=random.Random(20260919)
TOL=1e-9
hits=[]
best=(9.9,None)
N=0
for restart in range(4000):
    mode=restart%4
    if mode==0:   S=sorted(x+rng.gauss(0,0.4) for x in AP)
    elif mode==1: S=sorted(rng.uniform(1.02,7.98) for _ in range(6))
    elif mode==2: S=sorted(rng.uniform(1.02,16.0) for _ in range(6))
    else:         S=sorted([rng.uniform(1.02,3.0) for _ in range(3)]+[rng.uniform(3.0,8.0) for _ in range(3)])
    if S[0]<=1.02: continue
    cur=joint(S); stall=0
    for _ in range(2500):
        W=list(S); k=rng.randrange(6); W[k]*= (1+rng.gauss(0,0.01))
        W=sorted(W); N+=1
        if W[0]<=1.02 or W[5]>16.0: continue
        v=joint(W)
        if v<cur: S,cur,stall=W,v,0
        elif v==cur: S,stall=W,stall+1
        else: stall+=1
        if stall>350: break
    if cur<TOL:
        d=max(abs(a-b) for a,b in zip(sorted(S),AP)) if len(S)==6 else 9
        hits.append((cur,tuple(round(x,6) for x in S),d))
    if cur<best[0]: best=(cur,tuple(S))
print(f"  {N} evaluations across 4000 restarts, four seeding modes")
print(f"  profiles found with joint uncovered < {TOL}: {len(hits)}")
seen=set()
for u,S,d in hits[:12]:
    if S in seen: continue
    seen.add(S)
    print(f"    {list(S)}   uncovered {u:.2e}   max|s - AP| = {d:.6f}")
print(f"\n  all of them within 1e-3 of the AP? {all(d<1e-3 for _,_,d in hits) if hits else 'n/a'}")
print(f"  best overall: {best[0]:.3e} at {[round(x,6) for x in best[1]]}")
