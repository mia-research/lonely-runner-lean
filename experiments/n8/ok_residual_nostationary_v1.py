#!/usr/bin/env python3
"""RESIDUAL ANALYSIS, redone with NO adjoined stationary runner.

A configuration is 8 runners with 8 given speeds V. LRC(8) asks each runner to be lonely.
For runner i the constraints are the DISTINCT values |v_j - v_i| (||.|| is even, so a
symmetric pair gives ONE constraint, not two).

Runner i is settled if either:
  (E1) some d in 2..8 divides no |v_j - v_i|   -> t = a/d gives ||.|| >= 1/d >= 1/8
  (E2) it has <= 3 distinct constraints        -> union bound: bad measure <= 3/4 < 1
Otherwise runner i is RESIDUAL.
"""
from itertools import combinations
from functools import reduce
from math import gcd

def analyse(V):
    n=len(V); out=[]
    for i,v in enumerate(V):
        S=sorted({abs(w-v) for w in V if w!=v})
        e1=[d for d in range(2,9) if all(s%d for s in S)]
        e2=len(S)<=3
        out.append((v,S,e1,e2))
    return out
def globiso(V):
    n=len(V); w=[x-V[0] for x in V]; g=reduce(gcd,[abs(x) for x in w if x]) or 1
    return sorted((x//g)%n for x in w)==list(range(n))

for N in (16,20):
    tot=gi=0; hardpairs=0; pairs=0; hardconfigs=0
    e2only=0
    dist={}
    for V in combinations(range(1,N+1),8):
        tot+=1
        if globiso(V): gi+=1
        res=analyse(V); h=0
        for v,S,e1,e2 in res:
            pairs+=1
            if not e1 and not e2: h+=1; hardpairs+=1
            elif not e1 and e2: e2only+=1
        dist[h]=dist.get(h,0)+1
        if h: hardconfigs+=1
    print(f"8-subsets of [1..{N}]: {tot:,} configurations")
    print(f"   achieve GLOBAL isolation (all 8 at once): {gi:,} = {100*gi/tot:.2f}%")
    print(f"   (config,runner) pairs: {pairs:,};  RESIDUAL runners: {hardpairs:,} = {100*hardpairs/pairs:.2f}%")
    print(f"      settled only by the <=3-constraint union bound: {e2only:,}")
    print(f"   configurations with at least one residual runner: {hardconfigs:,} = {100*hardconfigs/tot:.2f}%")
    print(f"   distribution of residual-runner count per configuration:")
    for h in sorted(dist): print(f"      {h} hard runner(s): {dist[h]:>7,} ({100*dist[h]/tot:5.2f}%)")
    print()
