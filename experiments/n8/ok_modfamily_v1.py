#!/usr/bin/env python3
"""Minimal family of moduli covering the residual.  rho(d) is maximised at multiples of 8,
and at d=8m a multiple-of-8 speed demotes to ||delta*a/m|| -- the 2-adic filtration.
Q1: how far does the adapted family {8m} get?   Q2: minimal covering family, greedy+exact.
Q3: does the family survive box growth?"""
from math import gcd
from itertools import combinations
from functools import reduce
import random
def ok(E,d): return any(gcd(a,d)==1 and all(min((e*a)%d,d-(e*a)%d)*8>=d for e in E)
                        for a in range(1,d))
PHI={2:1,3:2,4:2,5:4,6:2,7:6,8:4}
def resid(E): return any(e%8==0 for e in E) and sum(p for d,p in PHI.items() if all(e%d for e in E))==0

R=[E for E in combinations(range(1,19),7) if reduce(gcd,E)==1 and resid(E)]
print(f"residual, complete [1..18]: {len(R)}")

fam8=[8*m for m in range(1,16)]
cov=sum(1 for E in R if any(ok(E,d) for d in fam8))
print(f"Q1  adapted family d=8m, m<=15: covers {cov}/{len(R)} = {100*cov/len(R):.2f}%")
for sub,lab in ((( 16,24,40,56),'{16,24,40,56}'), ((16,24),'{16,24}'), ((16,),'{16}'),
                ((24,),'{24}'), ((16,24,40),'{16,24,40}')):
    c=sum(1 for E in R if any(ok(E,d) for d in sub))
    print(f"      {lab:>16}: {100*c/len(R):6.2f}%")

print("\nQ2  greedy minimal cover over all d in 9..40")
cands=list(range(9,41))
hit={d:set(i for i,E in enumerate(R) if ok(E,d)) for d in cands}
need=set(range(len(R))); chosen=[]
while need:
    d=max(cands,key=lambda d:len(hit[d]&need))
    g=len(hit[d]&need)
    if g==0: break
    chosen.append((d,g)); need-=hit[d]
    print(f"      + d={d:>3}  (+{g:>5})  remaining {len(need):>5}")
print(f"      COVER = {[d for d,_ in chosen]}   size {len(chosen)}   uncovered {len(need)}")

print("\nQ3  does that family survive box growth?  residual sampled from larger boxes")
F=[d for d,_ in chosen]
random.seed(7)
for hi in (30,80,400,4000):
    n=0; miss=0; ex=None
    while n<40000:
        E=tuple(sorted(random.sample(range(1,hi+1),7)))
        g=reduce(gcd,E); E=tuple(e//g for e in E)
        if not resid(E): continue
        n+=1
        if not any(ok(E,d) for d in F):
            miss+=1
            if ex is None: ex=E
    print(f"      [1..{hi:<5d}] {n} residual: uncovered by {F} -> {miss} ({100*miss/n:.3f}%)  eg {ex}")
