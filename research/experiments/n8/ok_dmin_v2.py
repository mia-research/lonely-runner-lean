#!/usr/bin/env python3
"""Does dmin stay bounded as speeds grow?  Whether t=a/d works depends only on E mod d,
so dmin(E) <= D is a condition on E mod lcm(1..D) -- box-free in principle.  Test it."""
from math import gcd
from itertools import combinations
from functools import reduce
import random
from collections import Counter

def ok(E,d,a): return all(min((e*a)%d, d-(e*a)%d)*8 >= d for e in E)
def dmin(E,cap=2000):
    for d in range(2,cap+1):
        for a in range(1,d):
            if gcd(a,d)==1 and ok(E,d,a): return d
    return None
PHI={2:1,3:2,4:2,5:4,6:2,7:6,8:4}
def resid(E): return sum(p for d,p in PHI.items() if all(e%d for e in E))==0 and any(e%8==0 for e in E)

random.seed(20260911)
print(f"{'box':>12} {'residual sampled':>17} {'max dmin':>9}   argmax")
for hi,N in ((30,200000),(60,300000),(150,300000),(600,300000),(5000,300000)):
    best=(0,None); n=0
    while n<N:
        E=tuple(sorted(random.sample(range(1,hi+1),7)))
        g=reduce(gcd,E)
        if g>1: E=tuple(e//g for e in E)
        if not resid(E): continue
        n+=1
        d=dmin(E)
        if d and d>best[0]: best=(d,E)
    print(f"  [1..{hi:<6d}] {n:>15d} {best[0]:>9d}   {best[1]}")

print("\nADVERSARIAL: force the residual structure with a large common scale + resonances")
best=(0,None)
for _ in range(120000):
    base=[8,6,5,7]
    extra=random.sample(range(1,400),3)
    E=sorted(set([b*random.choice([1,2,3,4,5,6,7,8,9,11,13]) for b in base]+extra))
    if len(E)!=7: continue
    g=reduce(gcd,E); E=tuple(e//g for e in E)
    if not resid(E): continue
    d=dmin(E)
    if d and d>best[0]: best=(d,E)
print(f"  max dmin {best[0]}   at {best[1]}")

print("\n3-term-relation-rich (the extremum's signature): e_i+e_j=e_k built in")
best=(0,None)
for _ in range(120000):
    a,b=random.sample(range(1,120),2)
    E=sorted(set([a,b,a+b,2*a,2*b,2*(a+b),a+2*b]))
    if len(E)!=7: continue
    g=reduce(gcd,E); E=tuple(e//g for e in E)
    if not resid(E): continue
    d=dmin(E)
    if d and d>best[0]: best=(d,E)
print(f"  max dmin {best[0]}   at {best[1]}")
