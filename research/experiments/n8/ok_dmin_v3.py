#!/usr/bin/env python3
"""ADVERSARY: dmin is NOT universally bounded.  If one speed is lcm(1..D) then every
d<=D divides it, that runner sits at 0 for every a, so dmin > D.  Random sampling cannot
find this.  Measure how dmin actually grows, and against what."""
from math import gcd, lcm
from functools import reduce
import random
def ok(E,d,a): return all(min((e*a)%d, d-(e*a)%d)*8 >= d for e in E)
def dmin(E,cap=40000):
    for d in range(2,cap+1):
        for a in range(1,d):
            if gcd(a,d)==1 and ok(E,d,a): return d
    return None

print(f"{'D':>3} {'lcm(1..D)':>12} {'E = (lcm, 1,2,3,5,7,11)':>8}  {'dmin':>6}  {'dmin>D?':>8}")
for D in (6,8,10,12,14,16,18,20,22):
    L=reduce(lcm,range(1,D+1))
    E=tuple(sorted({L,1,2,3,5,7,11}))
    if len(E)!=7: continue
    d=dmin(E)
    print(f"{D:>3} {L:>12} {'':>8}  {d:>6}  {str(d>D):>8}")

print("\nsame, with the other six speeds also adversarial (all dividing L):")
for D in (6,8,10,12,14,16,18):
    L=reduce(lcm,range(1,D+1))
    E=tuple(sorted({L, L//2, L//3, L//4, L//5, L//6, L//7 if L%7==0 else L//8}))
    if len(E)!=7: continue
    g=reduce(gcd,E); E=tuple(e//g for e in E)
    d=dmin(E)
    print(f"  D={D:>3}  E={E}  ->  dmin={d}")

print("\nSANITY: a witness must actually exist (LRC(8) is true) -- verify the found d")
L=reduce(lcm,range(1,13)); E=tuple(sorted({L,1,2,3,5,7,11}))
d=dmin(E)
a=[x for x in range(1,d) if gcd(x,d)==1 and ok(E,d,x)][0]
print(f"  E={E}  d={d} a={a}")
print(f"  distances*8/d: {[min((e*a)%d,d-(e*a)%d)*8/d for e in E]}  (all >= 1 required)")
