"""Replacement for the withdrawn count-weighting: weight by DIFFICULTY, not by instance count.

Difficulty proxy: R, the least clear point >= 1.  R = 1 means it clears at the first instant.
Report, per k, the tail -- where the actual work is.
"""
from fractions import Fraction as F
from math import gcd
from functools import reduce
from collections import defaultdict
import random

def clear(S, x):
    for s in S:
        y = s*x
        if abs(y - 8*round(y/8)) < 1: return False
    return True
def R_exact(S, hi=F(16)):
    c = {F(1)}
    for s in S:
        k = 0
        while F(8*k+1,1)/s <= hi:
            for num in (8*k+1, 8*k-1):
                if num > 0:
                    x = F(num,1)/s
                    if 1 <= x <= hi: c.add(x)
            k += 1
    for x in sorted(c):
        if clear(S, x): return x
    return None

rng = random.Random(20260919)
byk = defaultdict(list); hard = []
for _ in range(40000):
    A = sorted(rng.sample(range(1, 300), 7))
    g = reduce(gcd, A); red=[x//g for x in A]; dmin=min(red)
    S=[F(x,dmin) for x in red]
    k = sum(1 for x in red if x % dmin != 0)
    R = R_exact(S)
    if R is None: continue
    byk[k].append(R)
    if R > 2: hard.append((R, k, red))
print(f"{'k':>3} {'n':>7} {'R=1':>7} {'R>1.25':>8} {'R>1.5':>7} {'R>2':>7} {'R>3':>7} {'maxR':>8}")
tot_hard = defaultdict(int)
for k in sorted(byk):
    v=byk[k]; n=len(v)
    f=lambda t: 100*sum(1 for r in v if r> t)/n
    tot_hard[k]=sum(1 for r in v if r>2)
    print(f"{k:>3} {n:>7,} {100*sum(1 for r in v if r==1)/n:>6.1f}% {f(F(5,4)):>7.2f}% "
          f"{f(F(3,2)):>6.2f}% {f(2):>6.2f}% {f(3):>6.2f}% {float(max(v)):>8.4f}")
H=sum(tot_hard.values())
print(f"\n  instances with R > 2 (a real cascade), by k:")
for k in sorted(tot_hard):
    if H: print(f"     k={k}: {tot_hard[k]:>5,}  ({100*tot_hard[k]/H:5.1f}% of all hard instances)")
print(f"\n  hardest found: R = {float(max(hard)[0]):.4f} at k = {max(hard)[1]}, speeds {max(hard)[2]}")
