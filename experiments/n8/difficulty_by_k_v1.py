"""Is the 99.95% meaningful, or does it count trivially easy instances?

Measure difficulty per k.  Proxies: R (least clear point >= 1 -- R = 1 means it clears instantly),
and the width of the clear set (how much room the witness has).
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
byk = defaultdict(list)
for _ in range(12000):
    A = sorted(rng.sample(range(1, 300), 7))
    g = reduce(gcd, A); red = [x//g for x in A]
    dmin = min(red)
    S = [F(x, dmin) for x in red]
    k = sum(1 for x in red if x % dmin != 0)
    R = R_exact(S)
    if R is not None: byk[k].append(R)
print(f"{'k':>3} {'instances':>10} {'R = 1 (clears instantly)':>26} {'median R':>10} {'max R':>10}")
for k in sorted(byk):
    v = byk[k]
    one = sum(1 for r in v if r == 1)
    med = sorted(v)[len(v)//2]
    print(f"{k:>3} {len(v):>10,} {100*one/len(v):>25.1f}% {float(med):>10.4f} {float(max(v)):>10.4f}")
print()
print("  R = 1 means the profile clears at the very first instant -- no cascade, nothing to prove.")
