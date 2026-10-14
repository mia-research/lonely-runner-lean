"""Profile of the largest-flank counterexamples: where exactly do they live?"""
import math
from itertools import combinations
from collections import Counter

def largest_works(c, n):
    e = c[-1]; M = n*e; lo, hi = e, (n-1)*e
    for j in range(e):
        a = n*j + 1
        if all(lo <= (d*a) % M <= hi for d in c): return True
    return False

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g, x)
    return g == 1

for n, hi in [(6, 34), (7, 26), (8, 22)]:
    k = n - 1
    fails = [c for c in combinations(range(1, hi+1), k) if prim(c) and not largest_works(c, n)]
    print(f"=== n={n}, exhaustive [1,{hi}]: {len(fails)} failures ===")
    print(f"   d_min distribution : {dict(sorted(Counter(c[0] for c in fails).items()))}")
    print(f"   d_max distribution : {dict(sorted(Counter(c[-1] for c in fails).items()))}")
    print(f"   max d_min/d_max    : {max(c[0]/c[-1] for c in fails):.5f}   (1/(n-1) = {1/(n-1):.5f})")
    print(f"   max d_min          : {max(c[0] for c in fails)}")
    print(f"   min d_max          : {min(c[-1] for c in fails)}")
    # does d_max <= (n-1)*d_min ever fail?
    inside = [c for c in fails if c[-1] <= (n-1)*c[0]]
    print(f"   failures INSIDE the ratio condition d_max <= (n-1)d_min: {len(inside)}  {inside[:3]}")
    print()
