"""WHY rank 1 at n=5 but not n=6?  Measure the actual blocking capacity.

At flank e, opening j (j in [0,e)), disparity d is BLOCKED when
    d*(n*j+1) mod n*e  is NOT in [e, (n-1)e].
The flank itself, d = e, is never blocked (it sits at exactly 1/n).
So only the other n-2 disparities block.

If  sum over non-flank d of (#blocked j)  <  e , then some opening survives BY PIGEONHOLE,
with no arithmetic beyond counting.  Question: is that sum always < e at n=5?  And is it
sometimes >= e at n=6, which would explain the split exactly.
"""
import math
from itertools import combinations

def blocked_count(d, e, n):
    M = n*e; lo, hi = e, (n-1)*e
    return sum(1 for j in range(e) if not (lo <= (d*(n*j+1)) % M <= hi))

def capacity(c, n):
    """sum of blocked counts over non-flank disparities, as a multiple of e."""
    e = c[-1]
    return sum(blocked_count(d, e, n) for d in c[:-1]) / e

def works(c, n):
    e = c[-1]; M = n*e; lo, hi = e, (n-1)*e
    return any(all(lo <= (d*(n*j+1)) % M <= hi for d in c) for j in range(e))

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

print("=== blocking capacity  (sum of blocked counts) / e ;  < 1 forces a survivor ===")
print(f"{'n':>3} {'range':>9} {'sets':>9} {'max capacity':>13} {'#with cap>=1':>13} {'#failures':>10}   witness at max")
for n, hi in [(5,40),(5,60),(5,80),(6,26),(6,34),(7,20),(7,24),(8,16),(8,18)]:
    k = n-1
    mx, mset, over, fails = 0.0, None, 0, 0
    tot = 0
    for c in combinations(range(1,hi+1), k):
        if not prim(c): continue
        tot += 1
        cap = capacity(c, n)
        if cap >= 1.0: over += 1
        if cap > mx: mx, mset = cap, c
        if not works(c, n): fails += 1
    print(f"{n:>3} {('[1,'+str(hi)+']'):>9} {tot:>9} {mx:>13.5f} {over:>13} {fails:>10}   {mset}")
