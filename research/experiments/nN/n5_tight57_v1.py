"""The n=5 sets with exactly ONE working opening at the largest flank.

The count is 57 and stable from [1,60] through [1,120], while at n=6,7,8 the analogous count
grows with the range.  If the 57 are a bounded family, an n=5 proof splits into: a finite
check on them, and a margin argument for everything else.
"""
import math
from itertools import combinations

def working(c, n=5):
    e = c[-1]; M = n*e; lo, hi = e, (n-1)*e
    return [j for j in range(e) if all(lo <= (d*(n*j+1)) % M <= hi for d in c)]

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g, x)
    return g == 1

for HI in (60, 120, 170):
    tight = [(c, working(c)[0]) for c in combinations(range(1, HI+1), 4)
             if prim(c) and len(working(c)) == 1]
    print(f"[1,{HI}]: {len(tight)} tight sets   max element among them: {max(max(c) for c,_ in tight)}")
print()
tight = [(c, working(c)[0]) for c in combinations(range(1, 170+1), 4)
         if prim(c) and len(working(c)) == 1]
print("=== the complete tight family (set, its single working opening j) ===")
for c, j in tight:
    print(f"   {str(c):>22}   j = {j}   d_max/d_min = {c[3]/c[0]:.3f}")
print()
print(f"total {len(tight)}")
print(f"largest element appearing: {max(max(c) for c,_ in tight)}")
print(f"all have d_min <= {max(c[0] for c,_ in tight)}, d_max <= {max(c[3] for c,_ in tight)}")
