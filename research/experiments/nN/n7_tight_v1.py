"""Order 7: is the DoorTwoLargest tight family bounded, as at orders 5 and 6?

n=5: tight family 57 sets, all d_max <= 15, stable [1,60] -> [1,200].
n=6: tight family 26 sets, all d_max <= 30, stable [1,40] -> [1,80].
Tight = at most ONE working opening across the two largest flanks.  A bounded, stable tight
family is what makes a proof split into a finite check plus a margin argument.
"""
import math, sys
from itertools import combinations

def count_top2(c, n=7, cap=2):
    cnt = 0
    for e in sorted(set(c), reverse=True)[:2]:
        M = n*e; lo, hi = e, (n-1)*e
        for j in range(e):
            a = n*j + 1
            if all(lo <= (d*a) % M <= hi for d in c):
                cnt += 1
                if cnt >= cap: return cap
    return cnt

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

for hi in (14, 16, 18, 20):
    sets = [c for c in combinations(range(1, hi+1), 6) if prim(c)]
    tight = [c for c in sets if count_top2(c) <= 1]
    zero  = [c for c in tight if count_top2(c) == 0]
    mx = max(max(c) for c in tight) if tight else 0
    print(f"[1,{hi}]  sets {len(sets):>7}   TIGHT {len(tight):>4}   with ZERO openings {len(zero)}"
          f"   max element among tight {mx}")
    if zero: print(f"    *** ZERO-OPENING (would refute DoorTwoLargest at n=7): {zero[:5]}")
print()
sets = [c for c in combinations(range(1, 21), 6) if prim(c)]
tight = sorted(c for c in sets if count_top2(c) <= 1)
print(f"tight family at [1,20] ({len(tight)} sets):")
for c in tight: print(f"   {c}")
