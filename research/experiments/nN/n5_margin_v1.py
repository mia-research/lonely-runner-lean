"""How TIGHT is n=5 DoorLargestFlank? Count the WORKING openings at the largest flank.

If the minimum count is 1, the claim is barely holding and a wider search may break it.
If it grows with e, the claim is structurally comfortable.  Same diagnostic run at n=6,7,8
where the claim is FALSE, for contrast.
"""
import math
from itertools import combinations

def count_working(c, n):
    e = c[-1]; M = n*e; lo, hi = e, (n-1)*e
    cnt = 0
    for j in range(e):
        a = n*j + 1
        if all(lo <= (d*a) % M <= hi for d in c): cnt += 1
    return cnt

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g, x)
    return g == 1

print("=== minimum number of WORKING openings at the largest flank ===")
print(f"{'n':>3} {'range':>9} {'sets':>9} {'min count':>10} {'#with 0':>8} {'#with 1':>8}   tightest sets")
for n, hi in [(5, 60), (5, 90), (5, 120), (6, 26), (7, 22), (8, 18)]:
    k = n - 1
    mn, zeros, ones, tight = 10**9, 0, 0, []
    tot = 0
    for c in combinations(range(1, hi+1), k):
        if not prim(c): continue
        tot += 1
        w = count_working(c, n)
        if w == 0: zeros += 1
        elif w == 1:
            ones += 1
            if len(tight) < 4: tight.append(c)
        if w < mn: mn = w
    print(f"{n:>3} {('[1,'+str(hi)+']'):>9} {tot:>9} {mn:>10} {zeros:>8} {ones:>8}   {tight}")
