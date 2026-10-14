"""Door 5: the best flank's rank from the large end, EXHAUSTIVELY.

n=8 record (Spec/Doors.lean): over 35,872 sampled sets the best rank was 1 in 35,785 cases,
2 in 84, 3 in 3, never 4 -- "so three is the right number and it is attained".  The three
rank-3 sets are named: (1,3,5,7,8,14,16), (1,4,5,6,7,8,14), (1,3,4,5,7,12,16).
This reproduces that as a control and asks what the number is at n = 5, 6, 7.
"""
import math
from fractions import Fraction as F
from itertools import combinations

def mk(N):
    INV = F(1, N)
    def circDist(x):
        fr = x - math.floor(x); return min(fr, 1 - fr)
    def lonely(ds, t): return all(circDist(d*t) >= INV for d in ds)
    def flankOpening(e, j): return (F(j) + INV)/e
    return lonely, flankOpening

def sweep(N, hi):
    lonely, flankOpening = mk(N); k = N - 1
    dist, worst, wsets, cnt = {}, 0, [], 0
    for c in combinations(range(1, hi+1), k):
        g = c[0]
        for x in c[1:]: g = math.gcd(g, x)
        if g != 1: continue
        cnt += 1
        ds = [F(x) for x in c]
        best = 99
        for r, e in enumerate(sorted(ds, reverse=True), 1):
            if any(lonely(ds, flankOpening(e, j)) for j in range(int(e))):
                best = r; break
        dist[best] = dist.get(best, 0) + 1
        if best > worst: worst, wsets = best, [c]
        elif best == worst and len(wsets) < 4: wsets.append(c)
    return cnt, dist, worst, wsets

print("=== CONTROL: n=8 over [1,16] (contains the three recorded rank-3 sets) ===")
cnt, dist, worst, wsets = sweep(8, 16)
print(f"  sets {cnt}   distribution {dict(sorted(dist.items()))}   worst rank {worst}")
print(f"  rank-{worst} sets found: {wsets}")
print(f"  recorded rank-3 sets: (1,3,5,7,8,14,16), (1,4,5,6,7,8,14), (1,3,4,5,7,12,16)")
print()

print("=== exhaustive flank-rank distribution per order ===")
print(f"{'n':>3} {'range':>9} {'sets':>9} {'worst':>6}  distribution")
for N, hi in [(5, 45), (5, 60), (6, 26), (6, 30), (7, 20), (7, 23), (8, 18), (8, 20)]:
    cnt, dist, worst, wsets = sweep(N, hi)
    print(f"{N:>3} {('[1,'+str(hi)+']'):>9} {cnt:>9} {worst:>6}  {dict(sorted(dist.items()))}")
    if worst >= 3: print(f"        rank-{worst} witnesses: {wsets}")
