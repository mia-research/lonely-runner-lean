"""max tau over EXHAUSTIVE primitive difference sets, and its growth with the range.

The n=8 record (Spec/Doors.lean, CAP_DEFECT_v1.md) states: exhaustive over every primitive
7-subset of [1,22], max tau = 33/56 = 0.58929 at (2,6,8,9,11,14,15); and the maximum is NOT
stable -- 17/24 on [1,24], 17/22 on [1,30], and it keeps climbing.  That instability is what
refuted DoorFirstLap.  This reproduces the n=8 figures as a control and measures the same
quantity at n = 5, 6, 7.
"""
import math
from fractions import Fraction as F
from itertools import combinations

def mk(N):
    INV = F(1, N)
    def circDist(x):
        fr = x - math.floor(x); return min(fr, 1 - fr)
    def inWay(d, t): return circDist(d*t) < INV
    def nextOpening(d, t): return (F(math.ceil(d*t - INV)) + INV)/d
    def cascade(ds, cap=100000):
        a = min(ds); t = F(1,1)/(N*a)
        for _ in range(cap):
            act = [d for d in ds if inWay(d, t)]
            if not act: return t
            t = max(nextOpening(d, t) for d in act)
        return None
    return cascade

def sweep(N, hi):
    casc = mk(N); k = N - 1
    worst, wset, cnt = F(0), None, 0
    for c in combinations(range(1, hi+1), k):
        g = c[0]
        for x in c[1:]: g = math.gcd(g, x)
        if g != 1: continue
        cnt += 1
        ds = [F(x) for x in c]
        t = casc(ds)
        if t is None: continue
        tau = F(c[0]) * t
        if tau > worst: worst, wset = tau, c
    return cnt, worst, wset

print("=== CONTROL: n=8, exhaustive primitive 7-subsets of [1,22] ===")
cnt, w, ws = sweep(8, 22)
print(f"  sets {cnt}   max tau {w} = {float(w):.5f}   at {ws}")
print(f"  recorded: 170,213 sets, 33/56 = 0.58929 at (2,6,8,9,11,14,15)")
print(f"  CONTROL {'PASSES' if w == F(33,56) else 'DIFFERS -- investigate'}")
print()

print("=== growth of max tau with the range, per order ===")
print(f"{'n':>3} {'range':>10} {'sets':>9} {'max tau':>12} {'float':>9}  witness")
for N, ranges in [(5, [20,30,40,55,70]), (6, [18,22,26,30,34]), (7, [16,19,22,25]), (8, [18,20,22,24])]:
    prev = None
    for hi in ranges:
        cnt, w, ws = sweep(N, hi)
        mark = "" if prev is None or w == prev else "  <-- increased"
        print(f"{N:>3} {('[1,'+str(hi)+']'):>10} {cnt:>9} {str(w):>12} {float(w):>9.5f}  {ws}{mark}")
        prev = w
    print()
