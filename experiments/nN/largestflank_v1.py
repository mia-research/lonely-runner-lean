"""DoorLargestFlank: does the LARGEST disparity always host a lonely opening?

n=8 record (Spec/Doors.lean): REFUTED -- (2,3,5,7,8,13,16) has no lonely opening at flank 16
and needs flank 13, lap 1.  Control on that witness first, then the question at n = 5, 6, 7.
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

print("=== CONTROL: the recorded n=8 refutation (2,3,5,7,8,13,16) ===")
lonely, fo = mk(8)
ds = [F(x) for x in (2,3,5,7,8,13,16)]
top = F(16)
hits16 = [j for j in range(16) if lonely(ds, fo(top, j))]
hits13 = [j for j in range(13) if lonely(ds, fo(F(13), j))]
print(f"  lonely openings at flank 16: {hits16}   (record: none)")
print(f"  lonely openings at flank 13: {hits13}   (record: lap 1)")
print(f"  CONTROL {'PASSES' if hits16 == [] and 1 in hits13 else 'FAILS -- stop'}")
print()

def sweep(N, hi):
    lonely, fo = mk(N); k = N - 1
    cnt, fails, examples = 0, 0, []
    for c in combinations(range(1, hi+1), k):
        g = c[0]
        for x in c[1:]: g = math.gcd(g, x)
        if g != 1: continue
        cnt += 1
        ds = [F(x) for x in c]
        e = F(max(c))
        if not any(lonely(ds, fo(e, j)) for j in range(int(e))):
            fails += 1
            if len(examples) < 5: examples.append(c)
    return cnt, fails, examples

print("=== does the LARGEST disparity always work? (exhaustive, primitive sets) ===")
print(f"{'n':>3} {'range':>9} {'sets':>9} {'failures':>9}  verdict")
for N, hi in [(5, 40), (5, 60), (5, 80), (6, 26), (6, 32), (7, 20), (7, 24), (8, 16), (8, 18)]:
    cnt, fails, ex = sweep(N, hi)
    v = f"REFUTED ({fails})" if fails else "holds on this range"
    print(f"{N:>3} {('[1,'+str(hi)+']'):>9} {cnt:>9} {fails:>9}  {v}")
    if ex: print(f"        witnesses: {ex}")
