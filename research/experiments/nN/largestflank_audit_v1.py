"""Audit of the DoorLargestFlank test: is the opening search bound correct?

The test declares a failure when NO j in range(e) gives a lonely opening at the largest
disparity e.  Two ways that could be wrong:
  (A) the j-bound truncates -> reports failures that are not failures (inflates n=6,7,8)
  (B) something else is miscomputed -> the n=8 control would not have reproduced

(A) is the live risk and it is ONE-SIDED: under-searching j can only ADD false failures,
never remove them.  So the n=5 "zero failures" result is safe from it, and the n=6,7,8
failures are what must be re-checked against a much wider j.
"""
import math
from fractions import Fraction as F

def mk(N):
    INV = F(1, N)
    def circDist(x):
        fr = x - math.floor(x); return min(fr, 1 - fr)
    def lonely(ds, t): return all(circDist(d*t) >= INV for d in ds)
    def fo(e, j): return (F(j) + INV)/e
    return circDist, lonely, fo

print("=== 1. periodicity: is range(e) really complete for integer sets? ===")
print("   flankOpening(e,j) = (j + 1/n)/e ; reading for disparity a is a*(j+1/n)/e.")
print("   j -> j+e  adds  a*e/e = a, an INTEGER, so circDist is unchanged. Period = e.")
circDist, lonely, fo = mk(8)
ds = [F(x) for x in (2,3,5,7,8,13,16)]
same = all(circDist(F(a)*fo(F(16), j)) == circDist(F(a)*fo(F(16), j+16)) for a in (2,3,5,7,8,13,16) for j in range(40))
print(f"   checked empirically on the n=8 witness, j vs j+16: {'periodic, bound is complete' if same else 'NOT periodic -- bound is WRONG'}")
print()

print("=== 2. re-check every reported failure against j up to 50*e (not e) ===")
from itertools import combinations
def audit(N, hi, wide=50):
    circDist, lonely, fo = mk(N); k = N - 1
    narrow_fail, still_fail, spurious = 0, 0, []
    for c in combinations(range(1, hi+1), k):
        g = c[0]
        for x in c[1:]: g = math.gcd(g, x)
        if g != 1: continue
        ds = [F(x) for x in c]; e = F(max(c)); ei = int(e)
        if any(lonely(ds, fo(e, j)) for j in range(ei)): continue
        narrow_fail += 1
        if any(lonely(ds, fo(e, j)) for j in range(ei, wide*ei)):
            spurious.append(c)
        else:
            still_fail += 1
    return narrow_fail, still_fail, spurious

for N, hi in [(6, 26), (7, 20), (8, 16)]:
    nf, sf, sp = audit(N, hi)
    print(f"  n={N} [1,{hi}]:  failures with j<e: {nf}   still failing with j<50e: {sf}   SPURIOUS: {len(sp)}")
    if sp: print(f"      spurious examples: {sp[:5]}")
print()

print("=== 3. one failure written out in full: n=6, ds=(1,3,4,5,6), largest e=6 ===")
circDist, lonely, fo = mk(6)
ds = [F(x) for x in (1,3,4,5,6)]
for j in range(6):
    t = fo(F(6), j)
    rs = [(a, circDist(F(a)*t)) for a in (1,3,4,5,6)]
    bad = [a for a,r in rs if r < F(1,6)]
    print(f"   j={j}  t={str(t):>7}  readings {[(a, str(r)) for a,r in rs]}  below 1/6: {bad}")
print("   -> no j clears every disparity, so flank 6 hosts no lonely opening.")
lo = [(e, j) for e in (1,3,4,5) for j in range(int(e)) if lonely(ds, fo(F(e), j))]
print(f"   working flanks elsewhere: {lo}")
print()

print("=== 4. failure RATE vs range at n=8 (record implies ~0.24% on larger ranges) ===")
for hi in [14, 16, 18, 20, 22]:
    cnt, bad = 0, 0
    for c in combinations(range(1, hi+1), 7):
        g = c[0]
        for x in c[1:]: g = math.gcd(g, x)
        if g != 1: continue
        cnt += 1
        ds = [F(x) for x in c]; e = F(max(c))
        if not any(lonely(ds, fo(e, j)) for j in range(int(e))): bad += 1
    print(f"   [1,{hi}]  sets {cnt:>7}  largest-flank failures {bad:>5}  rate {100*bad/cnt:.3f}%")
