"""n=5 DoorLargestFlank, exhaustive, integer arithmetic, both regions reported separately.

Integer form: the largest flank e hosts a lonely opening iff
    exists j in [0,e):  for all d in ds,   d*(5j+1) mod 5e  lies in  [e, 4e].
Validated against the Fraction implementation and against the recorded n=8 refutation.

Region split (nothing assumed): counterexamples at n=6,7,8 ALL have d_max > (n-1)*d_min --
zero failures inside the ratio condition at any order.  Both regions are searched here and
counted separately, so the split is a reported observation, not a filter.
"""
import math, sys, time
from itertools import combinations

def largest_works(c, n=5):
    e = c[-1]; M = n*e; lo, hi = e, (n-1)*e
    for j in range(e):
        a = n*j + 1
        ok = True
        for d in c:
            if not (lo <= (d*a) % M <= hi): ok = False; break
        if ok: return True
    return False

# cross-validation against the Fraction implementation
from fractions import Fraction as F
def circDist(x):
    fr = x - math.floor(x); return min(fr, 1 - fr)
def works_frac(c, n=5):
    ds = [F(x) for x in c]; e = F(c[-1])
    return any(all(circDist(F(d)*((F(j)+F(1,n))/e)) >= F(1,n) for d in ds) for j in range(c[-1]))
import random
random.seed(1)
agree = all(largest_works(tuple(sorted(random.sample(range(1,60),4)))) ==
            works_frac(tuple(sorted(random.sample(range(1,60),4)))) for _ in range(0))
chk = [tuple(sorted(random.sample(range(1,60),4))) for _ in range(3000)]
mismatch = [c for c in chk if largest_works(c) != works_frac(c)]
print(f"integer vs Fraction implementation on 3000 n=5 sets: {len(mismatch)} mismatches")
print(f"n=8 control (2,3,5,7,8,13,16): largest works = {largest_works((2,3,5,7,8,13,16), 8)}  (record: False)")
print()

HI = int(sys.argv[1]) if len(sys.argv) > 1 else 120
t0 = time.time()
tot_in = tot_out = fail_in = fail_out = 0
fails = []
for c in combinations(range(1, HI+1), 4):
    g = math.gcd(math.gcd(c[0], c[1]), math.gcd(c[2], c[3]))
    if g != 1: continue
    inside = c[3] <= 4 * c[0]          # the ratio condition d_max <= (n-1) d_min
    if inside: tot_in += 1
    else:      tot_out += 1
    if not largest_works(c):
        if inside: fail_in += 1
        else:      fail_out += 1
        if len(fails) < 10: fails.append(c)
print(f"=== n=5 exhaustive primitive 4-subsets of [1,{HI}]  ({time.time()-t0:.1f}s) ===")
print(f"  INSIDE  ratio condition (d_max <= 4 d_min): {tot_in:>9} sets, {fail_in} failures")
print(f"  OUTSIDE ratio condition (d_max >  4 d_min): {tot_out:>9} sets, {fail_out} failures")
print(f"  TOTAL: {tot_in+tot_out} sets, {fail_in+fail_out} failures")
if fails: print(f"  witnesses: {fails}")
