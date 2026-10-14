"""P6 candidate: use a DIFFERENT flank.

`lonely_iff_exists_flank` allows ANY flank, not the largest.  Every residue set contains a
disparity divisible by 5.  Taking THAT as the flank puts us in the `n | e` case, where
`flankWorks_of_prime_dvd` applies -- except that theorem also assumes every other disparity is
smaller than the flank, which fails when the multiple is not the largest.

So: measure how much the other flanks buy, before deciding whether to generalise the theorem.
"""
import math
from itertools import combinations

def flank_works(ds, e, n=5):
    M = n*e; lo, hi = e, (n-1)*e
    return any(all(lo <= (d*(n*j+1)) % M <= hi for d in ds) for j in range(e))

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

hi = 34
from collections import Counter
tot = res = anyflank = mult5flank = 0
which = Counter()
for c in combinations(range(1, hi+1), 4):
    if not prim(c): continue
    e = c[-1]; nf = c[:-1]
    P1 = all(d % 5 != 0 for d in nf); P2 = e <= 4*c[0]; P3 = e <= 15
    if P1 or P2 or P3: continue
    tot += 1
    # does SOME flank work?
    ok = [d for d in c if flank_works(c, d)]
    if ok: anyflank += 1
    which[len(ok)] += 1
    # does a 5-MULTIPLE flank work?
    if any(flank_works(c, d) for d in c if d % 5 == 0): mult5flank += 1
print(f"sets outside P1'/P2/P3 in [1,{hi}]: {tot}")
print(f"   some flank hosts a lonely opening      : {anyflank}  ({100*anyflank/tot:.2f}%)")
print(f"   a 5-MULTIPLE flank works               : {mult5flank}  ({100*mult5flank/tot:.2f}%)")
print(f"   number of working flanks, distribution : {dict(sorted(which.items()))}")
print()
print("=== of the sets where the LARGEST flank fails, does another flank work? ===")
lf = an = 0
for c in combinations(range(1, hi+1), 4):
    if not prim(c): continue
    if flank_works(c, c[-1]): continue
    lf += 1
    if any(flank_works(c, d) for d in c[:-1]): an += 1
print(f"   largest-flank failures: {lf};  another flank works for {an}  ({100*an/lf if lf else 0:.1f}%)")
