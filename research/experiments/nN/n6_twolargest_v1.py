"""n=6: does one of the TWO largest disparities host a lonely opening?

At n=5 the LARGEST alone works (DoorLargestFlank; 172M sets, 0 failures).  At n=6 that is
refuted, and the exhaustive flank-rank sweep found worst rank 2.  So the n=6 candidate is
rank <= 2.  That still feeds the proved chain: DoorThreeLargest requires
  |{d in ds : flank < d}| <= 2,
and a rank-2 flank has exactly 1 above it, so rank<=2 implies DoorThreeLargest implies
LonelyForSubject.  Same integer test as n=5, validated against the n=8 control.
"""
import math, sys, time
from itertools import combinations

def works_at(c, e, n):
    """Does flank e host a lonely opening for difference set c?"""
    M = n*e; lo, hi = e, (n-1)*e
    for j in range(e):
        a = n*j + 1
        ok = True
        for d in c:
            if not (lo <= (d*a) % M <= hi): ok = False; break
        if ok: return True
    return False

def best_rank(c, n):
    for r, e in enumerate(sorted(c, reverse=True), 1):
        if works_at(c, e, n): return r
    return 99

def count_working_top(c, n, top):
    """Working openings summed over the `top` largest flanks (cap at 2)."""
    cnt = 0
    for e in sorted(set(c), reverse=True)[:top]:
        M = n*e; lo, hi = e, (n-1)*e
        for j in range(e):
            a = n*j + 1
            if all(lo <= (d*a) % M <= hi for d in c):
                cnt += 1
                if cnt >= 2: return 2
    return cnt

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g, x)
    return g == 1

print("=== control: n=8 recorded refutation (2,3,5,7,8,13,16) ===")
print(f"   flank 16 works? {works_at((2,3,5,7,8,13,16), 16, 8)}  (record: False)")
print(f"   flank 13 works? {works_at((2,3,5,7,8,13,16), 13, 8)}  (record: True, lap 1)")
print(f"   best rank = {best_rank((2,3,5,7,8,13,16), 8)}  (record: 2)")
print()

HI = int(sys.argv[1]) if len(sys.argv) > 1 else 50
n, k = 6, 5
t0 = time.time()
tot = fail1 = fail2 = 0
tight = []
worst = 0
f2 = []
for c in combinations(range(1, HI+1), k):
    if not prim(c): continue
    tot += 1
    r = best_rank(c, n)
    if r > worst: worst = r
    if r >= 2: fail1 += 1          # largest alone fails
    if r >= 3:
        fail2 += 1                  # two largest both fail  <- would kill the candidate
        if len(f2) < 10: f2.append(c)
    w = count_working_top(c, n, 2)
    if w == 1: tight.append(c)
print(f"=== n=6 exhaustive primitive 5-subsets of [1,{HI}]  ({time.time()-t0:.1f}s) ===")
print(f"  sets                                  {tot}")
print(f"  worst best-rank                       {worst}")
print(f"  largest alone fails (rank>=2)         {fail1}")
print(f"  TWO largest both fail (rank>=3)       {fail2}   <- 0 means the candidate holds here")
if f2: print(f"     witnesses: {f2}")
print(f"  TIGHT (exactly 1 working opening across the two largest): {len(tight)}")
if tight:
    print(f"     max element among tight: {max(max(c) for c in tight)}")
    print(f"     tight sets: {tight[:40]}")
