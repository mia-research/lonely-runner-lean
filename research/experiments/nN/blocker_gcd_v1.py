"""Does a blocker's gcd with the flank drive the failures?

Theory: with g = gcd(d,e), the readings d*(n j+1)/(n e) as j varies live on a lattice of
spacing g/e, i.e. only e/g DISTINCT readings, each hit g times.  The bad region has width 2/n,
so the expected blocked count is 2e/n -- but on a COARSE lattice (g large, e/g small) the
count is a rounding of (2/n)*(e/g) points times g, which can be far above 2e/n.

So a blocker's damage is  (#lattice points in the bad region) * g,  and coarse lattices
over-block.  Tested per blocker, failures vs successes.
"""
import math
from itertools import combinations
from collections import Counter

def blocked_count(d, e, n):
    M = n*e
    return sum(1 for j in range(e) if not (e <= (d*(n*j+1)) % M <= (n-1)*e))

def works(c, n):
    e = c[-1]; M = n*e
    return any(all(e <= (d*(n*j+1)) % M <= (n-1)*e for d in c) for j in range(e))

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

print("=== lattice prediction check: blocked count vs g*ceil-ish, per blocker ===")
for c, n in [((1,2,3,5,6),6), ((2,3,5,7,8,13,16),8), ((1,13,15,28),5)]:
    e = c[-1]
    print(f"  ds={c} n={n} e={e}   avg prediction 2e/n = {2*e/n:.2f}")
    for d in c[:-1]:
        g = math.gcd(d,e); pts = e//g
        bc = blocked_count(d,e,n)
        print(f"    d={d:>3} g={g:>3} lattice points e/g={pts:>3}  blocked={bc:>3}  blocked/g={bc//g if g else 0:>3}  excess over 2e/n: {bc-2*e/n:+.2f}")
    print()

print("=== across all sets: does failure require a coarse-lattice blocker? ===")
print(f"{'n':>3} {'range':>8} {'outcome':>9} {'sets':>8}  max over blockers of g=gcd(d,e)   max of (blocked*n)/(2e)")
for n, hi in [(5,40),(6,26),(7,20),(8,16)]:
    k = n-1
    for label in ("fail","work"):
        mg, mr, cnt = Counter(), 0.0, 0
        worst = None
        for c in combinations(range(1,hi+1), k):
            if not prim(c): continue
            w = works(c, n)
            if (label=="fail") != (not w): continue
            cnt += 1
            e = c[-1]
            gm = max(math.gcd(d,e) for d in c[:-1])
            rm = max(blocked_count(d,e,n)*n/(2*e) for d in c[:-1])
            mg[gm] += 1
            if rm > mr: mr, worst = rm, c
        if cnt == 0: continue
        top = dict(sorted(mg.items(), key=lambda p:-p[0])[:4])
        print(f"{n:>3} {('[1,'+str(hi)+']'):>8} {label:>9} {cnt:>8}  g-distribution(top): {top}   max ratio {mr:.2f} at {worst}")
    print()
