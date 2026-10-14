"""Two candidate mechanisms, separated.

(A) resonance with the ORDER:  gcd(d, n) > 1.  Measured: every failure has one, at every order.
(B) resonance with the FLANK:  gcd(d, e) large -> readings on a coarse lattice of e/g points
    -> over-blocking.  The trace shows these: 7 blocks 7 of 14 openings when e = 14.

Are they the same phenomenon?  Test: among sets that are NON-resonant with n, does a large
gcd(d, e) still cause failure?  If never, (A) is doing real work beyond (B).
"""
import math
from itertools import combinations
from collections import Counter

def works_at(c, e, n=7):
    M = n*e; lo, hi = e, (n-1)*e
    return any(all(lo <= (d*(n*j+1)) % M <= hi for d in c) for j in range(e))

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

n, card, hi = 7, 6, 20
sets = [c for c in combinations(range(1, hi+1), card) if prim(c)]
print(f"order {n}, card {card}, [1,{hi}]: {len(sets)} primitive sets\n")

# split by (A) n-resonance and (B) max gcd(d,e)
buckets = {}
for c in sets:
    e = c[-1]
    A = any(math.gcd(d, n) > 1 for d in c)
    B = max(math.gcd(d, e) for d in c[:-1])
    bad = not works_at(c, e)
    key = (A, B >= 3)
    t, f = buckets.get(key, (0, 0))
    buckets[key] = (t + 1, f + bad)

print(f"{'n-resonant?':>12} {'gcd(d,e)>=3?':>13} {'sets':>8} {'failures':>9} {'rate':>9}")
for key in sorted(buckets):
    t, f = buckets[key]
    print(f"{str(key[0]):>12} {str(key[1]):>13} {t:>8} {f:>9} {f/t if t else 0:>9.5f}")
print()
print("=== among NON-n-resonant sets, the distribution of max gcd(d,e) and any failures ===")
dist = Counter(); fails = Counter()
for c in sets:
    if any(math.gcd(d, n) > 1 for d in c): continue
    e = c[-1]; g = max(math.gcd(d, e) for d in c[:-1])
    dist[g] += 1
    if not works_at(c, e): fails[g] += 1
for g in sorted(dist):
    print(f"   max gcd(d,e) = {g:>3}:  {dist[g]:>6} sets, {fails[g]:>3} failures")
print()
print("=== and among n-RESONANT sets, same breakdown ===")
dist2 = Counter(); fails2 = Counter()
for c in sets:
    if not any(math.gcd(d, n) > 1 for d in c): continue
    e = c[-1]; g = max(math.gcd(d, e) for d in c[:-1])
    dist2[g] += 1
    if not works_at(c, e): fails2[g] += 1
for g in sorted(dist2):
    print(f"   max gcd(d,e) = {g:>3}:  {dist2[g]:>6} sets, {fails2[g]:>3} failures")
