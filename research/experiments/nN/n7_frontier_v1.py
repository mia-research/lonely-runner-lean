"""Order 7: size and shape of the residual frontier.

7 is prime, so Resonant 7 d  <=>  7 | d  (resonant_iff_dvd_of_prime, PROVED).
And no disparity divisible by 7  =>  lonely at 1/7  (lonelyAt_inv_of_no_resonance, PROVED).
So the ENTIRE residual problem at order 7 is: subjects with at least one disparity divisible by 7.

A subject at order 7 has at most 6 disparities, so card 6 is the diagonal.
Measured: how big is the residual class, how much of it fails the largest flank, and does the
failure set have structure (how many 7-multiples, is the multiple the largest, etc).
"""
import math
from itertools import combinations
from collections import Counter

def works_at(c, e, n=7):
    M = n*e; lo, hi = e, (n-1)*e
    return any(all(lo <= (d*(n*j+1)) % M <= hi for d in c) for j in range(e))

def best_rank(c, n=7):
    for r, e in enumerate(sorted(set(c), reverse=True), 1):
        if works_at(c, e, n): return r
    return 99

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

for card, hi in ((5, 20), (6, 16), (6, 18)):
    sets = [c for c in combinations(range(1, hi+1), card) if prim(c)]
    res = [c for c in sets if any(d % 7 == 0 for d in c)]
    clean = len(sets) - len(res)
    fails = [c for c in res if not works_at(c, c[-1])]
    print(f"=== card {card}, primitive subsets of [1,{hi}]: {len(sets)} ===")
    print(f"   non-resonant (no multiple of 7): {clean:>7}   PROVED lonely at 1/7")
    print(f"   resonant (some multiple of 7)  : {len(res):>7}   ({100*len(res)/len(sets):.1f}%)  <- the frontier")
    print(f"   of those, largest flank fails  : {len(fails):>7}   ({100*len(fails)/len(res):.2f}% of the frontier,"
          f" {100*len(fails)/len(sets):.3f}% of all)")
    if fails:
        nm = Counter(sum(1 for d in c if d % 7 == 0) for c in fails)
        ismax = Counter(c[-1] % 7 == 0 for c in fails)
        ranks = Counter(best_rank(c) for c in fails)
        print(f"   # of 7-multiples in a failing set : {dict(sorted(nm.items()))}")
        print(f"   is the largest disparity a multiple of 7? {dict(ismax)}")
        print(f"   best working flank rank for failures    : {dict(sorted(ranks.items()))}")
        print(f"   examples: {fails[:5]}")
    print()
