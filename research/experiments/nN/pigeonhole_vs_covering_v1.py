"""Is the pigeonhole argument covering in disguise?

COVERING (manuscript 8.2): k in-the-way arcs, each of width 2/n on the TIME circle, cannot
cover it when k*(2/n) < 1, i.e. n > 2k.  On the diagonal k = n-1 this needs n > 2n-2, i.e. n < 2
-- it reaches NO order.

PIGEONHOLE (here): each non-flank disparity forbids EXACTLY ONE k in {1,...,n-1}, because for d
coprime to n the map k -> d*k mod n is a bijection.  With n-2 non-flank disparities and n-1
candidates, one survives.  On the diagonal that is n-2 <= n-2 -- it reaches EVERY prime order.

Different thresholds, so not the same argument.  But the pigeonhole is TIGHT on the diagonal,
so measure the actual slack: how many good k are there?
"""
import math
from itertools import combinations
from collections import Counter

def good_ks(c, n):
    e = c[-1]
    return [k for k in range(1, n) if all((d*k) % n not in (0, n-1) for d in c[:-1])]

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

print("=== the two thresholds, on the diagonal (subject at order n) ===")
print(f"{'n':>3} {'disparities':>12} {'covering needs n >':>19} {'reached?':>9} "
      f"{'pigeonhole needs #nonflank <=':>30} {'reached?':>9}")
for n in (5,6,7,8,9,11,13):
    k = n - 1
    print(f"{n:>3} {k:>12} {2*k:>19} {str(n > 2*k):>9} {n-2:>30} {str(n-2 <= n-2):>9}")
print()
print("=== how much slack does the pigeonhole actually have? (Case II, 5 | e, no inner mult) ===")
for n, hi in ((5, 60), (7, 30), (11, 24)):
    cnt = Counter(); tot = 0
    for c in combinations(range(1, hi+1), n-1):
        if not prim(c): continue
        e = c[-1]
        if e % n: continue
        if any(d % n == 0 for d in c[:-1]): continue
        tot += 1
        cnt[len(good_ks(c, n))] += 1
    if tot:
        print(f"   n={n:>2}: {tot:>7} sets   #good k distribution {dict(sorted(cnt.items()))}"
              f"   (candidates: {n-1}, disparities: {n-2})")
print()
print("=== is the bad set ever actually full size?  (all n-2 disparities forbidding DISTINCT k) ===")
for n, hi in ((5, 60), (7, 30)):
    full = tot = 0
    for c in combinations(range(1, hi+1), n-1):
        if not prim(c): continue
        e = c[-1]
        if e % n or any(d % n == 0 for d in c[:-1]): continue
        tot += 1
        bad = {(pow(d, -1, n) * (n-1)) % n for d in c[:-1]}
        if len(bad) == n - 2: full += 1
    print(f"   n={n:>2}: {full} of {tot} sets have all {n-2} forbidden k distinct"
          f"  -> exactly {1} good k remains in those")
