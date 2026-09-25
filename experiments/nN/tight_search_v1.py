"""Tight configurations at order eight: lonely at 1/8, but only at isolated instants (no interval).

Exhaustive over primitive 7-subsets of [1,B], exact fractions.  The lonely set on (0,1) is the
complement of the open blocked zones ((k - 1/8)/d, (k + 1/8)/d); touching zones leave their shared
endpoint clear (BSM: never merge touching zones).  Tight = the lonely set is nonempty and every
component is a single point.  Also reports the sets that are NOT lonely at all (there should be none).
"""
import sys, time
from fractions import Fraction as F
from itertools import combinations
from math import gcd
from functools import reduce
B = int(sys.argv[1]) if len(sys.argv) > 1 else 20
def components(S):
    z = sorted((F(8 * k - 1, 8 * d), F(8 * k + 1, 8 * d)) for d in S for k in range(0, d + 1))
    comps = []; cur = F(0)
    for a, b in z:
        if a > cur: comps.append((cur, a))
        elif a == cur and cur > 0: comps.append((cur, cur))
        cur = max(cur, b)
    return [(a, b) for a, b in comps if 0 < a and b < 1]
t0 = time.time(); tight = []; never = []; n = 0
for S in combinations(range(1, B + 1), 7):
    if reduce(gcd, S) != 1: continue
    n += 1
    c = components(S)
    if not c: never.append(S)
    elif all(a == b for a, b in c): tight.append((S, sorted({a for a, _ in c})))
print(f"primitive 7-subsets of [1,{B}]: {n};  not lonely at all: {len(never)} {never[:3]};  tight: {len(tight)}  ({time.time() - t0:.0f}s)")
for S, pts in tight: print(f"  {S}: isolated lonely instants in (0,1): {[str(p) for p in pts]}")
