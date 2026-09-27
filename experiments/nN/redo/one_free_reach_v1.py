"""E117: reach of the one-free rule (six readings share g >= 2, the seventh does not) on 7-subsets of [1, N],
among sets passing the arithmetic residual fields (odd, no common factor, 5|, 6|, 7|, 8| some reading,
spread > 7, cost >= 8, not_fast, no fast pair).  Exact integer arithmetic."""
import itertools, sys
from math import gcd
from functools import reduce
from collections import Counter
N = int(sys.argv[1]) if len(sys.argv) > 1 else 30
c = Counter(); ex = []
for T in itertools.combinations(range(1, N + 1), 7):
    if reduce(gcd, T) != 1: continue
    if not any(d % 2 for d in T): continue
    if not all(any(d % q == 0 for d in T) for q in (5, 6, 7, 8)): continue
    if T[-1] <= 7 * T[0]: continue
    if sum(max(2, gcd(d, 8)) for d in T if d % 8) < 8: continue
    if any(all(V > 7 * s for s in T if s != V) for V in T): continue
    if any(all(9 * x <= T[i] for x in T if x not in (T[i], T[j])) for i in range(7) for j in range(i + 1, 7)): continue
    c['arith-residual'] += 1
    hit = [(x, reduce(gcd, [d for d in T if d != x])) for x in T]
    hit = [(x, g) for x, g in hit if g >= 2 and x % g]
    if hit:
        c['one-free applies'] += 1
        c['g=%d' % hit[0][1]] += 1
        if len(ex) < 5: ex.append((T, hit[0]))
print("N =", N); [print("  ", k, v) for k, v in sorted(c.items())]; print("  e.g.", ex)
