"""
Tight-instance enumeration for general n.  Exact rational arithmetic (Fraction).

For T a set of n-1 distinct positive integers with gcd 1,
   M(T) := max_t min_{v in T} ||v t||.
LRC(n) asserts M(T) >= 1/n.   TIGHT means M(T) = 1/n exactly.

Tightness test: M(T) > 1/n  <=>  the OPEN bad set
   U = union over v,k of ( k/v - 1/(n v),  k/v + 1/(n v) )
leaves a positive-length gap in [0,1].  Two bad intervals meeting at a point leave
that point uncovered -- that is exactly the tight case, and it is why the Lebesgue
"good fraction" is the wrong functional for tight instances.

Ladder prefilter [PROVED, docs/n8/N11_TRANSLATION_v1.md sec 3]: if q in {2..n-1}
divides no element of T then t = 1/q gives ||v t|| >= 1/q > 1/n for all v, so T is
not tight.  Hence a tight T contains a multiple of every q in {2..n-1}; only the
maximal such q need be tested (those q not dividing a larger q' <= n-1).
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
import sys

def maximal_levels(n):
    qs = list(range(2, n))
    return [q for q in qs if not any(q2 % q == 0 and q2 != q for q2 in qs)]

def gaps_of(T, n):
    iv = []
    for v in T:
        w = F(1, n*v)
        for k in range(0, v+1):
            lo, hi = F(k,v)-w, F(k,v)+w
            if hi <= 0 or lo >= 1: continue
            iv.append((max(lo,F(0)), min(hi,F(1))))
    iv.sort()
    out, cur = [], F(0)
    for lo, hi in iv:
        if lo > cur: out.append((cur,lo))
        if hi > cur: cur = hi
    if cur < 1: out.append((cur,F(1)))
    return out

def main(n, V):
    levels = maximal_levels(n)
    print(f"n = {n}, speeds <= {V}, {n-1} speeds; ladder levels tested: {levels}", flush=True)
    tight, ncand = [], 0
    for T in combinations(range(1, V+1), n-1):
        ok = True
        for q in levels:
            if not any(v % q == 0 for v in T): ok = False; break
        if not ok: continue
        g = 0
        for v in T: g = gcd(g, v)
        if g != 1: continue
        ncand += 1
        if not gaps_of(T, n):
            tight.append(T); print("  TIGHT", T, flush=True)
    print(f"{ncand} candidates past filter; {len(tight)} tight instances")
    return tight

if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]))
