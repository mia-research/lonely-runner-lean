"""modgap_ancestor_v1 (2026-10-06): prediction on arrangements not used to build it (rule 10).  [P] the least-denominator rational a/q of
[t*, t_R] is a Stern-Brocot ancestor of the opener-closer mediant m = N/(e+f) (m is in the interval, P4 of modgap_map_v1).  Prediction:
walk up the Stern-Brocot path of m from m and stop at the first ancestor lying in [t*, t_R]; that ancestor's SIMPLEST one (the least
denominator) equals a/q; D = 0 iff m has no ancestor in the interval; k = steps from m to a/q on the path.  Tested on T2 = 7-subsets of
[1,28] containing 1 with d_max >= 25, and T3 = 7-subsets of [1,40] with residues mod 8 exactly {0,1,2,3,5,6,7}, gcd 1 (as modgap_rule_v1),
over the non-unit-fraction sets, using the best (smallest-D) opener/closer pair.  Exact."""
import itertools, math, collections, sys
sys.path.insert(0, '.')
from fractions import Fraction as F
from math import gcd
from functools import reduce
from modgap_lib_v1 import cascade, openers, component, simplest, E8, E78
def sb_ancestors(x):
    """Stern-Brocot ancestors of x = p/q from the root 1/1 down to x, as Fractions (with 0/1 and 1/0 as bounds, excluded)."""
    lo = (0, 1); hi = (1, 0); out = []
    while True:
        m = (lo[0] + hi[0], lo[1] + hi[1]); f = F(m[0], m[1]); out.append(f)
        if f == x: return out
        if x < f: hi = m
        else: lo = m
def t2():
    for r in itertools.combinations(range(2, 29), 6):
        if r[-1] >= 25: yield (1,) + r
def t3():
    pools = {k: [d for d in range(1, 41) if d % 8 == k] for k in range(8)}
    for p in itertools.product(pools[0], pools[1], pools[2], pools[3], pools[5], pools[6], pools[7]):
        S = tuple(sorted(p))
        if reduce(gcd, S) == 1: yield S
out = open('modgap_ancestor_v1.out', 'w'); out.write(__doc__ + "\n")
for name, gen in (('T2', t2()), ('T3', t3())):
    c = collections.Counter(); K = collections.Counter(); bad = []
    for S in gen:
        t = cascade(S); tR, cl = component(S, t)
        if t < 1 and F(1, math.ceil(1 / tR)) >= t: continue
        op = openers(S, t); sA = simplest(t, tR)
        best = None
        for e in op:
            for f in cl:
                N = int(e * t - E8) + int(f * tR - E78) + 1; g = gcd(N, e + f); m = F(N, e + f)
                Dr = abs(sA.numerator * ((e + f) // g) - sA.denominator * (N // g))
                if best is None or Dr < best[0]: best = (Dr, m)
        D, m = best
        anc = sb_ancestors(m)
        inside = [x for x in anc if t <= x <= tR]
        pred = min(inside, key=lambda x: x.denominator)
        ok = (pred == sA); c[('prediction a/q = least-denominator ancestor of m in [t*, t_R]', ok)] += 1
        c[('m in [t*, t_R]', t <= m <= tR)] += 1
        k = len(anc) - 1 - anc.index(sA) if sA in anc else None
        c[('a/q on the SB path of m', sA in anc)] += 1
        K[(min(D, 4), min(k, 6) if k is not None else None)] += 1
        if not ok and len(bad) < 5: bad.append((S, t, tR, m, sA, pred))
    out.write("\n==== %s\n" % name)
    for k_, v in sorted(c.items(), key=str): out.write("  %s: %d\n" % (k_, v))
    out.write("  (D capped at 4, steps k up the path from m, capped at 6): %s\n" % dict(sorted(K.items(), key=str)))
    for b in bad: out.write("  FAIL %s\n" % (b,))
out.close(); print(open('modgap_ancestor_v1.out').read()[len(__doc__):])
