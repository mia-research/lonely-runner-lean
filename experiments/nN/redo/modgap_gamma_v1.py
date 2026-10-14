"""modgap_gamma_v1 (2026-10-06): the lap-index relation of the opener and the closer.  Opener e at lap J (e t* = J + 1/8), closer f at lap M
(f t_R = M + 7/8).  J/e and M/f are the whole-lap positions of the two edges; Gamma = e M - f J is an integer (Farey determinant of J/e, M/f).
Delta = 8 Gamma + 7e - f (modgap_width_v1).  Recorded: the distribution of Gamma, the cross-tabulation of D (modgap_farey_v1: 0 mediant,
1 Farey parent, >=2 higher ancestor) against Gamma, and the sets where D >= 1 listed by (e, f, J, M, Gamma, a/q) for the individually
tight cases.  Populations: S1 (non-unit-fraction), T2, T3 (definitions as modgap_ancestor_v1).  Best (smallest-D) pair per set.  Exact."""
import itertools, math, collections, sys
sys.path.insert(0, '.')
from fractions import Fraction as F
from math import gcd
from functools import reduce
from modgap_lib_v1 import cascade, openers, component, simplest, E8, E78
def s1():
    for r in itertools.combinations(range(2, 25), 6): yield (1,) + r
def t2():
    for r in itertools.combinations(range(2, 29), 6):
        if r[-1] >= 25: yield (1,) + r
def t3():
    pools = {k: [d for d in range(1, 41) if d % 8 == k] for k in range(8)}
    for p in itertools.product(pools[0], pools[1], pools[2], pools[3], pools[5], pools[6], pools[7]):
        S = tuple(sorted(p))
        if reduce(gcd, S) == 1: yield S
out = open('modgap_gamma_v1.out', 'w'); out.write(__doc__ + "\n")
for name, gen in (('S1', s1()), ('T2', t2()), ('T3', t3())):
    tab = collections.Counter(); G = collections.Counter(); rows = []
    for S in gen:
        t = cascade(S); tR, cl = component(S, t)
        if t < 1 and F(1, math.ceil(1 / tR)) >= t: continue
        op = openers(S, t); sA = simplest(t, tR); best = None
        for e in op:
            for f in cl:
                J = int(e * t - E8); M = int(f * tR - E78); N = J + M + 1; g = gcd(N, e + f)
                Dr = abs(sA.numerator * ((e + f) // g) - sA.denominator * (N // g))
                if best is None or Dr < best[0]: best = (Dr, e, f, J, M, e * M - f * J)
        Dr, e, f, J, M, Gm = best
        tab[(min(Dr, 2), max(min(Gm, 6), -6))] += 1; G[max(min(Gm, 6), -6)] += 1
        if Dr >= 2 and len(rows) < 30: rows.append((S, e, f, J, M, Gm, str(sA)))
    out.write("\n==== %s: Gamma distribution %s\n" % (name, dict(sorted(G.items()))))
    for D in (0, 1, 2):
        out.write("  D=%s%s by Gamma: %s\n" % (D, '+' if D == 2 else '', {g: v for (d, g), v in sorted(tab.items()) if d == D}))
    out.write("  first sets with D>=2 (S, e, f, J, M, Gamma, a/q):\n")
    for rw in rows: out.write("    %s\n" % (rw,))
out.close(); print(open('modgap_gamma_v1.out').read()[len(__doc__):][:4500])
