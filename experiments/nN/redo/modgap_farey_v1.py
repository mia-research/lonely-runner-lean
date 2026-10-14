"""modgap_farey_v1 (2026-10-06): the near-mirror finding of modgap_mod8_v1 as an exact identity, and its distribution.
Opener e (e t* = J + 1/8), closer f (f t_R = M + 7/8), N = J + M + 1, mediant m = N/(e+f).  Landing rational a/q (least denominator in [t*, t_R]);
d1 = a/q - t*, d2 = t_R - a/q (both >= 0).  At a/q the opener sits at x_e = 1/8 + e d1 and the closer at x_f = 7/8 - f d2 (no lap inside the component).
  ID1 [P]  s := (e+f) a - N q = q (e d1 - f d2)  (an integer)   [x_e + x_f - 1 = e d1 - f d2, and (e+f)a - Nq = q((e+f)a/q - N)
           with (e + f) t* + ... : e t* = J + 1/8, f t_R = M + 7/8 give e d1 - f d2 = (e+f) a/q - (J+1/8) - (M+7/8) - ... ] checked below.
  ID2 [P]  a/q - m = s / (q (e+f)).  s = 0 iff a/q = m (the mediant case RM).  With g = gcd(N, e+f), D = |a (e+f)/g - q N/g|:
           D = 1 means a/q and the reduced mediant are Farey neighbours.
Recorded for every non-unit-fraction set of S1 = {1} + 6-subsets of [2,24], every opener/closer pair: ID1 check, and the distribution of
D (reduced) and |s|.  Exact."""
import itertools, math, collections, sys
sys.path.insert(0, '.')
from fractions import Fraction as F
from math import gcd
from modgap_lib_v1 import cascade, openers, component, simplest, E8, E78
c = collections.Counter(); D = collections.Counter(); Ds = collections.Counter(); ex = []
for r in itertools.combinations(range(2, 25), 6):
    S = (1,) + r; t = cascade(S); tR, cl = component(S, t)
    if t < 1 and F(1, math.ceil(1 / tR)) >= t: continue
    op = openers(S, t); sA = simplest(t, tR); a, q = sA.numerator, sA.denominator
    d1 = sA - t; d2 = tR - sA
    best = None
    for e in op:
        for f in cl:
            J = int(e * t - E8); M = int(f * tR - E78); N = J + M + 1
            s = (e + f) * a - N * q
            c[('ID1 s = q(e d1 - f d2)', s == q * (e * d1 - f * d2))] += 1
            g = gcd(N, e + f); Dr = abs(a * ((e + f) // g) - q * (N // g))
            c[('ID2 a/q - m = s/(q(e+f))', sA - F(N, e + f) == F(s, q * (e + f)))] += 1
            if best is None or Dr < best[0]: best = (Dr, abs(s), e, f, N, g)
    D[min(best[0], 6)] += 1; Ds[min(best[1], 6)] += 1
    if best[0] >= 2 and len(ex) < 15: ex.append((S, t, tR, sA, best))
out = open('modgap_farey_v1.out', 'w'); out.write(__doc__ + "\n")
for k, v in sorted(c.items(), key=str): out.write("%s: [T %d/%d]\n" % (k, v, v) if k[1] else "%s: FAIL %d\n" % (k, v))
out.write("sets: %d.  Over the best (opener, closer) pair per set:\n  reduced D = |a(e+f)/g - qN/g| (6 = 6 or more): %s\n  |s| = |(e+f)a - Nq| (6 = 6 or more): %s\n" % (sum(D.values()), dict(sorted(D.items())), dict(sorted(Ds.items()))))
out.write("sets with D >= 2 (first 15): (S, t*, t_R, a/q, (D, |s|, e, f, N, g))\n")
for e in ex: out.write("  %s\n" % (e,))
out.close(); print(open('modgap_farey_v1.out').read()[len(__doc__):])
