"""modgap_width_v1 (2026-10-06): the component width as an integer.  Opener e (e t* = J + 1/8), closer f (f t_R = M + 7/8), N = J+M+1.
[P] m = N/(e+f); e(m - t*) = f(t_R - m) = h with h = Delta/(8(e+f)), Delta = 8(eM - fJ) + 7e - f.  So t_R - t* = Delta/(8 e f) when the
opener and closer are unique, and Delta = -(e+f) (mod 8).  Checked on every non-unit-fraction set of S1 (all opener/closer pairs): the identities
(W1) e (m - t*) = f (t_R - m), (W2) h = Delta/(8(e+f)), (W3) t_R - t* = Delta/(8ef), (W4) Delta = -(e+f) mod 8; and the distribution of
Delta mod 8 and of (e+f) mod 8 for D = 0 against D >= 1 sets.  Exact."""
import itertools, math, collections, sys
sys.path.insert(0, '.')
from fractions import Fraction as F
from math import gcd
from modgap_lib_v1 import cascade, openers, component, simplest, E8, E78
c = collections.Counter(); dm = collections.Counter(); em = collections.Counter(); bad = []
for r in itertools.combinations(range(2, 25), 6):
    S = (1,) + r; t = cascade(S); tR, cl = component(S, t)
    if t < 1 and F(1, math.ceil(1 / tR)) >= t: continue
    op = openers(S, t); sA = simplest(t, tR); best = None
    for e in op:
        for f in cl:
            J = int(e * t - E8); M = int(f * tR - E78); N = J + M + 1; m = F(N, e + f); h = e * (m - t)
            Dl = 8 * (e * M - f * J) + 7 * e - f
            c[('W1', e * (m - t) == f * (tR - m))] += 1; c[('W2', h == F(Dl, 8 * (e + f)))] += 1
            c[('W3 (single opener & closer)', (tR - t == F(Dl, 8 * e * f)) if len(op) == 1 and len(cl) == 1 else None)] += 1
            c[('W4', (Dl + e + f) % 8 == 0)] += 1
            g = gcd(N, e + f); Dr = abs(sA.numerator * ((e + f) // g) - sA.denominator * (N // g))
            if best is None or Dr < best[0]: best = (Dr, Dl, e, f)
    dm[(min(best[0], 2), best[1] % 8)] += 1; em[(min(best[0], 2), (best[2] + best[3]) % 8)] += 1
out = open('modgap_width_v1.out', 'w'); out.write(__doc__ + "\n")
for k, v in sorted(c.items(), key=str): out.write("%s: %d\n" % (k, v))
out.write("(D capped at 2, Delta mod 8): %s\n(D capped at 2, (e+f) mod 8): %s\n" % (dict(sorted(dm.items())), dict(sorted(em.items()))))
out.close(); print(open('modgap_width_v1.out').read()[len(__doc__):])
