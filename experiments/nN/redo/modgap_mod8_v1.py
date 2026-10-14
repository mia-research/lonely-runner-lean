"""modgap_mod8_v1 (2026-10-06): owner's reading: the mirror pair falls short; look for a resonance with n = 8.  Exact.
Population: every non-unit-fraction set of S1 = {1} + 6-subsets of [2,24] (23,797).  G = sets with a mirror pair at a_A/q_A (RG),
X = sets without (the RG exceptions, 945).  Per set at a_A/q_A, with r_d = a d mod q, opener e, closer f (any pair of them):
  s  = (r_e + r_f) mod q, centred to (-q/2, q/2]  (0 = exact mirror of opener and closer)
  q mod 8, gcd(q, 8)
  u_d = (8 r_d) mod q  (the position in units of 1/8, mod q): is any u_d = 0 (a reading at an exact multiple of 1/8)?  min |u_d|.
Counts by class, G against X.
"""
import itertools, math, collections, sys
sys.path.insert(0, '.')
from fractions import Fraction as F
from math import gcd
from modgap_lib_v1 import cascade, openers, component, simplest, positions
cG = collections.Counter(); cX = collections.Counter(); nG = nX = 0
sG = collections.Counter(); sX = collections.Counter()
for r in itertools.combinations(range(2, 25), 6):
    S = (1,) + r; t = cascade(S); tR, cl = component(S, t)
    if t < 1 and F(1, math.ceil(1 / tR)) >= t: continue
    op = openers(S, t); sA = simplest(t, tR); a, q = sA.numerator, sA.denominator
    pos = positions(S, a, q)
    mir = any((pos[x] + pos[y]) % q == 0 for x, y in itertools.combinations(S, 2)) or any(2 * pos[x] == q for x in S)
    s = (pos[op[0]] + pos[cl[0]]) % q
    if s > q // 2: s -= q
    u = [8 * pos[d] % q for d in S]
    feat = dict(qmod8=q % 8, g8=gcd(q, 8), s=s, u0=any(x == 0 for x in u), umin=min(min(x, q - x) for x in u), sabs=min(abs(s), 5))
    C, SS = (cG, sG) if mir else (cX, sX)
    if mir: nG += 1
    else: nX += 1
    for k in ('qmod8', 'g8', 'u0', 'sabs'): C[(k, feat[k])] += 1
out = open('modgap_mod8_v1.out', 'w'); out.write(__doc__ + "\n")
out.write("G (mirror pair at a_A/q_A): %d sets; X (none): %d sets\n" % (nG, nX))
for k in ('qmod8', 'g8', 'u0', 'sabs'):
    vals = sorted({v for kk, v in list(cG) + list(cX) if kk == k}, key=str)
    out.write("%s:  " % k + "  ".join("%s: G %d (%s) X %d (%s)" % (v, cG[(k, v)], "%.3f" % (cG[(k, v)] / nG), cX[(k, v)], "%.3f" % (cX[(k, v)] / nX)) for v in vals) + "\n")
out.write("(shares printed as decimals for display only; counts are exact)\n")
out.close(); print(open('modgap_mod8_v1.out').read()[len(__doc__):])
