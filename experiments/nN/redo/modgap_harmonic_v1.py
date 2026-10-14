"""modgap_harmonic_v1 (2026-10-06): the sets whose landing rational a/q is not the opener-closer mediant (D >= 1 in modgap_farey_v1),
tested for a mirror pair of OTHER readings at a/q (a finer harmonic).  Exact.
Population: non-unit-fraction sets of S1 = {1} + 6-subsets of [2,24].  Per set at a/q, r_d = a d mod q, margin_d = min(r_d, q - r_d)/q - 1/8
(>= 0 at a lonely instant).  Mirror pair (d1, d2): r_d1 + r_d2 = 0 mod q (d1 = d2 allowed when 2 r = q).  For each D >= 1 set record:
  - the mirror pairs, whether the opener/closer are in one, the rank of each pair's readings by margin (0 = tightest),
  - the pair's own mediant: N' = (r_d1 + r_d2 + ... ) i.e. a/q = N'/(d1 + d2) reduced?  (always, by the mirror: (d1+d2) a = 0 mod q)
  - the margins (as exact fractions) of the opener, the closer, and of the paired readings.
Counts by D.  Examples individually."""
import itertools, math, collections, sys
sys.path.insert(0, '.')
from fractions import Fraction as F
from math import gcd
from modgap_lib_v1 import cascade, openers, component, simplest, positions, E8, E78
cnt = collections.Counter(); ex = collections.defaultdict(list)
for r in itertools.combinations(range(2, 25), 6):
    S = (1,) + r; t = cascade(S); tR, cl = component(S, t)
    if t < 1 and F(1, math.ceil(1 / tR)) >= t: continue
    op = openers(S, t); sA = simplest(t, tR); a, q = sA.numerator, sA.denominator
    best = None
    for e in op:
        for f in cl:
            N = int(e * t - E8) + int(f * tR - E78) + 1; g = gcd(N, e + f)
            Dr = abs(a * ((e + f) // g) - q * (N // g))
            if best is None or Dr < best: best = Dr
    if best == 0: continue
    pos = positions(S, a, q)
    mar = {d: F(min(pos[d], q - pos[d]), q) - E8 for d in S}
    order = sorted(S, key=lambda d: (mar[d], d))
    rank = {d: i for i, d in enumerate(order)}
    pairs = [(x, y) for x, y in itertools.combinations(S, 2) if (pos[x] + pos[y]) % q == 0] + [(x, x) for x in S if 2 * pos[x] == q]
    Dk = min(best, 3)
    cnt[(Dk, 'sets')] += 1
    if not pairs:
        cnt[(Dk, 'no mirror pair')] += 1; key = 'none'
    else:
        inv = [p for p in pairs if (p[0] in op or p[0] in cl) and (p[1] in op or p[1] in cl)]
        cnt[(Dk, 'mirror pair = {opener, closer}')] += bool(inv)
        cnt[(Dk, 'mirror pair other than {opener, closer}')] += (len(inv) < len(pairs))
        cnt[(Dk, 'some mirror pair uses the tightest or 2nd tightest reading')] += any(rank[p[0]] < 2 or rank[p[1]] < 2 for p in pairs)
        cnt[(Dk, 'some mirror pair has both readings in the 3 tightest')] += any(rank[p[0]] < 3 and rank[p[1]] < 3 for p in pairs)
        key = 'pair'
    if len(ex[(Dk, key)]) < 8:
        ex[(Dk, key)].append((S, str(t), str(tR), str(sA), 'op', op, 'cl', cl, 'pairs', pairs, 'margins', {d: str(mar[d]) for d in order}))
out = open('modgap_harmonic_v1.out', 'w'); out.write(__doc__ + "\n")
for k, v in sorted(cnt.items(), key=str): out.write("D=%s %s: %d\n" % (k[0] if k[0] < 3 else '>=3', k[1], v))
for k, v in sorted(ex.items(), key=str):
    out.write("\nexamples D=%s %s:\n" % k)
    for e in v: out.write("  %s\n" % (e,))
out.close(); print(open('modgap_harmonic_v1.out').read()[len(__doc__):][:6000])
