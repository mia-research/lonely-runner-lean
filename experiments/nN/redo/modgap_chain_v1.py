"""modgap_chain_v1 (2026-10-06): rule success against the cascade's chain length.  Population: every non-unit-fraction set of
S1 = {1} + 6-subsets of [2,24] (23,797 sets; the 'not U' sets of modgap_rule_v1.out).  Per set: n = number of distinct setters
in the cascade path (P), number of cascade moves; rules RM (mediant of an opener and a closer), RG (a mirror pair at a_A/q_A).
Exact.  Counts only; [OBS]."""
import itertools, math, collections, sys
sys.path.insert(0, '.')
from fractions import Fraction as F
from modgap_lib_v1 import cascade, cascade_path, openers, component, simplest, positions, E8, E78
c = collections.Counter(); tot = collections.Counter()
for r in itertools.combinations(range(2, 25), 6):
    S = (1,) + r
    path = cascade_path(S); t = path[-1][0]
    tR, cl = component(S, t)
    if t < 1 and F(1, math.ceil(1 / tR)) >= t: continue
    op = openers(S, t); sA = simplest(t, tR); a, q = sA.numerator, sA.denominator
    meds = {F(int(e * t - E8) + int(f * tR - E78) + 1, e + f) for e in op for f in cl}
    pos = positions(S, a, q)
    mir = any((pos[x] + pos[y]) % q == 0 for x, y in itertools.combinations(S, 2)) or any(2 * pos[x] == q for x in S)
    n = len({d for _, d in path if d}); mv = len(path) - 1
    k = min(n, 5)
    tot[k] += 1; c[(k, 'RM')] += sA in meds; c[(k, 'RG')] += mir
    tot[('mv', min(mv, 6))] += 1; c[(('mv', min(mv, 6)), 'RM')] += sA in meds; c[(('mv', min(mv, 6)), 'RG')] += mir
out = open('modgap_chain_v1.out', 'w'); out.write(__doc__ + "\n")
for k in sorted(tot, key=str):
    out.write("%-10s sets %6d   RM %6d (%s)   RG %6d (%s)\n" % (k, tot[k], c[(k, 'RM')], F(c[(k,'RM')], tot[k]) and "%d/%d" % (c[(k,'RM')], tot[k]), c[(k, 'RG')], "%d/%d" % (c[(k,'RG')], tot[k])))
out.close(); print(open('modgap_chain_v1.out').read()[len(__doc__):])
