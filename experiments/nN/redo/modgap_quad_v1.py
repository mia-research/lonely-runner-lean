"""modgap_quad_v1 (2026-10-06): the landing rational is a function of the quadruple Q = (e, J, f, M) (interval [(8J+1)/(8e), (8M+7)/(8f)] for a
unique opener and closer).  Counts, per population (S1, T2, T3, non-unit-fraction, single opener and single closer), of distinct quadruples
by D, and the number of sets per quadruple; D of a quadruple is a function of Q alone: checked that no quadruple appears with two D values.
Then, over the D>=2 quadruples: the Stern-Brocot ancestor chain of the mediant and where a/q sits, listed individually for the 40 most
frequent quadruples.  Exact."""
import itertools, math, collections, sys
sys.path.insert(0, '.')
from fractions import Fraction as F
from math import gcd
from functools import reduce
from modgap_lib_v1 import cascade, openers, component, simplest, E8, E78
def sb_ancestors(x):
    lo = (0, 1); hi = (1, 0); out = []
    while True:
        m = (lo[0] + hi[0], lo[1] + hi[1]); f = F(m[0], m[1]); out.append(f)
        if f == x: return out
        if x < f: hi = m
        else: lo = m
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

out = open('modgap_quad_v1.out', 'w'); out.write(__doc__ + "\n")
allQ = {}
for name, gen in (('S1', s1()), ('T2', t2()), ('T3', t3())):
    Q = collections.defaultdict(lambda: [None, 0, None]); multi = 0; nsets = collections.Counter()
    for S in gen:
        t = cascade(S); tR, cl = component(S, t)
        if t < 1 and F(1, math.ceil(1 / tR)) >= t: continue
        op = openers(S, t)
        if len(op) != 1 or len(cl) != 1: multi += 1; continue
        e, f = op[0], cl[0]; J = int(e * t - E8); M = int(f * tR - E78); N = J + M + 1; g = gcd(N, e + f)
        sA = simplest(t, tR); D = abs(sA.numerator * ((e + f) // g) - sA.denominator * (N // g))
        key = (e, J, f, M)
        if Q[key][0] is not None and Q[key][0] != (D, sA): out.write("CONFLICT %s %s %s\n" % (key, Q[key][0], (D, sA)))
        Q[key][0] = (D, sA); Q[key][1] += 1; Q[key][2] = F(N, e + f)
        nsets[min(D, 2)] += 1
    byD = collections.Counter(min(v[0][0], 2) for v in Q.values())
    out.write("\n==== %s: sets with unique opener and closer by D: %s (multi-opener/closer sets skipped: %d)\n" % (name, dict(sorted(nsets.items())), multi))
    out.write("  distinct quadruples by D (2 = 2 or more): %s; total %d\n" % (dict(sorted(byD.items())), len(Q)))
    allQ[name] = Q
    top = sorted(((v[1], k, v[0], v[2]) for k, v in Q.items() if v[0][0] >= 2), reverse=True)[:40]
    out.write("  D>=2 quadruples, most frequent first: (sets, (e,J,f,M), (D, a/q), mediant m, SB ancestors of m from m up to a/q)\n")
    for n, k, (D, sA), m in top:
        anc = sb_ancestors(m); up = [str(x) for x in reversed(anc[anc.index(sA):])] if sA in anc else None
        out.write("    %d %s D=%d a/q=%s m=%s chain=%s\n" % (n, k, D, sA, m, up))
out.close(); print(open('modgap_quad_v1.out').read()[len(__doc__):][:5200])
