"""modgap_cofactor_v1 (2026-10-06): common cofactors.  (A) g = gcd(e, f) of the opener and closer against the base rate gcd(d_i, d_j) > 1 over all
pairs of the same set, and against D (modgap_farey_v1) and the mediant reduction gcd(N, e+f).  (B) common factors between the opener and the
other readings: the number of readings sharing a factor > 1 with the opener, against the same number for a random reading of the set.
(C) the readings sharing a factor with the opener, as a subset: does its own cascade equal t*  (the shared-factor subset carries the landing)?
Populations: S1 (non-unit-fraction, unique opener and closer), T2, T3 (definitions as modgap_ancestor_v1).  Exact.
[PROVISIONAL: counting tool; supports: the base-rate comparison]"""
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
out = open('modgap_cofactor_v1.out', 'w'); out.write(__doc__ + "\n")
for name, gen in (('S1', s1()), ('T2', t2()), ('T3', t3())):
    c = collections.Counter(); byD = collections.Counter(); n = 0; pair_tot = pair_cf = 0; opshare = 0; opn = 0
    for S in gen:
        t = cascade(S); tR, cl = component(S, t)
        if t < 1 and F(1, math.ceil(1 / tR)) >= t: continue
        op = openers(S, t)
        if len(op) != 1 or len(cl) != 1: continue
        e, f = op[0], cl[0]; n += 1
        sA = simplest(t, tR); N = int(e * t - E8) + int(f * tR - E78) + 1; g = gcd(N, e + f)
        D = abs(sA.numerator * ((e + f) // g) - sA.denominator * (N // g))
        ge = gcd(e, f)
        c[('gcd(e,f) > 1', ge > 1)] += 1
        byD[(min(D, 2), ge > 1)] += 1
        c[('gcd(N, e+f) > 1 (mediant reduces)', g > 1)] += 1
        c[('gcd(e,f)>1 implies gcd(N,e+f)>1', (ge > 1) <= (g > 1))] += 1 if ge > 1 else 0
        for i, j in itertools.combinations(range(7), 2):
            pair_tot += 1; pair_cf += gcd(S[i], S[j]) > 1
        k = [d for d in S if d != e and gcd(d, e) > 1]
        opshare += len(k); opn += 6
        # (C) the subset sharing a factor with the opener (with the opener)
        sub = [d for d in S if gcd(d, e) > 1]
        if len(sub) >= 1:
            c[('subset sharing a factor with the opener has cascade = t*', cascade(sub) == t)] += 1
            if len(sub) >= 2: c[('  ... with at least 2 readings', cascade(sub) == t)] += 1
        # reduced to cofactors: divide by gcd of the subset
        gg = reduce(gcd, sub)
        if len(sub) >= 2 and gg > 1: c[('subset has a common divisor > 1 itself', True)] += 1
    out.write("\n==== %s: %d sets (unique opener and closer, non-unit-fraction)\n" % (name, n))
    out.write("  base rate: pairs of readings with gcd > 1: %d of %d\n" % (pair_cf, pair_tot))
    out.write("  readings (other than the opener) sharing a factor with the opener: %d of %d\n" % (opshare, opn))
    for k, v in sorted(c.items(), key=str): out.write("  %s: %d\n" % (k, v))
    out.write("  (D capped at 2, gcd(e,f) > 1): %s\n" % dict(sorted(byD.items())))
out.close(); print(open('modgap_cofactor_v1.out').read()[len(__doc__):])
