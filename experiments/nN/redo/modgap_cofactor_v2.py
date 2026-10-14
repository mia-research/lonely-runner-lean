"""modgap_cofactor_v2 (2026-10-06): control for modgap_cofactor_v1.  The shared factor of the opener and closer with the factor 2 removed
(gcd of the odd parts > 1) against the same rate over all pairs of readings of the same sets, and the shared 2-adic structure separately
(both even; min 2-adic valuation).  Populations as modgap_cofactor_v1.  Exact.  [PROVISIONAL: counting tool; supports: the base-rate comparison]"""
import itertools, math, collections, sys
sys.path.insert(0, '.')
from fractions import Fraction as F
from math import gcd
from functools import reduce
from modgap_lib_v1 import cascade, openers, component
exec(open('modgap_cofactor_v1.py').read().split("out = open")[0].split('from modgap_lib_v1 import cascade, openers, component, simplest, E8, E78')[1])
def odd(x):
    while x % 2 == 0: x //= 2
    return x
def v2(x):
    n = 0
    while x % 2 == 0: x //= 2; n += 1
    return n
out = open('modgap_cofactor_v2.out', 'w'); out.write(__doc__ + "\n")
for name, gen in (('S1', s1()), ('T2', t2()), ('T3', t3())):
    n = 0; ef_odd = ef_even = 0; pr = po = pe = pt = 0
    for S in gen:
        t = cascade(S); tR, cl = component(S, t)
        if t < 1 and F(1, math.ceil(1 / tR)) >= t: continue
        op = openers(S, t)
        if len(op) != 1 or len(cl) != 1: continue
        e, f = op[0], cl[0]; n += 1
        ef_odd += gcd(odd(e), odd(f)) > 1; ef_even += (e % 2 == 0 and f % 2 == 0)
        for i, j in itertools.combinations(range(7), 2):
            pt += 1; po += gcd(odd(S[i]), odd(S[j])) > 1; pe += (S[i] % 2 == 0 and S[j] % 2 == 0)
    out.write("\n==== %s: %d sets\n  opener-closer: odd parts share a factor %d (%.3f); both even %d (%.3f)\n  all pairs of the same sets: odd parts share a factor %d of %d (%.3f); both even %d (%.3f)\n" %
              (name, n, ef_odd, ef_odd / n, ef_even, ef_even / n, po, pt, po / pt, pe, pe / pt))
out.write("\n(decimals are for display; counts are exact)\n")
out.close(); print(open('modgap_cofactor_v2.out').read()[len(__doc__):])
