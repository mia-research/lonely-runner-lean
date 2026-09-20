"""The residual bucket: configurations where NO runner reaches a proved branch.

Branch A  : d_max(i) <= 7 * d_min(i)
Branch B1 : the reading is integral AND no s_j = 0 (mod 8)   [the spine serves]

Residual  : every runner has a mixed reading (some s_j not an integer) OR a blocked
            integer reading (some s_j = 0 mod 8).

Exact integer/rational arithmetic.  Nobody pinned.  No density, no covering.
"""
from fractions import Fraction as F
from math import gcd
from functools import reduce
import random
from collections import Counter

def reading(V, i):
    d = [abs(V[i]-V[j]) for j in range(8) if j != i]
    m = min(d)
    return d, m, [F(x, m) for x in d]

def branch(V, i):
    d, m, s = reading(V, i)
    if max(d) <= 7*m: return 'A'
    if all(x.denominator == 1 for x in s):
        return 'B1' if all(x.numerator % 8 != 0 for x in s) else 'blocked'
    return 'mixed'

def classify(V):
    return [branch(V, i) for i in range(8)]

random.seed(2026)
rates = {}
residuals = []
for span in (50, 200, 1000, 5000):
    hit = 0; N = 0
    for _ in range(4000):
        V = sorted(random.sample(range(1, span+1), 8))
        b = classify(V); N += 1
        if 'A' not in b and 'B1' not in b:
            hit += 1
            if len(residuals) < 4000: residuals.append((span, V, b))
    rates[span] = (hit, N)

print('rate of the residual bucket (no runner in A or B1):')
for span in sorted(rates):
    h, n = rates[span]
    print('   span %-6d %5d / %-6d = %5.2f%%' % (span, h, n, 100*h/n))
print()
print('composition of the eight runners inside residual configurations:')
comp = Counter()
for span, V, b in residuals:
    comp[(b.count('mixed'), b.count('blocked'))] += 1
for k, v in comp.most_common(10):
    print('   %d mixed + %d blocked   %5d  (%5.2f%%)' % (k[0], k[1], v, 100*v/len(residuals)))
print()
print('structural marks of the residual configurations (%d of them):' % len(residuals))
g = Counter(); rat = []; dm = Counter()
for span, V, b in residuals:
    G = reduce(gcd, [abs(V[i]-V[j]) for i in range(8) for j in range(i+1,8)])
    g[G] += 1
    mins = [min(abs(V[i]-V[j]) for j in range(8) if j != i) for i in range(8)]
    dm[min(mins)] += 1
    rat.append(max(V)-min(V))
print('   gcd of all differences: %s' % dict(sorted(g.items())[:6]))
print('   smallest d_min over the eight: %s' % dict(sorted(dm.items())[:8]))
rat.sort()
print('   spread max-min: median %d, min %d, max %d' % (rat[len(rat)//2], rat[0], rat[-1]))
