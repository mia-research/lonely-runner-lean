"""E141: the order in which a relay passes the isolation between runners: setter ranks (0 = nearest runner) and the lap
each move lands on, along late band chains and the longest band-24 chains.  Exact."""
import itertools, random, sys
from fractions import Fraction as F
from math import floor
from collections import Counter
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
from relay_setters_v1 import trace
E8 = F(1, 8)
def seq(T):
    R, mv = trace(T)
    out = []
    for w, r, t2 in mv:
        k = int(T[r] * t2 - E8)   # lap on which the setter exits (8k+1)/8
        out.append('%d.%d' % (r, k))
    return float(R), out
band = [T for T in itertools.combinations(range(1, 25), 7) if 7 * T[0] < T[-1] <= 9 * T[0]]
L = sorted(band, key=lambda T: -len(trace(T)[1]))[:8]
print("longest band-24 chains (setter rank.lap per move):")
for T in L:
    R, s = seq(T); print("  ", T, "R* %.3f" % R, ' '.join(s))
D1 = 27720; rng = random.Random(41); late = []
for sd in [(1, 2.3509, 3.2412, 4.1886, 5.2223, 5.7871, 7.4378), (1, 2.5302, 3.2218, 4.1563, 4.531, 5.6544, 7.0302)]:
    T = [int(round(x * D1)) for x in sd]
    for step in range(3000):
        U = list(T); i = rng.randrange(1, 7); U[i] += rng.randrange(-500, 501); U = sorted(set(U))
        if len(U) < 7 or U[0] != D1 or not (7 * D1 < U[-1] < 9 * D1): continue
        if clear_set([F(d, D1) for d in U], F(1), F(7)): continue
        T = U; late.append(tuple(U))
print("\nlate shapes (every 600th):")
for T in late[::600]:
    R, s = seq(T); print("  ", [round(d / D1, 3) for d in T], "R* %.3f" % R, ' '.join(s))
# rank-order statistic: fraction of consecutive setter pairs going to a slower runner
dn = Counter()
for T in late:
    R, s = seq(T); r = [int(x.split('.')[0]) for x in s]
    for a, b in zip(r, r[1:]): dn['to slower' if b < a else 'to faster' if b > a else 'same'] += 1
print("\nlate: consecutive setter steps:", dict(dn))
