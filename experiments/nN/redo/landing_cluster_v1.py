"""E143: is the landing the exit of a cluster's slowest member?  Clusters on lap k: maximal runs of readings with
consecutive ratio below rho_k = (8k+1)/(8k-1) (a sweep on lap k passes exactly these).  At the landing, flank f exits
lap k_f; test whether f is the slowest member of its lap-k_f cluster.  Populations: band to 24, Case B to 24, late fine
shapes.  Exact."""
import itertools, random, sys
from fractions import Fraction as F
from math import floor
from collections import Counter
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def cascade(T):
    t = F(1, 8 * T[0])
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)
def test(T):
    t = cascade(T)
    fl = [i for i, d in enumerate(T) if (8 * d * t) % 8 == 1]
    f = fl[0]; k = floor(T[f] * t)
    if k == 0: return 'flank on lap 0 (first window)', f
    # slowest of its cluster: previous reading (if any) at ratio >= rho_k
    if f == 0: return 'slowest of cluster (nearest runner)', f
    ratio = F(T[f], T[f - 1]); rho = F(8 * k + 1, 8 * k - 1)
    return ('slowest of its cluster' if ratio >= rho else 'inside a cluster'), f
C = Counter(); ex = []
for T in itertools.combinations(range(1, 25), 7):
    if not (7 * T[0] < T[-1]): continue
    pop = 'band24' if T[-1] <= 9 * T[0] else 'caseB24'
    r, f = test(T); C[(pop, r)] += 1
    if r == 'inside a cluster' and len(ex) < 12: ex.append((T, f))
D1 = 27720; rng = random.Random(41); late = set()
for sd in [(1, 2.3509, 3.2412, 4.1886, 5.2223, 5.7871, 7.4378), (1, 2.5302, 3.2218, 4.1563, 4.531, 5.6544, 7.0302)]:
    T = [int(round(x * D1)) for x in sd]
    for step in range(3000):
        U = list(T); i = rng.randrange(1, 7); U[i] += rng.randrange(-500, 501); U = sorted(set(U))
        if len(U) < 7 or U[0] != D1 or not (7 * D1 < U[-1] < 9 * D1): continue
        if clear_set([F(d, D1) for d in U], F(1), F(7)): continue
        T = U; late.add(tuple(U))
for T in late: C[('late', test(T)[0])] += 1
for k, v in sorted(C.items()): print("  %7d  %s" % (v, k))
print("examples inside a cluster:", ex)
