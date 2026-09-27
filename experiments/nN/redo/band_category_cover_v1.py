"""E124: the fewest lap assignments (wall-bounded cones) covering the band.  For each band shape, its categories are
the lap assignments of its clear components in [1,7] u [9,15].  Greedy cover over: every band set to N (exhaustive)
plus the late fine shapes (walked from the extremal family).  Exact."""
import itertools, random, sys
from fractions import Fraction as F
from collections import Counter
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
def cats(s):
    out = set()
    for lo, hi in [(F(1), F(7)), (F(9), F(15))]:
        for a, b in clear_set(s, lo, hi):
            m = (a + b) / 2
            out.add(tuple(int(x * m // 8) for x in s))
    return frozenset(out)
N = int(sys.argv[1]) if len(sys.argv) > 1 else 32
shapes = []
for T in itertools.combinations(range(1, N + 1), 7):
    if 7 * T[0] < T[-1] < 9 * T[0]: shapes.append(cats([F(d, T[0]) for d in T]))
# late fine shapes: walk from the extremal family keeping R* > 7
D1 = 27720; rnd = random.Random(11)
def least(s):
    S = clear_set(s, F(1), F(15)); return S[0][0] if S else None
seeds = [(1, 2.3509, 3.2412, 4.1886, 5.2223, 5.7871, 7.4378), (1, 2.5302, 3.2218, 4.1563, 4.531, 5.6544, 7.0302)]
late = 0
for sd in seeds:
    T = [int(round(x * D1)) for x in sd]
    for step in range(2500):
        L = list(T); i = rnd.randrange(1, 7); L[i] += rnd.randrange(-600, 601)
        U = sorted(set(L))
        if len(U) < 7 or U[0] != D1 or not (7 * D1 < U[-1] < 9 * D1): continue
        s = [F(d, D1) for d in U]; R = least(s)
        if R is not None and R > 7:
            T = U
            if step % 10 == 0: shapes.append(cats(s)); late += 1
print("shapes:", len(shapes), " (late fine:", late, ")  empty-category shapes:", sum(1 for c in shapes if not c))
left = list(shapes); chosen = []
while left:
    cnt = Counter(v for c in left for v in c)
    v, n = cnt.most_common(1)[0]; chosen.append((v, n)); left = [c for c in left if v not in c]
print("greedy cover by lap assignments: %d categories" % len(chosen))
for v, n in chosen: print("   laps %s  newly covered %d" % (''.join(map(str, v)) if max(v) < 10 else v, n))
