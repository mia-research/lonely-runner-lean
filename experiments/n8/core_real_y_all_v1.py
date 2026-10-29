# E643 [PROVISIONAL: covering]: for each of the 53 cores, the real extra readings y in [3/4, y0] served by the core's own windows, where y0 = 1/(4 w) and w = widest window (above y0 the single-reading window lemma applies; below 3/4 the periodic shift applies).  Exact.
import math
from fractions import Fraction as F
from classes_lib_v1 import clear_iv, meet
cores = [tuple(int(x) for x in l.split(',')) for l in open('core_cover_cores.txt').read().split()]
res = []
for core in cores:
    g = 0
    for d in core: g = math.gcd(g, d)
    T = F(1, g)
    J = clear_iv(F(core[0]), T)
    for s in core[1:]: J = meet(J, clear_iv(F(s), T))
    J = [(lo, hi) for lo, hi in J if hi >= lo]
    w = max(hi - lo for lo, hi in J); y0 = 1 / (4 * w)
    iv = []; NMAX = 400
    for lo, hi in J:
        for n in range(NMAX + 1):
            a, b = lo + F(n) * T, hi + F(n) * T
            if b * y0 < F(1, 8): continue
            k = 0
            while F(8 * k + 1, 8) / b <= y0:
                iv.append((F(8 * k + 1, 8) / b, F(8 * k + 7, 8) / a)); k += 1
    iv.sort(); gaps = []; cur = F(3, 4)
    for lo, hi in iv:
        if hi <= cur: continue
        if lo > cur: gaps.append((cur, lo))
        cur = max(cur, hi)
        if cur >= y0: break
    if cur < y0: gaps.append((cur, y0))
    res.append((core, len(J), w, y0, gaps))
    print(core, 'windows', len(J), 'y0', float(y0), 'g', g, 'gaps', [(str(a), str(b)) for a, b in gaps[:3]], flush=True)
print('cores', len(res), 'with no gap in [3/4,y0]:', sum(1 for r in res if not r[4]))
