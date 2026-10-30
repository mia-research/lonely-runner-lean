"""E647: for the 186 gap-strip exceptions whose nearest reading is the own step, which clear window of the own AP block
(readings j u, j <= J) contains the landing? Windows are the components of {t : j u t clear for all j <= J}, numbered
from 1 in time. Exact: components are computed from the zone edges (M +- 1/8)/(j u) up to the landing."""
import pickle, math
from fractions import Fraction as F
from collections import Counter
E = F(1, 8)
def dist(x):
    f = x - math.floor(x); return min(f, 1 - f)
recs = pickle.load(open('two_block_strip_cascade_v1.pkl', 'rb'))
def sp(p, A, b): return [F(i) for i in range(p)] + [A + j * b for j in range(8 - p)]
idx = Counter(); n = 0
for (p, b, G, k, t, op, M, mv, R, r) in recs:
    if G <= 0: continue
    A = G + (p - 1); v = sp(p, A, b)
    own = list(range(p)) if k < p else list(range(p, 8)); oth = [i for i in range(8) if i not in own]
    u = F(1) if k < p else b
    J = max(own.index(k), len(own) - 1 - own.index(k))
    lo, hi = F(1, 8) / u, F(7, 8) / (J * u)
    ds = [abs(v[i] - v[k]) for i in oth]
    if min(ds) < u: continue
    ok = any(lo <= c <= hi and all(dist(d * c) >= E for d in ds)
             for c in {lo} | {(F(m) + E) / d for d in ds for m in range(0, int(d * hi) + 1)})
    if ok: continue
    n += 1
    own_r = [j * u for j in range(1, J + 1)]
    edges = sorted({(F(m) + s * E) / d for d in own_r for m in range(0, int(d * t) + 2) for s in (1, -1)} | {t})
    # count components of the own clear set that start at or before t
    comps = 0; inside = False
    for a, bb in zip(edges, edges[1:]):
        mid = (a + bb) / 2
        c = all(dist(d * mid) >= E for d in own_r) or all(dist(d * a) >= E for d in own_r) and a == bb
        if c and not inside and a <= t: comps += 1
        inside = c
    xR = 8 * u * t
    idx[(J, comps, 'R_own in [%s,%s]' % (math.floor(xR), math.floor(xR) + 1))] += 1
print("exceptions with nearest = own step:", n)
for kk, vv in sorted(idx.items()): print(vv, "J=%d, own window #%d," % kk[:2], kk[2])
