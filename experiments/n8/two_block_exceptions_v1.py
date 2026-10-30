"""E647 exceptions: gap-strip records (G > 0) where the other block has no clear point in the own window W.
Features recorded: p, own block size, subject position, whether the nearest reading is in the other block,
G against u, the other block's step b' relative to u, the landing R = 8 d_min t and where it lies relative to W. Exact."""
import pickle, math
from fractions import Fraction as F
from collections import Counter
E = F(1, 8)
def dist(x):
    f = x - math.floor(x); return min(f, 1 - f)
recs = pickle.load(open('two_block_strip_cascade_v1.pkl', 'rb'))
def sp(p, A, b): return [F(i) for i in range(p)] + [A + j * b for j in range(8 - p)]
feat = Counter(); ex = []
for (p, b, G, k, t, op, M, mv, R, r) in recs:
    if G <= 0: continue
    A = G + (p - 1); v = sp(p, A, b)
    own = list(range(p)) if k < p else list(range(p, 8)); oth = [i for i in range(8) if i not in own]
    u = F(1) if k < p else b; uo = b if k < p else F(1)
    J = max(own.index(k), len(own) - 1 - own.index(k))
    lo, hi = F(1, 8) / u, F(7, 8) / (J * u)
    ds = [abs(v[i] - v[k]) for i in oth]
    ok = any(lo <= c <= hi and all(dist(d * c) >= E for d in ds)
             for c in {lo} | {(F(m) + E) / d for d in ds for m in range(0, int(d * hi) + 1)})
    if ok: continue
    edge = own.index(k) in (0, len(own) - 1) and ((k == p - 1) or (k == p))
    nearest_other = min(ds) < u
    key = ('edge subject' if edge else 'not at edge', 'nearest is other block' if nearest_other else 'nearest is own step',
           'other step < own step' if uo < u else 'other step > own step', 'landing after W' if t > hi else 'landing before W')
    feat[key] += 1
    if not nearest_other and len(ex) < 8: ex.append((p, b, G, k, R, t, hi))
for kk, vv in sorted(feat.items(), key=lambda x: -x[1]): print(vv, kk)
print("examples with nearest = own step (p, b, G, subject, R, landing, end of W):")
for e in ex: print("  ", e)
