"""E647 place test. Class: the strip of two_block_strip_cascade_v1 (gap G > 0 and interleaved G <= 0 reported apart).
Place named: for subject k in a block of step u (1 or b) with J = the largest multiple of u among its own-block
readings, W = [1/(8u), 7/(8 J u)] (the own block is 1/8-clear on all of W, by j u t in [j/8, 7j/(8J)]); the landing
is the first t in W at which every other-block reading is clear. Pass: equality with the cascade's landing; misses
listed by kind. Exact."""
import pickle, math
from fractions import Fraction as F
from collections import Counter
E = F(1, 8)
def dist(x):
    f = x - math.floor(x); return min(f, 1 - f)
recs = pickle.load(open('two_block_strip_cascade_v1.pkl', 'rb'))
def sp(p, A, b): return [F(i) for i in range(p)] + [A + j * b for j in range(8 - p)]
res = Counter(); miss = []
for (p, b, G, k, t, op, M, mv, R, r) in recs:
    A = G + (p - 1); v = sp(p, A, b)
    own = list(range(p)) if k < p else list(range(p, 8))
    oth = [i for i in range(8) if i not in own]
    u = F(1) if k < p else b
    J = max(own.index(k), len(own) - 1 - own.index(k))
    lo, hi = F(1, 8) / u, F(7, 8) / (J * u)
    ds = [abs(v[i] - v[k]) for i in oth]
    # first t in [lo, hi] where all other readings clear: candidates lo and openings (M+1/8)/d
    cands = sorted({lo} | {(F(m) + E) / d for d in ds for m in range(0, int(d * hi) + 1)})
    place = None
    for c in cands:
        if lo <= c <= hi and all(dist(d * c) >= E for d in ds): place = c; break
    regime = 'interleaved' if G <= 0 else 'gap'
    dmin_own = min(abs(v[i] - v[k]) for i in range(8) if i != k) == u
    if place == t: res[(regime, 'hit')] += 1
    else:
        why = 'no clear point in W' if place is None else ('place earlier' if place < t else 'place later')
        why += '' if dmin_own else ' (d_min not own step)'
        res[(regime, why)] += 1
        if len(miss) < 12 and regime == 'gap': miss.append((p, b, G, k, t, place, op, M))
for kk, vv in sorted(res.items()): print(vv, kk)
print("first gap misses (p, b, G, subject, landing, place, opener, lap):")
for m in miss: print("  ", m)
