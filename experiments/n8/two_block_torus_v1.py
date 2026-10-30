"""E661. The other block (q readings x_0 + i s, gap strip) at instant t has phases phi + i delta, phi = x_0 t,
delta = s t: a point moving on a line in the 2-torus. For fixed delta, some phi clears all q readings iff the points
{i delta mod 1 : i < q} leave a circular gap >= 1/4 (closed clear set [1/8, 7/8]). Dead set D_q = delta in [0,1)
with every gap < 1/4. Computed exactly from breakpoints (gap equalities and order changes). Then, for the gap-strip
records whose nearest reading is the own step: delta range over the own window W = [1/(8u), 7/(8Ju)], i.e.
[s/(8u), 7s/(8Ju)], and whether it lies inside D_q (no phi can work during W) or meets the alive set (phi decides).
Cross-tabulated with whether the landing is in W (E647). Exact Fractions."""
import math, pickle
from fractions import Fraction as F
from collections import Counter
def frac(x): return x - math.floor(x)
def maxgap(delta, q):
    pts = sorted(frac(i * delta) for i in range(q))
    gaps = [b - a for a, b in zip(pts, pts[1:])] + [1 - pts[-1] + pts[0]]
    return max(gaps)
def dead_intervals(q):
    bp = {F(0), F(1)}
    for d in range(1, q):
        for m in range(0, d + 1):
            for c in (F(0), F(1, 4), F(3, 4)):
                x = (m + c) / d
                if 0 <= x <= 1: bp.add(x)
    bp = sorted(bp); out = []
    for a, b in zip(bp, bp[1:]):
        if maxgap((a + b) / 2, q) < F(1, 4):
            if out and out[-1][1] == a: out[-1] = (out[-1][0], b)
            else: out.append((a, b))
    return out
D = {q: dead_intervals(q) for q in range(2, 7)}
for q in range(2, 7):
    print("q=%d dead bands of delta in (0,1) (open intervals):" % q, [(str(a), str(b)) for a, b in D[q]])
def dead_cover(lo, hi, q):
    # is [lo, hi] inside one dead open interval (mod 1)? requires hi - lo < 1
    if hi - lo >= 1: return False
    k = math.floor(lo); a, b = lo - k, hi - k
    return any(x < a and b < y for x, y in D[q])
recs = pickle.load(open('two_block_strip_cascade_v1.pkl', 'rb'))
def sp(p, A, b): return [F(i) for i in range(p)] + [A + j * b for j in range(8 - p)]
tab = Counter()
for (p, b, G, k, t, op, M, mv, R, r) in recs:
    if G <= 0: continue
    v = sp(p, G + p - 1, b)
    ownb = list(range(p)) if k < p else list(range(p, 8)); u = F(1) if k < p else b; s = b if k < p else F(1)
    if min(abs(v[i] - v[k]) for i in range(8) if i != k) < u: continue
    q = 8 - len(ownb)
    J = max(ownb.index(k), len(ownb) - 1 - ownb.index(k))
    lo, hi = F(1, 8) / u, F(7, 8) / (J * u)
    inW = lo <= t <= hi
    tab[('landing in W' if inW else 'landing after W', 'delta dead throughout W' if dead_cover(s * lo, s * hi, q) else 'delta meets alive set in W')] += 1
for kk, vv in sorted(tab.items()): print(vv, kk)
