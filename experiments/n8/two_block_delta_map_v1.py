"""E654. Phase windows of an AP block and where the landing's delta sits.
C_j(q) = {delta in [0,1) : frac(D delta) not in (3/4,1) for every D in [-j, q-1-j], D != 0}: the phase steps at which
an AP block of q readings is clear at the exit of its reading j. Computed exactly from the breakpoints
(m + 3/4)/|D|, m/|D|. Then for every gap-strip landing whose setter is an other-block reading: q, j, delta* = s t*,
floor(delta*), and the index of the component of C_j holding frac(delta*). Exact Fractions."""
import math, pickle
from fractions import Fraction as F
from collections import Counter
E = F(1, 8)
def frac(x): return x - math.floor(x)
def clear(delta, j, q):
    return all(not (F(3, 4) < frac(D * delta) < 1) for D in range(-j, q - j) if D != 0)
def Cj(j, q):
    pts = {F(0), F(1)}
    for D in range(1, q):
        for m in range(0, D + 1):
            pts |= {F(m, D), F(4 * m + 3, 4 * D)}
    pts = sorted(x for x in pts if 0 <= x <= 1)
    comps = []
    for a, b in zip(pts, pts[1:]):
        if clear((a + b) / 2, j, q):
            if comps and comps[-1][1] == a: comps[-1] = (comps[-1][0], b)
            else: comps.append((a, b))
    return comps
print("Phase windows C_j(q) in [0,1) (closed components):")
for q in range(2, 7):
    for j in range(q):
        print("  q=%d j=%d:" % (q, j), [(str(a), str(b)) for a, b in Cj(j, q)])
recs = pickle.load(open('two_block_strip_cascade_v1.pkl', 'rb'))
def sp(p, A, b): return [F(i) for i in range(p)] + [A + j * b for j in range(8 - p)]
tab = Counter(); notin = 0
for (p, b, G, k, t, op, M, mv, R, r) in recs:
    if G <= 0 or op[0] != 'set': continue
    v = sp(p, G + p - 1, b)
    ownb = list(range(p)) if k < p else list(range(p, 8))
    if op[1] in ownb: continue
    s = b if k < p else F(1)
    oth = [i for _, i in sorted((abs(v[i] - v[k]), i) for i in range(8) if i not in ownb)]
    q = len(oth); j = oth.index(op[1]); d = s * t
    cs = Cj(j, q); f = frac(d)
    idx = next((n + 1 for n, (a, bb) in enumerate(cs) if a <= f <= bb), None)
    if idx is None: notin += 1
    tab[(q, j, 'lap of delta %d' % math.floor(d), 'window %s of %d' % (idx, len(cs)))] += 1
print("landings with delta outside C_j (would contradict the definitions):", notin)
for kk, vv in sorted(tab.items()): print("  %6d" % vv, kk)
