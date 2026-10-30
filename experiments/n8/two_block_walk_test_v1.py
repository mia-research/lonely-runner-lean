"""E652 test of the walk statement, all strip records with G > 0 and the subject's nearest reading in its own block.
Statement: every move of the cascade whose setter and next setter are both in the other block goes from the other
block's reading j (counted from the reading nearest the subject) at lap M to reading j-1 at lap M, or from j = 0 at
lap M to the farthest reading q-1 at lap M+1. Paths recomputed with the unchanged cascade. Misses listed by kind.
Exact Fractions."""
import math, pickle
from fractions import Fraction as F
from collections import Counter
E = F(1, 8)
def dist(x):
    f = x - math.floor(x); return min(f, 1 - f)
def cascade_path(r):
    t = F(1, 8 * r[0]); path = []
    while True:
        way = [(i, d) for i, d in enumerate(r) if dist(d * t) < E]
        if not way: return t, path
        best = None
        for i, d in way:
            M = round(d * t); nt = (F(M) + E) / d
            if best is None or nt > best[0]: best = (nt, i, M)
        t, i, M = best; path.append((i, M))
recs = pickle.load(open('two_block_strip_cascade_v1.pkl', 'rb'))
def sp(p, A, b): return [F(i) for i in range(p)] + [A + j * b for j in range(8 - p)]
moves = Counter(); ex = []; seen = 0; paths_ok = 0; paths = 0
for (p, b, G, k, t, op, M, mv, R, r0) in recs:
    if G <= 0: continue
    v = sp(p, G + p - 1, b)
    ownb = list(range(p)) if k < p else list(range(p, 8)); u = F(1) if k < p else b
    ds = [abs(v[i] - v[k]) for i in range(8) if i != k]
    if min(ds) < u: continue
    oth = sorted((abs(v[i] - v[k]), i) for i in range(8) if i not in ownb); q = len(oth)
    rd = sorted((abs(x - v[k]), i) for i, x in enumerate(v) if i != k)
    r = [d for d, _ in rd]; who = [i for _, i in rd]
    _, path = cascade_path(r)
    lab = []
    for i, Mm in path:
        w = who[i]
        lab.append(('oth', [x for _, x in oth].index(w), Mm) if w not in ownb else ('own', w, Mm))
    paths += 1; ok = True
    for a, c in zip(lab, lab[1:]):
        if a[0] != 'oth' or c[0] != 'oth': moves['involves own block'] += 1; continue
        if (c[1] == a[1] - 1 and c[2] == a[2]): moves['j -> j-1, same lap'] += 1
        elif a[1] == 0 and c[1] == q - 1 and c[2] == a[2] + 1: moves['0 -> q-1, next lap'] += 1
        else:
            ok = False; key = 'other: dj=%d dM=%d' % (c[1] - a[1], c[2] - a[2]); moves[key] += 1
            if len(ex) < 15: ex.append((p, b, G, k, lab))
    paths_ok += ok
print("paths:", paths, " paths with no miss:", paths_ok)
for kk, vv in sorted(moves.items(), key=lambda x: -x[1]): print("  ", vv, kk)
print("misses (p, b, G, subject, path):"); [print("  ", e) for e in ex]
