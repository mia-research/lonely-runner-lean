"""E653 check of a derived step rule (derivation in the log entry first; the run only checks it).
At a move whose setter is other-block reading j at lap M (exit t = (M+1/8)/x_j), with delta = s t (s the other block's
step): reading i of that block is in the way iff frac((i-j) delta) in (3/4, 1), and then its exit is later than t by
(1 - frac((i-j) delta))/x_i. Predicted next setter: among in-way readings of BOTH blocks, the largest exit; the
other-block part uses only delta and the x_i. Check: predicted (block, index, lap) equals the cascade's next setter,
every move of every gap-strip path with the nearest reading in the own block. Also records, for other-block to
other-block moves, the step dj against delta's band. Exact Fractions."""
import math, pickle
from fractions import Fraction as F
from collections import Counter
E = F(1, 8)
def frac(x): return x - math.floor(x)
def dist(x):
    f = frac(x); return min(f, 1 - f)
def cascade_path(r):
    t = F(1, 8 * r[0]); path = []
    while True:
        way = [(i, d) for i, d in enumerate(r) if dist(d * t) < E]
        if not way: return t, path
        best = None
        for i, d in way:
            M = round(d * t); nt = (F(M) + E) / d
            if best is None or nt > best[0]: best = (nt, i, M)
        t, i, M = best; path.append((i, M, t))
recs = pickle.load(open('two_block_strip_cascade_v1.pkl', 'rb'))
def sp(p, A, b): return [F(i) for i in range(p)] + [A + j * b for j in range(8 - p)]
agree = 0; disagree = 0; bad = []; band = Counter()
for (p, b, G, k, t0, op, M0, mv, R, r0) in recs:
    if G <= 0 or mv < 2: continue
    v = sp(p, G + p - 1, b)
    ownb = list(range(p)) if k < p else list(range(p, 8)); u = F(1) if k < p else b; s = b if k < p else F(1)
    if min(abs(v[i] - v[k]) for i in range(8) if i != k) < u: continue
    oth = [i for _, i in sorted((abs(v[i] - v[k]), i) for i in range(8) if i not in ownb)]
    xo = [abs(v[i] - v[k]) for i in oth]
    rd = sorted((abs(x - v[k]), i) for i, x in enumerate(v) if i != k)
    r = [d for d, _ in rd]; who = [i for _, i in rd]
    _, path = cascade_path(r)
    for (ia, Ma, ta), (ib, Mb, tb) in zip(path, path[1:]):
        wa = who[ia]
        if wa in ownb: continue
        j = oth.index(wa); delta = s * ta
        cands = []
        for i in range(len(oth)):
            f = frac((i - j) * delta)
            if i != j and F(3, 4) < f < 1:
                ext = ta + (1 - f) / xo[i]; cands.append((ext, 'oth', i))
        for w in ownb:
            if w == k: continue
            d = abs(v[w] - v[k])
            if dist(d * ta) < E:
                cands.append(((round(d * ta) + E) / d, 'own', w))
        pred = max(cands)
        wb = who[ib]
        actual = ('oth', oth.index(wb)) if wb not in ownb else ('own', wb)
        if (pred[1], pred[2]) == actual and pred[0] == tb: agree += 1
        else:
            disagree += 1
            if len(bad) < 10: bad.append((p, b, G, k, j, delta, pred, actual))
        if actual[0] == 'oth':
            dj = actual[1] - j
            band[(dj, 'frac(dj*delta) in (3/4,1)')] += 1
print("moves from an other-block setter: predicted = cascade:", agree, " differ:", disagree)
for x in bad: print("  ", x)
print("steps dj (all consistent with frac(dj*delta) in (3/4,1) by construction):", sorted(band.items())[:20])
