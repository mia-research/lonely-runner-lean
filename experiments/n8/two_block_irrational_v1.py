"""E657. The two-block strip with irrational parameters, exact in Q(sqrt2) (qsqrt2_v1.py).
Speeds c + i (i < p) and c + A + j b' (j < 8 - p), b' = n/12 + sqrt2/100 (n = 2, 6, 10, ..., 94), gap
G' = g + sqrt2/997 with g from max(1,b)/4 in steps of max(1,b)/4 below Gcov(p, n/12) (E646), and interleaved
g = -(p-1) .. 0 in steps of 1/4; every subject. Tests, each against the unchanged cascade:
 C1: landing = first instant >= 1/(8 d_min) with every reading clear, found by scanning openings without the cascade;
 E648: landing = first point of the first clear component of the block N holding the nearest reading at which the
       other block is clear (components built from the zones, single points kept);
 E653: at every move from an other-block setter, the predicted next setter (largest exit among in-way readings,
       other block read through delta = s t) equals the cascade's.
Floats only propose floor candidates; every decision is an exact sign. No sampling: the grid above is enumerated."""
import sys, io, contextlib
from fractions import Fraction as F
from collections import Counter
from qsqrt2_v1 import Q2, dist, E
with contextlib.redirect_stdout(io.StringIO()):
    from two_block_remainder_v1 import gcov
def rnd(x): return (x + F(1, 2)).floor()
def cascade(r):
    t = F(1, 8) / r[0]; path = []
    while True:
        way = [(i, d) for i, d in enumerate(r) if dist(d * t) < E]
        if not way: return t, path
        best = None
        for i, d in way:
            M = rnd(d * t); nt = (M + E) / d
            if best is None or nt > best[0]: best = (nt, i, M)
        t, i, M = best; path.append((i, M, t))
def first_lonely(r, upto):
    lo = F(1, 8) / r[0]
    cands = {lo}
    for d in r:
        for M in range(0, (d * upto).floor() + 1): cands.add((M + E) / d)
    for t in sorted(cands, key=float):
        if t < lo or t > upto: continue
        if all(dist(d * t) >= E for d in r): return t
def comps(ds, T):
    zones = []
    for d in ds:
        for m in range(0, (d * T).floor() + 2): zones.append(((m - E) / d, (m + E) / d))
    zones.sort(key=lambda z: float(z[0]))
    out = []; cur = Q2(0)
    for a, b in zones:
        if a >= cur: out.append((cur, a))
        if b > cur: cur = b
    return out
r2 = Q2(0, 1)
res = Counter(); steps = Counter(); n_rec = 0; EMPTY = []; GAPD = []
for p in range(2, 7):
    for n in range(2, 96, 4):
        bq = F(n, 12); b = bq + r2 * F(1, 100)
        gc, _ = gcov(p, bq); m = max(F(1), bq)
        gs = [F(-(p - 1)) + F(j, 4) for j in range(4 * (p - 1) + 1)]
        g = m / 4
        while g < gc: gs.append(g); g += m / 4
        for g in gs:
            G = r2 * F(1, 997) + g
            A = G + (p - 1)
            v = [Q2(i) for i in range(p)] + [A + b * j for j in range(8 - p)]
            if len({(x.a, x.b) for x in v}) < 8: continue
            for k in range(8):
                rd = sorted(((v[i] - v[k]) if v[i] > v[k] else (v[k] - v[i]), i) for i in range(8) if i != k)
                rd.sort(key=lambda z: float(z[0]))
                r = [d for d, _ in rd]; who = [i for _, i in rd]
                t, path = cascade(r); n_rec += 1
                fl = first_lonely(r, t); res['C1 ok' if (fl is not None and fl == t) else 'C1 FAIL'] += 1
                ownb = list(range(p)) if k < p else list(range(p, 8))
                do = [d for d, i in rd if i in ownb]; dx = [d for d, i in rd if i not in ownb]
                N, O = (do, dx) if min(do, key=float) <= min(dx, key=float) else (dx, do)
                c1 = comps(N, t + 2)[0]
                place = None
                cands = {c1[0]}
                for d in O:
                    for M in range(0, (d * c1[1]).floor() + 1): cands.add((M + E) / d)
                for c in sorted(cands, key=float):
                    if c1[0] <= c <= c1[1] and all(dist(d * c) >= E for d in O): place = c; break
                reg = 'gap' if g > 0 else 'interleaved'
                res[(reg, 'E648 first window: hit' if (place is not None and place == t) else 'E648 first window: miss')] += 1
                s = b if k < p else Q2(1)
                oth = [i for _, i in sorted(((v[i] - v[k]) if v[i] > v[k] else (v[k] - v[i]), i) for i in range(8) if i not in ownb)]
                for (ia, Ma, ta), (ib, Mb, tb) in zip(path, path[1:]):
                    wa = who[ia]
                    if wa in ownb: continue
                    j = oth.index(wa); delta = s * ta; cand = []
                    for i in range(len(oth)):
                        if i == j: continue
                        f = (delta * (i - j)); f = f - f.floor()
                        if f > F(3, 4) and f < 1:
                            xi = r[who.index(oth[i])]
                            cand.append(((ta + (1 - f) / xi), 'oth', i))
                    for w in ownb:
                        if w == k: continue
                        d = r[who.index(w)]
                        if dist(d * ta) < E: cand.append(((rnd(d * ta) + E) / d, 'own', w))
                    if not cand:
                        steps[(reg, 'E653 step: no predicted in-way reading')] += 1
                        if len(EMPTY) < 5:
                            wb = who[ib]
                            EMPTY.append((p, n, str(g), k, 'setter', wa, 'next', wb, 'delta', delta, 'in way at ta:',
                                [(who[i], str(dist(d * ta))) for i, d in enumerate(r) if dist(d * ta) < E]))
                        continue
                    pred = max(cand, key=lambda z: float(z[0]))
                    wb = who[ib]; act = ('oth', oth.index(wb)) if wb not in ownb else ('own', wb)
                    ok = (pred[1], pred[2]) == act and pred[0] == tb
                    steps[(reg, 'E653 step: agree' if ok else 'E653 step: differ')] += 1
                    if not ok and reg == 'gap' and len(GAPD) < 5: GAPD.append((p, n, str(g), k, wa, act, pred[1:], 'pred exit', pred[0], 'actual', tb))
print("records:", n_rec)
for kk, vv in sorted(res.items(), key=str): print("  ", vv, kk)
for kk, vv in sorted(steps.items(), key=str): print("  ", vv, kk)

for e in EMPTY: print('  empty case:', e)
for e in GAPD: print('  gap differ:', e)
