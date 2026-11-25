"""E944 checks (2026-11-25).  Exact Fractions.
(a) Member 1072: the window's length when reading 4 is raised to the bisection's upper end (path already changed) is an
    exact upper bound for the length inside the path, since the length rises with the move; reported against 2 L0.
(b) The closed single-reading moves of groups R2 (short_window_vertex_v2) whose closing pair is not one of the member's
    near-coincidences: the pair's exact relative gap in the member.
(c) The closed moves of R2 that name no closing pair: at the last kept point, the smallest relative gap between the
    exits of two readings in the way at the same state (a change of the maximum-exit choice is not a zone-edge pair).
"""
import pickle, glob
from fractions import Fraction as Fr
from math import floor, ceil
from collections import Counter
exec(open('short_window_vertex_v1.py').read().split("rec = pickle.load(open('/Users/trentpalelei")[0])
rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
mem = {}
for f in glob.glob('short_window_classes_v1_part*.pkl'):
    for m in pickle.load(open(f, 'rb')): mem[m[0]] = m
# (a)
(_, cls, xi, j, yi, jp, a, b, *_r) = mem[1072]
rs = sorted(Fr(x) for x in rec[1072][1]); T0, sig0 = path_sig(rs); L0 = b - a
Lw = lambda rr: Fr(8 * jp - 1, 8) / rr[yi] - Fr(8 * j + 1, 8) / rr[xi]
lo, hi = Fr(0), Fr(1, 10 ** 7)
mv = lambda e: [rs[q] * (1 + e) if q == xi else rs[q] for q in range(7)]
for _ in range(80):
    mid = (lo + hi) / 2
    if path_sig(mv(mid))[1] == sig0: lo = mid
    else: hi = mid
print('(a) member 1072: length at the first changed point / L0 =', Lw(mv(hi)) / L0, '| < 2:', Lw(mv(hi)) < 2 * L0, '| > 3/2:', Lw(mv(lo)) > Fr(3, 2) * L0)
# (b), (c)
c = Counter()
for f in sorted(glob.glob('short_window_vertex_v2_part*.pkl')):
    for (idx, cl, R, L0, a, res, C) in pickle.load(open(f, 'rb')):
        if R != 'R2': continue
        rs = sorted(Fr(x) for x in rec[idx][1]); Cs = set(C)
        for which, kind, Ln, lo, p in res:
            if kind != 'closed': continue
            if p is not None and p not in Cs:
                g = gap_of(rs, p)
                c[('(b) not a near-coincidence: member gap', '[10^-7, 10^-6)' if Fr(1, 10 ** 7) <= g < Fr(1, 10 ** 6) else ('>= 10^-6' if g >= Fr(1, 10 ** 6) else '< 10^-7'))] += 1
            if p is None:
                (_, _, xi, j, yi, jp, *_q) = mem[idx]; q = xi if which == 'raise x' else yi; sign = 1 if which == 'raise x' else -1
                nw = list(rs); nw[q] = rs[q] * (1 + sign * lo)
                T, path = cascade(nw, E); t = E; best = None
                for s in path + [None]:
                    bl = [r for r in nw if blocked(r, t)]
                    ex = sorted(nxt(r, t) for r in bl)
                    for u in range(len(ex) - 1):
                        d = (ex[u + 1] - ex[u]) / ex[u + 1]
                        if best is None or d < best: best = d
                    if s is None: break
                    lap = floor(s * t + E); t = (lap + E) / s
                c[('(c) no pair named: smallest exit-exit gap at the last kept point', 'below 10^-20' if best is not None and best < Fr(1, 10 ** 20) else 'not below 10^-20')] += 1
                print('(c) E340 index', idx, which, '| smallest exit-exit relative gap ~', None if best is None else '%.3e' % float(best))
for k in sorted(c): print(c[k], '|', k)
# (d) the 3 of (c): is the closing event the readings' order (the moved reading reaching a neighbour)?
for f in sorted(glob.glob('short_window_vertex_v2_part*.pkl')):
    for (idx, cl, R, L0, a, res, C) in pickle.load(open(f, 'rb')):
        if R != 'R2': continue
        for which, kind, Ln, lo, p in res:
            if kind != 'closed' or p is not None: continue
            rs = sorted(Fr(x) for x in rec[idx][1]); (_, _, xi, j, yi, jp, *_q) = mem[idx]
            q = xi if which == 'raise x' else yi; nb = q + 1 if which == 'raise x' else q - 1
            print('(d) E340 index', idx, which, '| moved rank', q + 1, '| neighbour rank', nb + 1, '| relative gap to the neighbour', abs(rs[nb] - rs[q]) / rs[q], '~ %.3e' % float(abs(rs[nb] - rs[q]) / rs[q]), '| last kept move', '%.3e' % float(lo))
# (e) the 3 close at a move of 0: the member's exact ties (gap 0, not the setter) and where a move of 10^-30 changes the path
for idx, which in ((51121, 'raise x'), (65340, 'raise x'), (76449, 'lower y')):
    rs = sorted(Fr(x) for x in rec[idx][1]); (_, _, xi, j, yi, jp, *_q) = mem[idx]; T0, sig = path_sig(rs)
    q = xi if which == 'raise x' else yi; sign = 1 if which == 'raise x' else -1
    ties = sorted(p for p in coinc(rs, Fr(1, 10 ** 30)) if gap_of(rs, p) == 0)
    nw = list(rs); nw[q] = rs[q] * (1 + sign * Fr(1, 10 ** 30)); T1n, s1 = path_sig(nw)
    u = next((k for k in range(min(len(sig), len(s1))) if sig[k] != s1[k]), min(len(sig), len(s1)))
    print('(e) E340 index', idx, which, '| exact ties (state, rank, edge):', [(i, r + 1, str(e)) for i, r, e in ties], '| a move of 10^-30 changes the path after state', u, '| tie at that state:', any(i == u for i, r, e in ties))
