"""v2: as v1 with every LP row tightened by 10^-9 times its norm, so the float optimum lies strictly inside the cell
(a member with an exact tie has zero slack, and a float optimum on the boundary then leaves the cell).
E943's members whose window no single-reading move lengthens tenfold: the window over the whole path cell (2026-11-25).
Members: short_window_vertex_v2 groups R2 (757), R3 (56), R0 (73).  The path cell (all arrangements with reading 1 = 1
whose cascade has the member's path: same setter ranks and laps, same readings in the way at every state, same
maximum-exit choices, landing clear) is cut out by inequalities LINEAR in the speeds r_2..r_7: at state
t_i = (l_i + 1/8)/r_{k_i}, reading q in the way with lap m is (m - 1/8) r_{k_i} < (l_i + 1/8) r_q < (m + 1/8) r_{k_i},
clear is (m + 1/8) r_{k_i} <= (l_i + 1/8) r_q <= (m + 7/8) r_{k_i}, and the maximum-exit choice is
(l_q + 1/8) r_{k_{i+1}} <= (l_{i+1} + 1/8) r_q.  A float LP (STEERS ONLY, rule 15) maximises the window's numerator
(8j' - 1) r_x - (8j + 1) r_y over the cell (r_7 boxed at 10 times its value).  Points member + lam (opt - member),
lam = 1 - 10^-3, 0.9, 0.5, 10^-1 ... 10^-8, are then built in exact Fractions and kept only if the EXACT cascade gives
the member's path; the window's length (8j' - 1)/(8 r_y) - (8j + 1)/(8 r_x) there is exact.
"""
import pickle, sys, glob
import numpy as np
from scipy.optimize import linprog
from fractions import Fraction as Fr
from math import floor, ceil
from collections import Counter
exec(open('short_window_v1.py').read().split("rec = pickle.load(open('/Users/trentpalelei")[0])
rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
mem = {}
for f in glob.glob('short_window_classes_v1_part*.pkl'):
    for m in pickle.load(open(f, 'rb')): mem[m[0]] = m
grp = {}
for f in glob.glob('short_window_vertex_v2_part*.pkl'):
    for m in pickle.load(open(f, 'rb')): grp[m[0]] = m[2]

def cell(rs):
    T, path = cascade(rs, E); t = E; st = [(E, 0, E)]  # (t, setter index, c) with t = c / r_setter
    for s in path:
        lap = floor(s * t + E); k = rs.index(s); t = (lap + E) / s; st.append((t, k, lap + E))
    A = []; b = []
    def row(coef, const=0.0):  # coef: dict index -> value; sum coef * r <= const ; r_0 = 1 moved to the right
        v = np.zeros(6); rhs = const
        for q, a in coef.items():
            if q == 0: rhs -= float(a)
            else: v[q - 1] += float(a)
        A.append(v); b.append(rhs)
    for i, (t, k, cc) in enumerate(st):
        blk = []
        for q in range(7):
            if q == k and (i > 0 or q == 0): continue
            x = rs[q] * t
            if blocked(rs[q], t):
                m = round(x); blk.append((q, ceil(x - E)))
                row({k: m - E, q: -cc}); row({q: cc, k: -(m + E)})
            else:
                m = floor(x - E)
                row({k: m + E, q: -cc}); row({q: cc, k: -(m + 1 - E)})
        if i + 1 < len(st):
            _, kn, cn = st[i + 1]
            for q, lq in blk:
                if q != kn: row({kn: lq + E, q: -cn})
    for q in range(6): row({q: 1, q + 1: -1})
    return np.array(A), np.array(b)

step = int(sys.argv[1]); off = int(sys.argv[2])
c = Counter(); shown = set()
todo = sorted(i for i in grp if grp[i] in ('R2', 'R3', 'R0'))
for idx in todo[off::step]:
    (_, cls, xi, j, yi, jp, a, b, *_r) = mem[idx]; R = grp[idx]
    rs = sorted(Fr(x) for x in rec[idx][1]); T0, sig0 = path_sig(rs); L0 = b - a
    Lw = lambda rr: Fr(8 * jp - 1, 8) / rr[yi] - Fr(8 * j + 1, 8) / rr[xi]
    A, bb = cell(rs)
    obj = np.zeros(6)
    if xi > 0: obj[xi - 1] -= (8 * jp - 1)
    obj[yi - 1] += (8 * j + 1)
    bounds = [(1.0, 10 * float(rs[q])) for q in range(1, 7)]
    bb = bb - 1e-9 * np.linalg.norm(A, axis=1)
    res = linprog(obj, A_ub=A, b_ub=bb, bounds=bounds, method='highs')
    if res.status != 0: c[(R, 'LP status %d' % res.status)] += 1; continue
    opt = [Fr(1)] + [Fr(float(v)) for v in res.x]
    best = None
    for lam in [1 - Fr(1, 1000), Fr(9, 10), Fr(1, 2)] + [Fr(1, 10 ** e) for e in range(1, 9)]:
        p = [rs[q] + lam * (opt[q] - rs[q]) for q in range(7)]
        if sorted(p) != p or path_sig(p)[1] != sig0: continue
        best = (lam, Lw(p), p); break
    if best is None: c[(R, 'no exact point on the path found')] += 1; continue
    lam, Ln, p = best
    g = 'L0 = 0: positive length' if (L0 == 0 and Ln > 0) else ('L0 = 0: none' if L0 == 0 else ('grows > 10' if Ln > 10 * L0 else 'grows <= 10'))
    c[(R, 'over the cell', g)] += 1
    if L0 and Ln > 10 * L0: c[(R, 'over the cell', 'length >= 10^-9' if Ln >= Fr(1, 10 ** 9) else 'length < 10^-9')] += 1
    hit = [q + 1 for q in range(1, 7) if abs(float(res.x[q - 1]) - bounds[q - 1][1]) < 1e-9]
    if hit: c[(R, 'LP optimum at the box on ranks', tuple(hit))] += 1
    if (R, g) not in shown:
        shown.add((R, g))
        print('first of', R, g, '| E340 index', idx, '| L0 ~ %.3e' % float(L0), '| exact point at lam', lam, '| length there', Ln, '~ %.3e' % float(Ln))
        print('    readings there (floats, steer only)', [round(float(q), 9) for q in p])
for k, val in sorted(c.items(), key=str): print(val, '|', k)
