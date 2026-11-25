"""E949, rule 8: the certificates of attain_lp_cert_v1 tested through the cascade at other points of each path cell
(2026-11-25).  Exact Fractions for every verdict; the float LP only proposes points (steers only).
For each of the 2,607 certified crossers: 3 float LP vertices of the tightened cell (objectives +r_7, -r_7, +r_2 - r_6);
points p = member + lam (vertex - member), lam = 1/2, 1/10, 1/100, kept only if the EXACT cascade gives the member's
path (short_window_v1.path_sig).  At each kept point, exactly: is min_k B_k = 8 end (bmove, as crosser_equality_v1)?
Also the 8 crossers whose opener is reading 1: is R* = 9 exactly?"""
import pickle, glob, sys
import numpy as np
from scipy.optimize import linprog
from fractions import Fraction as Fr
from math import floor, ceil
from collections import Counter
src = open('attain_lp_v2.py').read(); exec(src.split("step, off = int(sys.argv[1]), int(sys.argv[2]); c = Counter()\n")[0])
def path_sig(rs):
    T, path = cascade(rs, E); t = E; sig = []
    for s in path:
        lap = floor(s * t + E); t = (lap + E) / s; sig.append((rs.index(s), lap))
    return T, tuple(sig)
step, off = int(sys.argv[1]), int(sys.argv[2]); c = Counter()
for idx, R0, closers, cls, att in rows[off::step]:
    rs = sorted(Fr(x) for x in rec[idx][1]); T, path = cascade(rs, E)
    if rs.index(path[-1]) == 0: c[('opener is reading 1', 'R* = 9 exactly', 8 * T == 9)] += 1
    if not att or any(cls[k] != 'X' for k in att): continue
    skip = False
    for k1 in att:
        f = facing(rs, T, k1 - 1)
        if f is None or f[0] == 0: skip = True
    if skip: continue
    A, bb = cell(rs); bb = bb - 1e-9 * np.linalg.norm(A, axis=1)
    bounds = [(1.0, 10 * float(rs[q])) for q in range(1, 7)]
    _, sig0 = path_sig(rs); kept = 0
    for obj in ([0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, -1], [1, 0, 0, 0, -1, 0]):
        res = linprog(np.array(obj, float), A_ub=A, b_ub=bb, bounds=bounds, method='highs')
        if res.status != 0: continue
        v = [Fr(1)] + [Fr(float(x)) for x in res.x]
        for lam in (Fr(1, 2), Fr(1, 10), Fr(1, 100)):
            p = [rs[q] + lam * (v[q] - rs[q]) for q in range(7)]
            if p == rs or sorted(p) != p or path_sig(p)[1] != sig0: continue
            r = minB_vs_end(p); kept += 1
            c[('cell point (same path)', 'min B_k = 8 end', None if r is None else (not r[0]))] += 1
            if r is not None and r[0]: print('ESCAPE AT CELL POINT', idx, lam, [str(x) for x in p], flush=True)
            break
    c[('crosser', 'cell points kept', kept)] += 1
for kk, v in sorted(c.items(), key=str): print(v, '|', kk)
