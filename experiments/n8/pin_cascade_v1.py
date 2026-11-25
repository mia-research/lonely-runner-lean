"""E951, rule 8: the blocking mechanism (pins and ratio cycles, cert_cycle_v2 / pin_ident_v1 / cycle_rigid_v1) tested through
the cascade at other points of each path cell.  Exact Fractions for every verdict; the float LP only proposes points.
Points as attain_cell_cascade_v1 (3 LP vertices of the tightened cell, lam = 1/2, 1/10, 1/100, first kept per vertex; kept only
if the EXACT cascade gives the member's path).  At each kept point, for every attaining reading k of the member: is k still
class X (facing ends exist, gap > 0), and are its facing ends the SAME multiples of the same readings (x_P = q_P r_jP,
x_A = q_A r_jA with the member's q, j)?  For rigid pins: is the gap exactly (q_A - q_P) r_j at the point?"""
import sys
from fractions import Fraction as Fr
from collections import Counter
src = open('attain_cell_cascade_v1.py').read(); exec(src.split("step, off = int(sys.argv[1]), int(sys.argv[2]); c = Counter()\n")[0])
import numpy as np
from scipy.optimize import linprog
def idents(x, rs):
    return [(j + 1, x / rs[j]) for j in range(7) if (x / rs[j]).numerator < 2000 and (x / rs[j]).denominator < 2000]
step, off = int(sys.argv[1]), int(sys.argv[2]); c = Counter()
for idx, R0, closers, cls, att in rows[off::step]:
    if not att or any(cls[k] != 'X' for k in att): continue
    rs = sorted(Fr(x) for x in rec[idx][1]); T, path = cascade(rs, E)
    info = {}; skip = False
    for k1 in att:
        f = facing(rs, T, k1 - 1)
        if f is None or f[0] == 0 or ident(f[1], rs)[0] is None or ident(f[2], rs)[0] is None: skip = True; break
        IP, IA = idents(f[1], rs), idents(f[2], rs)
        info[k1] = (IP, IA, f[3], len(IP) == 1 and len(IA) == 1 and IP[0][0] == IA[0][0])
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
            kept += 1; Tp, _ = cascade(p, E)
            for k1, (IP, IA, side, rp) in info.items():
                f = facing(p, Tp, k1 - 1)
                if f is None: c[('attaining reading at point', 'pin' if rp else 'other', 'facing None')] += 1; continue
                d, xP, xA, sd = f
                if d == 0: c[('attaining reading at point', 'pin' if rp else 'other', 'gap 0 (touch or meet)')] += 1; continue
                sameP = any(xP == q * p[j - 1] for j, q in IP); sameA = any(xA == q * p[j - 1] for j, q in IA)
                key = ('attaining reading at point', 'pin' if rp else 'other', 'class X', 'side same', sd == side, 'P same multiple', sameP, 'A same multiple', sameA)
                c[key] += 1
                if rp and sameP and sameA:
                    j = IP[0][0]; c[('rigid pin at point', 'gap = |q_A - q_P| r_j exactly', d == abs(IA[0][1] - IP[0][1]) * p[j - 1])] += 1
                if rp and not (sameP and sameA): print('PIN CHANGED', idx, k1, lam, flush=True)
            break
    c[('crosser', 'cell points kept', kept)] += 1
for kk, v in sorted(c.items(), key=str): print(v, '|', kk)
